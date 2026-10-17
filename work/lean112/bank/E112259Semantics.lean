import E112259Data
namespace Snake9.Regrowth.E112259
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 116 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (3 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (4 : Vertex)) else decide (InPath q (7 : Vertex))) else (if i < 6 then decide (InPath q (8 : Vertex)) else decide (InPath q (9 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (10 : Vertex)) else (if i < 9 then decide (InPath q (13 : Vertex)) else decide (InPath q (14 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex))) else (if i < 13 then decide (InPath q (21 : Vertex)) else decide (InPath q (22 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (24 : Vertex)) else (if i < 16 then decide (InPath q (27 : Vertex)) else decide (InPath q (28 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (30 : Vertex)) else decide (InPath q (31 : Vertex))) else (if i < 20 then decide (InPath q (33 : Vertex)) else decide (InPath q (35 : Vertex))))) else (if i < 25 then (if i < 23 then (if i < 22 then decide (InPath q (36 : Vertex)) else decide (InPath q (38 : Vertex))) else (if i < 24 then decide (InPath q (40 : Vertex)) else decide (InPath q (42 : Vertex)))) else (if i < 27 then (if i < 26 then decide (InPath q (45 : Vertex)) else decide (InPath q (47 : Vertex))) else (if i < 28 then decide (InPath q (48 : Vertex)) else decide (InPath q (49 : Vertex))))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then decide (InPath q (50 : Vertex)) else (if i < 31 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex)))) else (if i < 34 then (if i < 33 then decide (InPath q (57 : Vertex)) else decide (InPath q (59 : Vertex))) else (if i < 35 then decide (InPath q (60 : Vertex)) else decide (InPath q (62 : Vertex))))) else (if i < 39 then (if i < 37 then decide (InPath q (75 : Vertex)) else (if i < 38 then decide (InPath q (79 : Vertex)) else decide (InPath q (80 : Vertex)))) else (if i < 41 then (if i < 40 then decide (InPath q (83 : Vertex)) else decide (InPath q (84 : Vertex))) else (if i < 42 then decide (InPath q (87 : Vertex)) else decide (InPath q (89 : Vertex)))))) else (if i < 50 then (if i < 46 then (if i < 44 then decide (InPath q (93 : Vertex)) else (if i < 45 then decide (InPath q (105 : Vertex)) else decide (InPath q (107 : Vertex)))) else (if i < 48 then (if i < 47 then decide (InPath q (108 : Vertex)) else decide (InPath q (110 : Vertex))) else (if i < 49 then decide (InPath q (113 : Vertex)) else decide (InPath q (115 : Vertex))))) else (if i < 54 then (if i < 52 then (if i < 51 then decide (InPath q (116 : Vertex)) else decide (InPath q (118 : Vertex))) else (if i < 53 then decide (InPath q (125 : Vertex)) else decide (InPath q (127 : Vertex)))) else (if i < 56 then (if i < 55 then decide (InPath q (128 : Vertex)) else decide (InPath q (129 : Vertex))) else (if i < 57 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex)))))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then decide (InPath q (133 : Vertex)) else (if i < 60 then decide (InPath q (134 : Vertex)) else decide (InPath q (136 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (137 : Vertex)) else decide (InPath q (139 : Vertex))) else (if i < 64 then decide (InPath q (141 : Vertex)) else decide (InPath q (142 : Vertex))))) else (if i < 68 then (if i < 66 then decide (InPath q (146 : Vertex)) else (if i < 67 then decide (InPath q (147 : Vertex)) else decide (InPath q (148 : Vertex)))) else (if i < 70 then (if i < 69 then decide (InPath q (149 : Vertex)) else decide (InPath q (150 : Vertex))) else (if i < 71 then decide (InPath q (152 : Vertex)) else decide (InPath q (155 : Vertex)))))) else (if i < 79 then (if i < 75 then (if i < 73 then decide (InPath q (157 : Vertex)) else (if i < 74 then decide (InPath q (158 : Vertex)) else decide (InPath q (159 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (160 : Vertex)) else decide (InPath q (161 : Vertex))) else (if i < 78 then decide (InPath q (162 : Vertex)) else decide (InPath q (163 : Vertex))))) else (if i < 83 then (if i < 81 then (if i < 80 then decide (InPath q (164 : Vertex)) else decide (InPath q (167 : Vertex))) else (if i < 82 then decide (InPath q (168 : Vertex)) else decide (InPath q (170 : Vertex)))) else (if i < 85 then (if i < 84 then decide (InPath q (171 : Vertex)) else decide (InPath q (172 : Vertex))) else (if i < 86 then decide (InPath q (175 : Vertex)) else decide (InPath q (176 : Vertex))))))) else (if i < 101 then (if i < 94 then (if i < 90 then (if i < 88 then decide (InPath q (177 : Vertex)) else (if i < 89 then decide (InPath q (178 : Vertex)) else decide (InPath q (180 : Vertex)))) else (if i < 92 then (if i < 91 then decide (InPath q (181 : Vertex)) else decide (InPath q (183 : Vertex))) else (if i < 93 then decide (InPath q (185 : Vertex)) else decide (InPath q (186 : Vertex))))) else (if i < 97 then (if i < 95 then decide (InPath q (189 : Vertex)) else (if i < 96 then decide (InPath q (190 : Vertex)) else decide (InPath q (199 : Vertex)))) else (if i < 99 then (if i < 98 then decide (InPath q (207 : Vertex)) else decide (InPath q (208 : Vertex))) else (if i < 100 then decide (InPath q (209 : Vertex)) else decide (InPath q (214 : Vertex)))))) else (if i < 108 then (if i < 104 then (if i < 102 then decide (InPath q (215 : Vertex)) else (if i < 103 then decide (InPath q (217 : Vertex)) else decide (InPath q (224 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (225 : Vertex)) else decide (InPath q (227 : Vertex))) else (if i < 107 then decide (InPath q (230 : Vertex)) else decide (InPath q (233 : Vertex))))) else (if i < 112 then (if i < 110 then (if i < 109 then decide (InPath q (235 : Vertex)) else decide (InPath q (237 : Vertex))) else (if i < 111 then decide (InPath q (238 : Vertex)) else decide (InPath q (242 : Vertex)))) else (if i < 114 then (if i < 113 then decide (InPath q (243 : Vertex)) else decide (InPath q (245 : Vertex))) else (if i < 115 then decide (InPath q (246 : Vertex)) else decide (InPath q (251 : Vertex))))))))) else (if i < 174 then (if i < 145 then (if i < 130 then (if i < 123 then (if i < 119 then (if i < 117 then decide (InPath q (255 : Vertex)) else (if i < 118 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (3 : Vertex)))) else (if i < 121 then (if i < 120 then decide (BallClauseLogic.Endpoint q (4 : Vertex)) else decide (BallClauseLogic.Endpoint q (7 : Vertex))) else (if i < 122 then decide (BallClauseLogic.Endpoint q (8 : Vertex)) else decide (BallClauseLogic.Endpoint q (9 : Vertex))))) else (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (13 : Vertex)) else decide (BallClauseLogic.Endpoint q (14 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (21 : Vertex)) else decide (BallClauseLogic.Endpoint q (22 : Vertex)))))) else (if i < 137 then (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (24 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (27 : Vertex)) else decide (BallClauseLogic.Endpoint q (28 : Vertex)))) else (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else decide (BallClauseLogic.Endpoint q (31 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (33 : Vertex)) else decide (BallClauseLogic.Endpoint q (35 : Vertex))))) else (if i < 141 then (if i < 139 then (if i < 138 then decide (BallClauseLogic.Endpoint q (36 : Vertex)) else decide (BallClauseLogic.Endpoint q (38 : Vertex))) else (if i < 140 then decide (BallClauseLogic.Endpoint q (40 : Vertex)) else decide (BallClauseLogic.Endpoint q (42 : Vertex)))) else (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (45 : Vertex)) else decide (BallClauseLogic.Endpoint q (47 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (48 : Vertex)) else decide (BallClauseLogic.Endpoint q (49 : Vertex))))))) else (if i < 159 then (if i < 152 then (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (50 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (53 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (57 : Vertex)) else decide (BallClauseLogic.Endpoint q (59 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (60 : Vertex)) else decide (BallClauseLogic.Endpoint q (62 : Vertex))))) else (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (75 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (79 : Vertex)) else decide (BallClauseLogic.Endpoint q (80 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (83 : Vertex)) else decide (BallClauseLogic.Endpoint q (84 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (87 : Vertex)) else decide (BallClauseLogic.Endpoint q (89 : Vertex)))))) else (if i < 166 then (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (93 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (105 : Vertex)) else decide (BallClauseLogic.Endpoint q (107 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (108 : Vertex)) else decide (BallClauseLogic.Endpoint q (110 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (113 : Vertex)) else decide (BallClauseLogic.Endpoint q (115 : Vertex))))) else (if i < 170 then (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (116 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (125 : Vertex)) else decide (BallClauseLogic.Endpoint q (127 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (128 : Vertex)) else decide (BallClauseLogic.Endpoint q (129 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex)))))))) else (if i < 203 then (if i < 188 then (if i < 181 then (if i < 177 then (if i < 175 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else (if i < 176 then decide (BallClauseLogic.Endpoint q (134 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex)))) else (if i < 179 then (if i < 178 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex))) else (if i < 180 then decide (BallClauseLogic.Endpoint q (141 : Vertex)) else decide (BallClauseLogic.Endpoint q (142 : Vertex))))) else (if i < 184 then (if i < 182 then decide (BallClauseLogic.Endpoint q (146 : Vertex)) else (if i < 183 then decide (BallClauseLogic.Endpoint q (147 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex)))) else (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else decide (BallClauseLogic.Endpoint q (150 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (152 : Vertex)) else decide (BallClauseLogic.Endpoint q (155 : Vertex)))))) else (if i < 195 then (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (157 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (158 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (162 : Vertex)) else decide (BallClauseLogic.Endpoint q (163 : Vertex))))) else (if i < 199 then (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (164 : Vertex)) else decide (BallClauseLogic.Endpoint q (167 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else decide (BallClauseLogic.Endpoint q (170 : Vertex)))) else (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else decide (BallClauseLogic.Endpoint q (172 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else decide (BallClauseLogic.Endpoint q (176 : Vertex))))))) else (if i < 218 then (if i < 210 then (if i < 206 then (if i < 204 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else (if i < 205 then decide (BallClauseLogic.Endpoint q (178 : Vertex)) else decide (BallClauseLogic.Endpoint q (180 : Vertex)))) else (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else decide (BallClauseLogic.Endpoint q (183 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (185 : Vertex)) else decide (BallClauseLogic.Endpoint q (186 : Vertex))))) else (if i < 214 then (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (190 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (207 : Vertex)))) else (if i < 216 then (if i < 215 then decide (BallClauseLogic.Endpoint q (208 : Vertex)) else decide (BallClauseLogic.Endpoint q (209 : Vertex))) else (if i < 217 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (215 : Vertex)))))) else (if i < 225 then (if i < 221 then (if i < 219 then decide (BallClauseLogic.Endpoint q (217 : Vertex)) else (if i < 220 then decide (BallClauseLogic.Endpoint q (224 : Vertex)) else decide (BallClauseLogic.Endpoint q (225 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (227 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (233 : Vertex)) else decide (BallClauseLogic.Endpoint q (235 : Vertex))))) else (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (237 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (242 : Vertex)) else decide (BallClauseLogic.Endpoint q (243 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (246 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count233 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [117, 118, 119]
def count237 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count239 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count241 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123]
def count245 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [124, 125, 126]
def count249 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130]
def count259 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [131, 132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]
def count285 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [145, 146, 147]
def count291 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 163, 164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count333 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count337 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count343 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count345 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [175, 176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181]
def count357 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count365 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185, 186, 187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188]
def count371 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192, 193, 194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count387 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count393 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203]
def count395 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201, 202, 203]
def count397 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203]
def count401 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [204, 205, 206]
def count405 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count409 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210]
def count411 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207, 208, 209, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [211, 212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count419 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count421 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217]
def count423 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214, 215, 216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
def count427 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [218, 219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count435 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count441 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count443 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count447 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count449 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count451 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]
def count457 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]
def count459 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]
def count461 (b : Nat → Bool) : Nat := countLit b [2, 6]
def count463 (b : Nat → Bool) : Nat := countLit b [1, 2, 6]
def count466 (b : Nat → Bool) : Nat := countLit b [7, 10]
def count468 (b : Nat → Bool) : Nat := countLit b [11, 14]
def count470 (b : Nat → Bool) : Nat := countLit b [7, 10, 11, 14]
def count474 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11, 14]
def count481 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count483 (b : Nat → Bool) : Nat := countLit b [15, 17, 19]
def count486 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count488 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count490 (b : Nat → Bool) : Nat := countLit b [21, 23, 25, 27]
def count494 (b : Nat → Bool) : Nat := countLit b [15, 17, 19, 21, 23, 25, 27]
def count501 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11, 14, 15, 17, 19, 21, 23, 25, 27]
def count515 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count517 (b : Nat → Bool) : Nat := countLit b [30, 32, 34]
def count520 (b : Nat → Bool) : Nat := countLit b [36, 38]
def count522 (b : Nat → Bool) : Nat := countLit b [39, 42]
def count524 (b : Nat → Bool) : Nat := countLit b [36, 38, 39, 42]
def count528 (b : Nat → Bool) : Nat := countLit b [30, 32, 34, 36, 38, 39, 42]
def count535 (b : Nat → Bool) : Nat := countLit b [44, 46]
def count537 (b : Nat → Bool) : Nat := countLit b [48, 50]
def count539 (b : Nat → Bool) : Nat := countLit b [44, 46, 48, 50]
def count543 (b : Nat → Bool) : Nat := countLit b [52, 55]
def count545 (b : Nat → Bool) : Nat := countLit b [57, 60]
def count547 (b : Nat → Bool) : Nat := countLit b [52, 55, 57, 60]
def count551 (b : Nat → Bool) : Nat := countLit b [44, 46, 48, 50, 52, 55, 57, 60]
def count559 (b : Nat → Bool) : Nat := countLit b [30, 32, 34, 36, 38, 39, 42, 44, 46, 48, 50, 52, 55, 57, 60]
def count574 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11, 14, 15, 17, 19, 21, 23, 25, 27, 30, 32, 34, 36, 38, 39, 42, 44, 46, 48, 50, 52, 55, 57, 60]
def count603 (b : Nat → Bool) : Nat := countLit b [63, 64]
def count605 (b : Nat → Bool) : Nat := countLit b [62, 63, 64]
def count608 (b : Nat → Bool) : Nat := countLit b [66, 68]
def count610 (b : Nat → Bool) : Nat := countLit b [69, 74]
def count612 (b : Nat → Bool) : Nat := countLit b [66, 68, 69, 74]
def count616 (b : Nat → Bool) : Nat := countLit b [62, 63, 64, 66, 68, 69, 74]
def count623 (b : Nat → Bool) : Nat := countLit b [78, 82]
def count625 (b : Nat → Bool) : Nat := countLit b [75, 78, 82]
def count628 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count630 (b : Nat → Bool) : Nat := countLit b [87, 88]
def count632 (b : Nat → Bool) : Nat := countLit b [84, 85, 87, 88]
def count636 (b : Nat → Bool) : Nat := countLit b [75, 78, 82, 84, 85, 87, 88]
def count643 (b : Nat → Bool) : Nat := countLit b [62, 63, 64, 66, 68, 69, 74, 75, 78, 82, 84, 85, 87, 88]
def count657 (b : Nat → Bool) : Nat := countLit b [91, 94]
def count659 (b : Nat → Bool) : Nat := countLit b [89, 91, 94]
def count662 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count664 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count666 (b : Nat → Bool) : Nat := countLit b [95, 97, 99, 101]
def count670 (b : Nat → Bool) : Nat := countLit b [89, 91, 94, 95, 97, 99, 101]
def count677 (b : Nat → Bool) : Nat := countLit b [104, 108]
def count679 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count681 (b : Nat → Bool) : Nat := countLit b [104, 108, 109, 110]
def count685 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count687 (b : Nat → Bool) : Nat := countLit b [114, 116]
def count689 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 116]
def count693 (b : Nat → Bool) : Nat := countLit b [104, 108, 109, 110, 112, 113, 114, 116]
def count701 (b : Nat → Bool) : Nat := countLit b [89, 91, 94, 95, 97, 99, 101, 104, 108, 109, 110, 112, 113, 114, 116]
def count716 (b : Nat → Bool) : Nat := countLit b [62, 63, 64, 66, 68, 69, 74, 75, 78, 82, 84, 85, 87, 88, 89, 91, 94, 95, 97, 99, 101, 104, 108, 109, 110, 112, 113, 114, 116]
def count745 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11, 14, 15, 17, 19, 21, 23, 25, 27, 30, 32, 34, 36, 38, 39, 42, 44, 46, 48, 50, 52, 55, 57, 60, 62, 63, 64, 66, 68, 69, 74, 75, 78, 82, 84, 85, 87, 88, 89, 91, 94, 95, 97, 99, 101, 104, 108, 109, 110, 112, 113, 114, 116]
def count787 (b : Nat → Bool) : Nat := countLit b [-2, -6]
def count789 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6]
def count792 (b : Nat → Bool) : Nat := countLit b [-7, -10]
def count794 (b : Nat → Bool) : Nat := countLit b [-11, -14]
def count796 (b : Nat → Bool) : Nat := countLit b [-7, -10, -11, -14]
def count800 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11, -14]
def count807 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count809 (b : Nat → Bool) : Nat := countLit b [-15, -17, -19]
def count812 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count814 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count816 (b : Nat → Bool) : Nat := countLit b [-21, -23, -25, -27]
def count820 (b : Nat → Bool) : Nat := countLit b [-15, -17, -19, -21, -23, -25, -27]
def count827 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27]
def count841 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count843 (b : Nat → Bool) : Nat := countLit b [-30, -32, -34]
def count846 (b : Nat → Bool) : Nat := countLit b [-36, -38]
def count848 (b : Nat → Bool) : Nat := countLit b [-39, -42]
def count850 (b : Nat → Bool) : Nat := countLit b [-36, -38, -39, -42]
def count854 (b : Nat → Bool) : Nat := countLit b [-30, -32, -34, -36, -38, -39, -42]
def count861 (b : Nat → Bool) : Nat := countLit b [-44, -46]
def count863 (b : Nat → Bool) : Nat := countLit b [-48, -50]
def count865 (b : Nat → Bool) : Nat := countLit b [-44, -46, -48, -50]
def count869 (b : Nat → Bool) : Nat := countLit b [-52, -55]
def count871 (b : Nat → Bool) : Nat := countLit b [-57, -60]
def count873 (b : Nat → Bool) : Nat := countLit b [-52, -55, -57, -60]
def count877 (b : Nat → Bool) : Nat := countLit b [-44, -46, -48, -50, -52, -55, -57, -60]
def count885 (b : Nat → Bool) : Nat := countLit b [-30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]
def count900 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60]
def count918 (b : Nat → Bool) : Nat := countLit b [-63, -64]
def count920 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64]
def count923 (b : Nat → Bool) : Nat := countLit b [-66, -68]
def count925 (b : Nat → Bool) : Nat := countLit b [-69, -74]
def count927 (b : Nat → Bool) : Nat := countLit b [-66, -68, -69, -74]
def count931 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64, -66, -68, -69, -74]
def count938 (b : Nat → Bool) : Nat := countLit b [-78, -82]
def count940 (b : Nat → Bool) : Nat := countLit b [-75, -78, -82]
def count943 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count945 (b : Nat → Bool) : Nat := countLit b [-87, -88]
def count947 (b : Nat → Bool) : Nat := countLit b [-84, -85, -87, -88]
def count951 (b : Nat → Bool) : Nat := countLit b [-75, -78, -82, -84, -85, -87, -88]
def count958 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88]
def count972 (b : Nat → Bool) : Nat := countLit b [-91, -94]
def count974 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94]
def count977 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count979 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count981 (b : Nat → Bool) : Nat := countLit b [-95, -97, -99, -101]
def count985 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94, -95, -97, -99, -101]
def count992 (b : Nat → Bool) : Nat := countLit b [-104, -108]
def count994 (b : Nat → Bool) : Nat := countLit b [-109, -110]
def count996 (b : Nat → Bool) : Nat := countLit b [-104, -108, -109, -110]
def count1000 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1002 (b : Nat → Bool) : Nat := countLit b [-114, -116]
def count1004 (b : Nat → Bool) : Nat := countLit b [-112, -113, -114, -116]
def count1008 (b : Nat → Bool) : Nat := countLit b [-104, -108, -109, -110, -112, -113, -114, -116]
def count1016 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]
def count1031 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]
def count1049 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11, -14, -15, -17, -19, -21, -23, -25, -27, -30, -32, -34, -36, -38, -39, -42, -44, -46, -48, -50, -52, -55, -57, -60, -62, -63, -64, -66, -68, -69, -74, -75, -78, -82, -84, -85, -87, -88, -89, -91, -94, -95, -97, -99, -101, -104, -108, -109, -110, -112, -113, -114, -116]
def count1067 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count1069 (b : Nat → Bool) : Nat := countLit b [3, 4, 5]
def count1072 (b : Nat → Bool) : Nat := countLit b [8, 9]
def count1074 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count1076 (b : Nat → Bool) : Nat := countLit b [8, 9, 12, 13]
def count1080 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 12, 13]
def count1087 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count1089 (b : Nat → Bool) : Nat := countLit b [16, 18, 20]
def count1092 (b : Nat → Bool) : Nat := countLit b [22, 24]
def count1094 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count1096 (b : Nat → Bool) : Nat := countLit b [22, 24, 26, 28]
def count1100 (b : Nat → Bool) : Nat := countLit b [16, 18, 20, 22, 24, 26, 28]
def count1107 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 12, 13, 16, 18, 20, 22, 24, 26, 28]
def count1121 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count1123 (b : Nat → Bool) : Nat := countLit b [29, 31, 33]
def count1126 (b : Nat → Bool) : Nat := countLit b [35, 37]
def count1128 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count1130 (b : Nat → Bool) : Nat := countLit b [35, 37, 40, 41]
def count1134 (b : Nat → Bool) : Nat := countLit b [29, 31, 33, 35, 37, 40, 41]
def count1141 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count1143 (b : Nat → Bool) : Nat := countLit b [47, 49]
def count1145 (b : Nat → Bool) : Nat := countLit b [43, 45, 47, 49]
def count1149 (b : Nat → Bool) : Nat := countLit b [51, 53]
def count1151 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count1153 (b : Nat → Bool) : Nat := countLit b [51, 53, 54, 56]
def count1157 (b : Nat → Bool) : Nat := countLit b [43, 45, 47, 49, 51, 53, 54, 56]
def count1165 (b : Nat → Bool) : Nat := countLit b [29, 31, 33, 35, 37, 40, 41, 43, 45, 47, 49, 51, 53, 54, 56]
def count1180 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 12, 13, 16, 18, 20, 22, 24, 26, 28, 29, 31, 33, 35, 37, 40, 41, 43, 45, 47, 49, 51, 53, 54, 56]
def count1209 (b : Nat → Bool) : Nat := countLit b [59, 61]
def count1211 (b : Nat → Bool) : Nat := countLit b [58, 59, 61]
def count1214 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count1216 (b : Nat → Bool) : Nat := countLit b [70, 71]
def count1218 (b : Nat → Bool) : Nat := countLit b [65, 67, 70, 71]
def count1222 (b : Nat → Bool) : Nat := countLit b [58, 59, 61, 65, 67, 70, 71]
def count1229 (b : Nat → Bool) : Nat := countLit b [73, 76]
def count1231 (b : Nat → Bool) : Nat := countLit b [72, 73, 76]
def count1234 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count1236 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count1238 (b : Nat → Bool) : Nat := countLit b [77, 79, 80, 81]
def count1242 (b : Nat → Bool) : Nat := countLit b [72, 73, 76, 77, 79, 80, 81]
def count1249 (b : Nat → Bool) : Nat := countLit b [58, 59, 61, 65, 67, 70, 71, 72, 73, 76, 77, 79, 80, 81]
def count1263 (b : Nat → Bool) : Nat := countLit b [86, 90]
def count1265 (b : Nat → Bool) : Nat := countLit b [83, 86, 90]
def count1268 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count1270 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count1272 (b : Nat → Bool) : Nat := countLit b [92, 93, 96, 98]
def count1276 (b : Nat → Bool) : Nat := countLit b [83, 86, 90, 92, 93, 96, 98]
def count1283 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count1285 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count1287 (b : Nat → Bool) : Nat := countLit b [100, 102, 103, 105]
def count1291 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count1293 (b : Nat → Bool) : Nat := countLit b [111, 115]
def count1295 (b : Nat → Bool) : Nat := countLit b [106, 107, 111, 115]
def count1299 (b : Nat → Bool) : Nat := countLit b [100, 102, 103, 105, 106, 107, 111, 115]
def count1307 (b : Nat → Bool) : Nat := countLit b [83, 86, 90, 92, 93, 96, 98, 100, 102, 103, 105, 106, 107, 111, 115]
def count1322 (b : Nat → Bool) : Nat := countLit b [58, 59, 61, 65, 67, 70, 71, 72, 73, 76, 77, 79, 80, 81, 83, 86, 90, 92, 93, 96, 98, 100, 102, 103, 105, 106, 107, 111, 115]
def count1351 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 12, 13, 16, 18, 20, 22, 24, 26, 28, 29, 31, 33, 35, 37, 40, 41, 43, 45, 47, 49, 51, 53, 54, 56, 58, 59, 61, 65, 67, 70, 71, 72, 73, 76, 77, 79, 80, 81, 83, 86, 90, 92, 93, 96, 98, 100, 102, 103, 105, 106, 107, 111, 115]
def count1393 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1395 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5]
def count1398 (b : Nat → Bool) : Nat := countLit b [-8, -9]
def count1400 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count1402 (b : Nat → Bool) : Nat := countLit b [-8, -9, -12, -13]
def count1406 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -12, -13]
def count1413 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count1415 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20]
def count1418 (b : Nat → Bool) : Nat := countLit b [-22, -24]
def count1420 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count1422 (b : Nat → Bool) : Nat := countLit b [-22, -24, -26, -28]
def count1426 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20, -22, -24, -26, -28]
def count1433 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28]
def count1447 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count1449 (b : Nat → Bool) : Nat := countLit b [-29, -31, -33]
def count1452 (b : Nat → Bool) : Nat := countLit b [-35, -37]
def count1454 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count1456 (b : Nat → Bool) : Nat := countLit b [-35, -37, -40, -41]
def count1460 (b : Nat → Bool) : Nat := countLit b [-29, -31, -33, -35, -37, -40, -41]
def count1467 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count1469 (b : Nat → Bool) : Nat := countLit b [-47, -49]
def count1471 (b : Nat → Bool) : Nat := countLit b [-43, -45, -47, -49]
def count1475 (b : Nat → Bool) : Nat := countLit b [-51, -53]
def count1477 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count1479 (b : Nat → Bool) : Nat := countLit b [-51, -53, -54, -56]
def count1483 (b : Nat → Bool) : Nat := countLit b [-43, -45, -47, -49, -51, -53, -54, -56]
def count1491 (b : Nat → Bool) : Nat := countLit b [-29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]
def count1506 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]
def count1524 (b : Nat → Bool) : Nat := countLit b [-59, -61]
def count1526 (b : Nat → Bool) : Nat := countLit b [-58, -59, -61]
def count1529 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count1531 (b : Nat → Bool) : Nat := countLit b [-70, -71]
def count1533 (b : Nat → Bool) : Nat := countLit b [-65, -67, -70, -71]
def count1537 (b : Nat → Bool) : Nat := countLit b [-58, -59, -61, -65, -67, -70, -71]
def count1544 (b : Nat → Bool) : Nat := countLit b [-73, -76]
def count1546 (b : Nat → Bool) : Nat := countLit b [-72, -73, -76]
def count1549 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count1551 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1553 (b : Nat → Bool) : Nat := countLit b [-77, -79, -80, -81]
def count1557 (b : Nat → Bool) : Nat := countLit b [-72, -73, -76, -77, -79, -80, -81]
def count1564 (b : Nat → Bool) : Nat := countLit b [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]
def count1578 (b : Nat → Bool) : Nat := countLit b [-86, -90]
def count1580 (b : Nat → Bool) : Nat := countLit b [-83, -86, -90]
def count1583 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1585 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count1587 (b : Nat → Bool) : Nat := countLit b [-92, -93, -96, -98]
def count1591 (b : Nat → Bool) : Nat := countLit b [-83, -86, -90, -92, -93, -96, -98]
def count1598 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count1600 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count1602 (b : Nat → Bool) : Nat := countLit b [-100, -102, -103, -105]
def count1606 (b : Nat → Bool) : Nat := countLit b [-106, -107]
def count1608 (b : Nat → Bool) : Nat := countLit b [-111, -115]
def count1610 (b : Nat → Bool) : Nat := countLit b [-106, -107, -111, -115]
def count1614 (b : Nat → Bool) : Nat := countLit b [-100, -102, -103, -105, -106, -107, -111, -115]
def count1622 (b : Nat → Bool) : Nat := countLit b [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]
def count1637 (b : Nat → Bool) : Nat := countLit b [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]
def count1655 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56, -58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 836 then (if i < 418 then (if i < 209 then (if i < 104 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 19 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 17 then b 16 else (if i < 18 then b 17 else b 18))) else (if i < 22 then (if i < 20 then b 19 else (if i < 21 then b 20 else b 21)) else (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else b 25))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31))) else (if i < 35 then (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)) else (if i < 37 then (if i < 36 then b 35 else b 36) else (if i < 38 then b 37 else b 38)))) else (if i < 45 then (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44))) else (if i < 48 then (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)) else (if i < 50 then (if i < 49 then b 48 else b 49) else (if i < 51 then b 50 else b 51)))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then b 52 else (if i < 54 then b 53 else b 54)) else (if i < 56 then b 55 else (if i < 57 then b 56 else b 57))) else (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else b 64)))) else (if i < 71 then (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 69 then b 68 else (if i < 70 then b 69 else b 70))) else (if i < 74 then (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)) else (if i < 76 then (if i < 75 then b 74 else b 75) else (if i < 77 then b 76 else b 77))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90)))) else (if i < 97 then (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 95 then b 94 else (if i < 96 then b 95 else b 96))) else (if i < 100 then (if i < 98 then b 97 else (if i < 99 then b 98 else b 99)) else (if i < 102 then (if i < 101 then b 100 else b 101) else (if i < 103 then b 102 else b 103))))))) else (if i < 156 then (if i < 130 then (if i < 117 then (if i < 110 then (if i < 107 then (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)) else (if i < 108 then b 107 else (if i < 109 then b 108 else b 109))) else (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 115 then (if i < 114 then b 113 else b 114) else (if i < 116 then b 115 else b 116)))) else (if i < 123 then (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122))) else (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else b 129))))) else (if i < 143 then (if i < 136 then (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 134 then b 133 else (if i < 135 then b 134 else b 135))) else (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 141 then (if i < 140 then b 139 else b 140) else (if i < 142 then b 141 else b 142)))) else (if i < 149 then (if i < 146 then (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)) else (if i < 147 then b 146 else (if i < 148 then b 147 else b 148))) else (if i < 152 then (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)) else (if i < 154 then (if i < 153 then b 152 else b 153) else (if i < 155 then b 154 else b 155)))))) else (if i < 182 then (if i < 169 then (if i < 162 then (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 167 then (if i < 166 then b 165 else b 166) else (if i < 168 then b 167 else b 168)))) else (if i < 175 then (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174))) else (if i < 178 then (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)) else (if i < 180 then (if i < 179 then b 178 else b 179) else (if i < 181 then b 180 else b 181))))) else (if i < 195 then (if i < 188 then (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187))) else (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else b 194)))) else (if i < 202 then (if i < 198 then (if i < 196 then b 195 else (if i < 197 then b 196 else b 197)) else (if i < 200 then (if i < 199 then b 198 else b 199) else (if i < 201 then b 200 else b 201))) else (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 207 then (if i < 206 then b 205 else b 206) else (if i < 208 then b 207 else b 208)))))))) else (if i < 313 then (if i < 261 then (if i < 235 then (if i < 222 then (if i < 215 then (if i < 212 then (if i < 210 then b 209 else (if i < 211 then b 210 else b 211)) else (if i < 213 then b 212 else (if i < 214 then b 213 else b 214))) else (if i < 218 then (if i < 216 then b 215 else (if i < 217 then b 216 else b 217)) else (if i < 220 then (if i < 219 then b 218 else b 219) else (if i < 221 then b 220 else b 221)))) else (if i < 228 then (if i < 225 then (if i < 223 then b 222 else (if i < 224 then b 223 else b 224)) else (if i < 226 then b 225 else (if i < 227 then b 226 else b 227))) else (if i < 231 then (if i < 229 then b 228 else (if i < 230 then b 229 else b 230)) else (if i < 233 then (if i < 232 then b 231 else b 232) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))))) else (if i < 248 then (if i < 241 then (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))) else (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 246 then (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))))) else (if i < 254 then (if i < 251 then (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 252 then decide (1 ≤ count251 b) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)))) else (if i < 257 then (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b))) else (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))))))) else (if i < 287 then (if i < 274 then (if i < 267 then (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))) else (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 272 then (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))))) else (if i < 280 then (if i < 277 then (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))) else (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)))) else (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))))) else (if i < 300 then (if i < 293 then (if i < 290 then (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))) else (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))) else (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 298 then (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))))) else (if i < 306 then (if i < 303 then (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b))) else (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))) else (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))))))) else (if i < 365 then (if i < 339 then (if i < 326 then (if i < 319 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))) else (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 324 then (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))))) else (if i < 332 then (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 335 then (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))))) else (if i < 352 then (if i < 345 then (if i < 342 then (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))) else (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)))) else (if i < 348 then (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))) else (if i < 350 then (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b))))) else (if i < 358 then (if i < 355 then (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b))) else (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b)))) else (if i < 361 then (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))) else (if i < 363 then (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b))))))) else (if i < 391 then (if i < 378 then (if i < 371 then (if i < 368 then (if i < 366 then decide (1 ≤ count365 b) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))) else (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 376 then (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))))) else (if i < 384 then (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)))) else (if i < 387 then (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b))) else (if i < 389 then (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))))) else (if i < 404 then (if i < 397 then (if i < 394 then (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)))) else (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))))) else (if i < 411 then (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)))) else (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 416 then (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)))))))))) else (if i < 627 then (if i < 522 then (if i < 470 then (if i < 444 then (if i < 431 then (if i < 424 then (if i < 421 then (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))) else (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)))) else (if i < 427 then (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b))) else (if i < 429 then (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))))) else (if i < 437 then (if i < 434 then (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))) else (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))) else (if i < 440 then (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))) else (if i < 442 then (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)))))) else (if i < 457 then (if i < 450 then (if i < 447 then (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b))) else (if i < 448 then decide (1 ≤ count447 b) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b)))) else (if i < 453 then (if i < 451 then decide (2 ≤ count449 b) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))) else (if i < 455 then (if i < 454 then decide (1 ≤ count453 b) else decide (2 ≤ count453 b)) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))))) else (if i < 463 then (if i < 460 then (if i < 458 then decide (1 ≤ count457 b) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b))) else (if i < 461 then decide (2 ≤ count459 b) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)))) else (if i < 466 then (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (3 ≤ count463 b))) else (if i < 468 then (if i < 467 then decide (1 ≤ count466 b) else decide (2 ≤ count466 b)) else (if i < 469 then decide (1 ≤ count468 b) else decide (2 ≤ count468 b))))))) else (if i < 496 then (if i < 483 then (if i < 476 then (if i < 473 then (if i < 471 then decide (1 ≤ count470 b) else (if i < 472 then decide (2 ≤ count470 b) else decide (3 ≤ count470 b))) else (if i < 474 then decide (4 ≤ count470 b) else (if i < 475 then decide (1 ≤ count474 b) else decide (2 ≤ count474 b)))) else (if i < 479 then (if i < 477 then decide (3 ≤ count474 b) else (if i < 478 then decide (4 ≤ count474 b) else decide (5 ≤ count474 b))) else (if i < 481 then (if i < 480 then decide (6 ≤ count474 b) else decide (7 ≤ count474 b)) else (if i < 482 then decide (1 ≤ count481 b) else decide (2 ≤ count481 b))))) else (if i < 489 then (if i < 486 then (if i < 484 then decide (1 ≤ count483 b) else (if i < 485 then decide (2 ≤ count483 b) else decide (3 ≤ count483 b))) else (if i < 487 then decide (1 ≤ count486 b) else (if i < 488 then decide (2 ≤ count486 b) else decide (1 ≤ count488 b)))) else (if i < 492 then (if i < 490 then decide (2 ≤ count488 b) else (if i < 491 then decide (1 ≤ count490 b) else decide (2 ≤ count490 b))) else (if i < 494 then (if i < 493 then decide (3 ≤ count490 b) else decide (4 ≤ count490 b)) else (if i < 495 then decide (1 ≤ count494 b) else decide (2 ≤ count494 b)))))) else (if i < 509 then (if i < 502 then (if i < 499 then (if i < 497 then decide (3 ≤ count494 b) else (if i < 498 then decide (4 ≤ count494 b) else decide (5 ≤ count494 b))) else (if i < 500 then decide (6 ≤ count494 b) else (if i < 501 then decide (7 ≤ count494 b) else decide (1 ≤ count501 b)))) else (if i < 505 then (if i < 503 then decide (2 ≤ count501 b) else (if i < 504 then decide (3 ≤ count501 b) else decide (4 ≤ count501 b))) else (if i < 507 then (if i < 506 then decide (5 ≤ count501 b) else decide (6 ≤ count501 b)) else (if i < 508 then decide (7 ≤ count501 b) else decide (8 ≤ count501 b))))) else (if i < 515 then (if i < 512 then (if i < 510 then decide (9 ≤ count501 b) else (if i < 511 then decide (10 ≤ count501 b) else decide (11 ≤ count501 b))) else (if i < 513 then decide (12 ≤ count501 b) else (if i < 514 then decide (13 ≤ count501 b) else decide (14 ≤ count501 b)))) else (if i < 518 then (if i < 516 then decide (1 ≤ count515 b) else (if i < 517 then decide (2 ≤ count515 b) else decide (1 ≤ count517 b))) else (if i < 520 then (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b)) else (if i < 521 then decide (1 ≤ count520 b) else decide (2 ≤ count520 b)))))))) else (if i < 574 then (if i < 548 then (if i < 535 then (if i < 528 then (if i < 525 then (if i < 523 then decide (1 ≤ count522 b) else (if i < 524 then decide (2 ≤ count522 b) else decide (1 ≤ count524 b))) else (if i < 526 then decide (2 ≤ count524 b) else (if i < 527 then decide (3 ≤ count524 b) else decide (4 ≤ count524 b)))) else (if i < 531 then (if i < 529 then decide (1 ≤ count528 b) else (if i < 530 then decide (2 ≤ count528 b) else decide (3 ≤ count528 b))) else (if i < 533 then (if i < 532 then decide (4 ≤ count528 b) else decide (5 ≤ count528 b)) else (if i < 534 then decide (6 ≤ count528 b) else decide (7 ≤ count528 b))))) else (if i < 541 then (if i < 538 then (if i < 536 then decide (1 ≤ count535 b) else (if i < 537 then decide (2 ≤ count535 b) else decide (1 ≤ count537 b))) else (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (1 ≤ count539 b) else decide (2 ≤ count539 b)))) else (if i < 544 then (if i < 542 then decide (3 ≤ count539 b) else (if i < 543 then decide (4 ≤ count539 b) else decide (1 ≤ count543 b))) else (if i < 546 then (if i < 545 then decide (2 ≤ count543 b) else decide (1 ≤ count545 b)) else (if i < 547 then decide (2 ≤ count545 b) else decide (1 ≤ count547 b)))))) else (if i < 561 then (if i < 554 then (if i < 551 then (if i < 549 then decide (2 ≤ count547 b) else (if i < 550 then decide (3 ≤ count547 b) else decide (4 ≤ count547 b))) else (if i < 552 then decide (1 ≤ count551 b) else (if i < 553 then decide (2 ≤ count551 b) else decide (3 ≤ count551 b)))) else (if i < 557 then (if i < 555 then decide (4 ≤ count551 b) else (if i < 556 then decide (5 ≤ count551 b) else decide (6 ≤ count551 b))) else (if i < 559 then (if i < 558 then decide (7 ≤ count551 b) else decide (8 ≤ count551 b)) else (if i < 560 then decide (1 ≤ count559 b) else decide (2 ≤ count559 b))))) else (if i < 567 then (if i < 564 then (if i < 562 then decide (3 ≤ count559 b) else (if i < 563 then decide (4 ≤ count559 b) else decide (5 ≤ count559 b))) else (if i < 565 then decide (6 ≤ count559 b) else (if i < 566 then decide (7 ≤ count559 b) else decide (8 ≤ count559 b)))) else (if i < 570 then (if i < 568 then decide (9 ≤ count559 b) else (if i < 569 then decide (10 ≤ count559 b) else decide (11 ≤ count559 b))) else (if i < 572 then (if i < 571 then decide (12 ≤ count559 b) else decide (13 ≤ count559 b)) else (if i < 573 then decide (14 ≤ count559 b) else decide (15 ≤ count559 b))))))) else (if i < 600 then (if i < 587 then (if i < 580 then (if i < 577 then (if i < 575 then decide (1 ≤ count574 b) else (if i < 576 then decide (2 ≤ count574 b) else decide (3 ≤ count574 b))) else (if i < 578 then decide (4 ≤ count574 b) else (if i < 579 then decide (5 ≤ count574 b) else decide (6 ≤ count574 b)))) else (if i < 583 then (if i < 581 then decide (7 ≤ count574 b) else (if i < 582 then decide (8 ≤ count574 b) else decide (9 ≤ count574 b))) else (if i < 585 then (if i < 584 then decide (10 ≤ count574 b) else decide (11 ≤ count574 b)) else (if i < 586 then decide (12 ≤ count574 b) else decide (13 ≤ count574 b))))) else (if i < 593 then (if i < 590 then (if i < 588 then decide (14 ≤ count574 b) else (if i < 589 then decide (15 ≤ count574 b) else decide (16 ≤ count574 b))) else (if i < 591 then decide (17 ≤ count574 b) else (if i < 592 then decide (18 ≤ count574 b) else decide (19 ≤ count574 b)))) else (if i < 596 then (if i < 594 then decide (20 ≤ count574 b) else (if i < 595 then decide (21 ≤ count574 b) else decide (22 ≤ count574 b))) else (if i < 598 then (if i < 597 then decide (23 ≤ count574 b) else decide (24 ≤ count574 b)) else (if i < 599 then decide (25 ≤ count574 b) else decide (26 ≤ count574 b)))))) else (if i < 613 then (if i < 606 then (if i < 603 then (if i < 601 then decide (27 ≤ count574 b) else (if i < 602 then decide (28 ≤ count574 b) else decide (29 ≤ count574 b))) else (if i < 604 then decide (1 ≤ count603 b) else (if i < 605 then decide (2 ≤ count603 b) else decide (1 ≤ count605 b)))) else (if i < 609 then (if i < 607 then decide (2 ≤ count605 b) else (if i < 608 then decide (3 ≤ count605 b) else decide (1 ≤ count608 b))) else (if i < 611 then (if i < 610 then decide (2 ≤ count608 b) else decide (1 ≤ count610 b)) else (if i < 612 then decide (2 ≤ count610 b) else decide (1 ≤ count612 b))))) else (if i < 620 then (if i < 616 then (if i < 614 then decide (2 ≤ count612 b) else (if i < 615 then decide (3 ≤ count612 b) else decide (4 ≤ count612 b))) else (if i < 618 then (if i < 617 then decide (1 ≤ count616 b) else decide (2 ≤ count616 b)) else (if i < 619 then decide (3 ≤ count616 b) else decide (4 ≤ count616 b)))) else (if i < 623 then (if i < 621 then decide (5 ≤ count616 b) else (if i < 622 then decide (6 ≤ count616 b) else decide (7 ≤ count616 b))) else (if i < 625 then (if i < 624 then decide (1 ≤ count623 b) else decide (2 ≤ count623 b)) else (if i < 626 then decide (1 ≤ count625 b) else decide (2 ≤ count625 b))))))))) else (if i < 731 then (if i < 679 then (if i < 653 then (if i < 640 then (if i < 633 then (if i < 630 then (if i < 628 then decide (3 ≤ count625 b) else (if i < 629 then decide (1 ≤ count628 b) else decide (2 ≤ count628 b))) else (if i < 631 then decide (1 ≤ count630 b) else (if i < 632 then decide (2 ≤ count630 b) else decide (1 ≤ count632 b)))) else (if i < 636 then (if i < 634 then decide (2 ≤ count632 b) else (if i < 635 then decide (3 ≤ count632 b) else decide (4 ≤ count632 b))) else (if i < 638 then (if i < 637 then decide (1 ≤ count636 b) else decide (2 ≤ count636 b)) else (if i < 639 then decide (3 ≤ count636 b) else decide (4 ≤ count636 b))))) else (if i < 646 then (if i < 643 then (if i < 641 then decide (5 ≤ count636 b) else (if i < 642 then decide (6 ≤ count636 b) else decide (7 ≤ count636 b))) else (if i < 644 then decide (1 ≤ count643 b) else (if i < 645 then decide (2 ≤ count643 b) else decide (3 ≤ count643 b)))) else (if i < 649 then (if i < 647 then decide (4 ≤ count643 b) else (if i < 648 then decide (5 ≤ count643 b) else decide (6 ≤ count643 b))) else (if i < 651 then (if i < 650 then decide (7 ≤ count643 b) else decide (8 ≤ count643 b)) else (if i < 652 then decide (9 ≤ count643 b) else decide (10 ≤ count643 b)))))) else (if i < 666 then (if i < 659 then (if i < 656 then (if i < 654 then decide (11 ≤ count643 b) else (if i < 655 then decide (12 ≤ count643 b) else decide (13 ≤ count643 b))) else (if i < 657 then decide (14 ≤ count643 b) else (if i < 658 then decide (1 ≤ count657 b) else decide (2 ≤ count657 b)))) else (if i < 662 then (if i < 660 then decide (1 ≤ count659 b) else (if i < 661 then decide (2 ≤ count659 b) else decide (3 ≤ count659 b))) else (if i < 664 then (if i < 663 then decide (1 ≤ count662 b) else decide (2 ≤ count662 b)) else (if i < 665 then decide (1 ≤ count664 b) else decide (2 ≤ count664 b))))) else (if i < 672 then (if i < 669 then (if i < 667 then decide (1 ≤ count666 b) else (if i < 668 then decide (2 ≤ count666 b) else decide (3 ≤ count666 b))) else (if i < 670 then decide (4 ≤ count666 b) else (if i < 671 then decide (1 ≤ count670 b) else decide (2 ≤ count670 b)))) else (if i < 675 then (if i < 673 then decide (3 ≤ count670 b) else (if i < 674 then decide (4 ≤ count670 b) else decide (5 ≤ count670 b))) else (if i < 677 then (if i < 676 then decide (6 ≤ count670 b) else decide (7 ≤ count670 b)) else (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b))))))) else (if i < 705 then (if i < 692 then (if i < 685 then (if i < 682 then (if i < 680 then decide (1 ≤ count679 b) else (if i < 681 then decide (2 ≤ count679 b) else decide (1 ≤ count681 b))) else (if i < 683 then decide (2 ≤ count681 b) else (if i < 684 then decide (3 ≤ count681 b) else decide (4 ≤ count681 b)))) else (if i < 688 then (if i < 686 then decide (1 ≤ count685 b) else (if i < 687 then decide (2 ≤ count685 b) else decide (1 ≤ count687 b))) else (if i < 690 then (if i < 689 then decide (2 ≤ count687 b) else decide (1 ≤ count689 b)) else (if i < 691 then decide (2 ≤ count689 b) else decide (3 ≤ count689 b))))) else (if i < 698 then (if i < 695 then (if i < 693 then decide (4 ≤ count689 b) else (if i < 694 then decide (1 ≤ count693 b) else decide (2 ≤ count693 b))) else (if i < 696 then decide (3 ≤ count693 b) else (if i < 697 then decide (4 ≤ count693 b) else decide (5 ≤ count693 b)))) else (if i < 701 then (if i < 699 then decide (6 ≤ count693 b) else (if i < 700 then decide (7 ≤ count693 b) else decide (8 ≤ count693 b))) else (if i < 703 then (if i < 702 then decide (1 ≤ count701 b) else decide (2 ≤ count701 b)) else (if i < 704 then decide (3 ≤ count701 b) else decide (4 ≤ count701 b)))))) else (if i < 718 then (if i < 711 then (if i < 708 then (if i < 706 then decide (5 ≤ count701 b) else (if i < 707 then decide (6 ≤ count701 b) else decide (7 ≤ count701 b))) else (if i < 709 then decide (8 ≤ count701 b) else (if i < 710 then decide (9 ≤ count701 b) else decide (10 ≤ count701 b)))) else (if i < 714 then (if i < 712 then decide (11 ≤ count701 b) else (if i < 713 then decide (12 ≤ count701 b) else decide (13 ≤ count701 b))) else (if i < 716 then (if i < 715 then decide (14 ≤ count701 b) else decide (15 ≤ count701 b)) else (if i < 717 then decide (1 ≤ count716 b) else decide (2 ≤ count716 b))))) else (if i < 724 then (if i < 721 then (if i < 719 then decide (3 ≤ count716 b) else (if i < 720 then decide (4 ≤ count716 b) else decide (5 ≤ count716 b))) else (if i < 722 then decide (6 ≤ count716 b) else (if i < 723 then decide (7 ≤ count716 b) else decide (8 ≤ count716 b)))) else (if i < 727 then (if i < 725 then decide (9 ≤ count716 b) else (if i < 726 then decide (10 ≤ count716 b) else decide (11 ≤ count716 b))) else (if i < 729 then (if i < 728 then decide (12 ≤ count716 b) else decide (13 ≤ count716 b)) else (if i < 730 then decide (14 ≤ count716 b) else decide (15 ≤ count716 b)))))))) else (if i < 783 then (if i < 757 then (if i < 744 then (if i < 737 then (if i < 734 then (if i < 732 then decide (16 ≤ count716 b) else (if i < 733 then decide (17 ≤ count716 b) else decide (18 ≤ count716 b))) else (if i < 735 then decide (19 ≤ count716 b) else (if i < 736 then decide (20 ≤ count716 b) else decide (21 ≤ count716 b)))) else (if i < 740 then (if i < 738 then decide (22 ≤ count716 b) else (if i < 739 then decide (23 ≤ count716 b) else decide (24 ≤ count716 b))) else (if i < 742 then (if i < 741 then decide (25 ≤ count716 b) else decide (26 ≤ count716 b)) else (if i < 743 then decide (27 ≤ count716 b) else decide (28 ≤ count716 b))))) else (if i < 750 then (if i < 747 then (if i < 745 then decide (29 ≤ count716 b) else (if i < 746 then decide (1 ≤ count745 b) else decide (2 ≤ count745 b))) else (if i < 748 then decide (3 ≤ count745 b) else (if i < 749 then decide (4 ≤ count745 b) else decide (5 ≤ count745 b)))) else (if i < 753 then (if i < 751 then decide (6 ≤ count745 b) else (if i < 752 then decide (7 ≤ count745 b) else decide (8 ≤ count745 b))) else (if i < 755 then (if i < 754 then decide (9 ≤ count745 b) else decide (10 ≤ count745 b)) else (if i < 756 then decide (11 ≤ count745 b) else decide (12 ≤ count745 b)))))) else (if i < 770 then (if i < 763 then (if i < 760 then (if i < 758 then decide (13 ≤ count745 b) else (if i < 759 then decide (14 ≤ count745 b) else decide (15 ≤ count745 b))) else (if i < 761 then decide (16 ≤ count745 b) else (if i < 762 then decide (17 ≤ count745 b) else decide (18 ≤ count745 b)))) else (if i < 766 then (if i < 764 then decide (19 ≤ count745 b) else (if i < 765 then decide (20 ≤ count745 b) else decide (21 ≤ count745 b))) else (if i < 768 then (if i < 767 then decide (22 ≤ count745 b) else decide (23 ≤ count745 b)) else (if i < 769 then decide (24 ≤ count745 b) else decide (25 ≤ count745 b))))) else (if i < 776 then (if i < 773 then (if i < 771 then decide (26 ≤ count745 b) else (if i < 772 then decide (27 ≤ count745 b) else decide (28 ≤ count745 b))) else (if i < 774 then decide (29 ≤ count745 b) else (if i < 775 then decide (30 ≤ count745 b) else decide (31 ≤ count745 b)))) else (if i < 779 then (if i < 777 then decide (32 ≤ count745 b) else (if i < 778 then decide (33 ≤ count745 b) else decide (34 ≤ count745 b))) else (if i < 781 then (if i < 780 then decide (35 ≤ count745 b) else decide (36 ≤ count745 b)) else (if i < 782 then decide (37 ≤ count745 b) else decide (38 ≤ count745 b))))))) else (if i < 809 then (if i < 796 then (if i < 789 then (if i < 786 then (if i < 784 then decide (39 ≤ count745 b) else (if i < 785 then decide (40 ≤ count745 b) else decide (41 ≤ count745 b))) else (if i < 787 then decide (42 ≤ count745 b) else (if i < 788 then decide (1 ≤ count787 b) else decide (2 ≤ count787 b)))) else (if i < 792 then (if i < 790 then decide (1 ≤ count789 b) else (if i < 791 then decide (2 ≤ count789 b) else decide (3 ≤ count789 b))) else (if i < 794 then (if i < 793 then decide (1 ≤ count792 b) else decide (2 ≤ count792 b)) else (if i < 795 then decide (1 ≤ count794 b) else decide (2 ≤ count794 b))))) else (if i < 802 then (if i < 799 then (if i < 797 then decide (1 ≤ count796 b) else (if i < 798 then decide (2 ≤ count796 b) else decide (3 ≤ count796 b))) else (if i < 800 then decide (4 ≤ count796 b) else (if i < 801 then decide (1 ≤ count800 b) else decide (2 ≤ count800 b)))) else (if i < 805 then (if i < 803 then decide (3 ≤ count800 b) else (if i < 804 then decide (4 ≤ count800 b) else decide (5 ≤ count800 b))) else (if i < 807 then (if i < 806 then decide (6 ≤ count800 b) else decide (7 ≤ count800 b)) else (if i < 808 then decide (1 ≤ count807 b) else decide (2 ≤ count807 b)))))) else (if i < 822 then (if i < 815 then (if i < 812 then (if i < 810 then decide (1 ≤ count809 b) else (if i < 811 then decide (2 ≤ count809 b) else decide (3 ≤ count809 b))) else (if i < 813 then decide (1 ≤ count812 b) else (if i < 814 then decide (2 ≤ count812 b) else decide (1 ≤ count814 b)))) else (if i < 818 then (if i < 816 then decide (2 ≤ count814 b) else (if i < 817 then decide (1 ≤ count816 b) else decide (2 ≤ count816 b))) else (if i < 820 then (if i < 819 then decide (3 ≤ count816 b) else decide (4 ≤ count816 b)) else (if i < 821 then decide (1 ≤ count820 b) else decide (2 ≤ count820 b))))) else (if i < 829 then (if i < 825 then (if i < 823 then decide (3 ≤ count820 b) else (if i < 824 then decide (4 ≤ count820 b) else decide (5 ≤ count820 b))) else (if i < 827 then (if i < 826 then decide (6 ≤ count820 b) else decide (7 ≤ count820 b)) else (if i < 828 then decide (1 ≤ count827 b) else decide (2 ≤ count827 b)))) else (if i < 832 then (if i < 830 then decide (3 ≤ count827 b) else (if i < 831 then decide (4 ≤ count827 b) else decide (5 ≤ count827 b))) else (if i < 834 then (if i < 833 then decide (6 ≤ count827 b) else decide (7 ≤ count827 b)) else (if i < 835 then decide (8 ≤ count827 b) else decide (9 ≤ count827 b))))))))))) else (if i < 1254 then (if i < 1045 then (if i < 940 then (if i < 888 then (if i < 862 then (if i < 849 then (if i < 842 then (if i < 839 then (if i < 837 then decide (10 ≤ count827 b) else (if i < 838 then decide (11 ≤ count827 b) else decide (12 ≤ count827 b))) else (if i < 840 then decide (13 ≤ count827 b) else (if i < 841 then decide (14 ≤ count827 b) else decide (1 ≤ count841 b)))) else (if i < 845 then (if i < 843 then decide (2 ≤ count841 b) else (if i < 844 then decide (1 ≤ count843 b) else decide (2 ≤ count843 b))) else (if i < 847 then (if i < 846 then decide (3 ≤ count843 b) else decide (1 ≤ count846 b)) else (if i < 848 then decide (2 ≤ count846 b) else decide (1 ≤ count848 b))))) else (if i < 855 then (if i < 852 then (if i < 850 then decide (2 ≤ count848 b) else (if i < 851 then decide (1 ≤ count850 b) else decide (2 ≤ count850 b))) else (if i < 853 then decide (3 ≤ count850 b) else (if i < 854 then decide (4 ≤ count850 b) else decide (1 ≤ count854 b)))) else (if i < 858 then (if i < 856 then decide (2 ≤ count854 b) else (if i < 857 then decide (3 ≤ count854 b) else decide (4 ≤ count854 b))) else (if i < 860 then (if i < 859 then decide (5 ≤ count854 b) else decide (6 ≤ count854 b)) else (if i < 861 then decide (7 ≤ count854 b) else decide (1 ≤ count861 b)))))) else (if i < 875 then (if i < 868 then (if i < 865 then (if i < 863 then decide (2 ≤ count861 b) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b))) else (if i < 866 then decide (1 ≤ count865 b) else (if i < 867 then decide (2 ≤ count865 b) else decide (3 ≤ count865 b)))) else (if i < 871 then (if i < 869 then decide (4 ≤ count865 b) else (if i < 870 then decide (1 ≤ count869 b) else decide (2 ≤ count869 b))) else (if i < 873 then (if i < 872 then decide (1 ≤ count871 b) else decide (2 ≤ count871 b)) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b))))) else (if i < 881 then (if i < 878 then (if i < 876 then decide (3 ≤ count873 b) else (if i < 877 then decide (4 ≤ count873 b) else decide (1 ≤ count877 b))) else (if i < 879 then decide (2 ≤ count877 b) else (if i < 880 then decide (3 ≤ count877 b) else decide (4 ≤ count877 b)))) else (if i < 884 then (if i < 882 then decide (5 ≤ count877 b) else (if i < 883 then decide (6 ≤ count877 b) else decide (7 ≤ count877 b))) else (if i < 886 then (if i < 885 then decide (8 ≤ count877 b) else decide (1 ≤ count885 b)) else (if i < 887 then decide (2 ≤ count885 b) else decide (3 ≤ count885 b))))))) else (if i < 914 then (if i < 901 then (if i < 894 then (if i < 891 then (if i < 889 then decide (4 ≤ count885 b) else (if i < 890 then decide (5 ≤ count885 b) else decide (6 ≤ count885 b))) else (if i < 892 then decide (7 ≤ count885 b) else (if i < 893 then decide (8 ≤ count885 b) else decide (9 ≤ count885 b)))) else (if i < 897 then (if i < 895 then decide (10 ≤ count885 b) else (if i < 896 then decide (11 ≤ count885 b) else decide (12 ≤ count885 b))) else (if i < 899 then (if i < 898 then decide (13 ≤ count885 b) else decide (14 ≤ count885 b)) else (if i < 900 then decide (15 ≤ count885 b) else decide (1 ≤ count900 b))))) else (if i < 907 then (if i < 904 then (if i < 902 then decide (2 ≤ count900 b) else (if i < 903 then decide (3 ≤ count900 b) else decide (4 ≤ count900 b))) else (if i < 905 then decide (5 ≤ count900 b) else (if i < 906 then decide (6 ≤ count900 b) else decide (7 ≤ count900 b)))) else (if i < 910 then (if i < 908 then decide (8 ≤ count900 b) else (if i < 909 then decide (9 ≤ count900 b) else decide (10 ≤ count900 b))) else (if i < 912 then (if i < 911 then decide (11 ≤ count900 b) else decide (12 ≤ count900 b)) else (if i < 913 then decide (13 ≤ count900 b) else decide (14 ≤ count900 b)))))) else (if i < 927 then (if i < 920 then (if i < 917 then (if i < 915 then decide (15 ≤ count900 b) else (if i < 916 then decide (16 ≤ count900 b) else decide (17 ≤ count900 b))) else (if i < 918 then decide (18 ≤ count900 b) else (if i < 919 then decide (1 ≤ count918 b) else decide (2 ≤ count918 b)))) else (if i < 923 then (if i < 921 then decide (1 ≤ count920 b) else (if i < 922 then decide (2 ≤ count920 b) else decide (3 ≤ count920 b))) else (if i < 925 then (if i < 924 then decide (1 ≤ count923 b) else decide (2 ≤ count923 b)) else (if i < 926 then decide (1 ≤ count925 b) else decide (2 ≤ count925 b))))) else (if i < 933 then (if i < 930 then (if i < 928 then decide (1 ≤ count927 b) else (if i < 929 then decide (2 ≤ count927 b) else decide (3 ≤ count927 b))) else (if i < 931 then decide (4 ≤ count927 b) else (if i < 932 then decide (1 ≤ count931 b) else decide (2 ≤ count931 b)))) else (if i < 936 then (if i < 934 then decide (3 ≤ count931 b) else (if i < 935 then decide (4 ≤ count931 b) else decide (5 ≤ count931 b))) else (if i < 938 then (if i < 937 then decide (6 ≤ count931 b) else decide (7 ≤ count931 b)) else (if i < 939 then decide (1 ≤ count938 b) else decide (2 ≤ count938 b)))))))) else (if i < 992 then (if i < 966 then (if i < 953 then (if i < 946 then (if i < 943 then (if i < 941 then decide (1 ≤ count940 b) else (if i < 942 then decide (2 ≤ count940 b) else decide (3 ≤ count940 b))) else (if i < 944 then decide (1 ≤ count943 b) else (if i < 945 then decide (2 ≤ count943 b) else decide (1 ≤ count945 b)))) else (if i < 949 then (if i < 947 then decide (2 ≤ count945 b) else (if i < 948 then decide (1 ≤ count947 b) else decide (2 ≤ count947 b))) else (if i < 951 then (if i < 950 then decide (3 ≤ count947 b) else decide (4 ≤ count947 b)) else (if i < 952 then decide (1 ≤ count951 b) else decide (2 ≤ count951 b))))) else (if i < 959 then (if i < 956 then (if i < 954 then decide (3 ≤ count951 b) else (if i < 955 then decide (4 ≤ count951 b) else decide (5 ≤ count951 b))) else (if i < 957 then decide (6 ≤ count951 b) else (if i < 958 then decide (7 ≤ count951 b) else decide (1 ≤ count958 b)))) else (if i < 962 then (if i < 960 then decide (2 ≤ count958 b) else (if i < 961 then decide (3 ≤ count958 b) else decide (4 ≤ count958 b))) else (if i < 964 then (if i < 963 then decide (5 ≤ count958 b) else decide (6 ≤ count958 b)) else (if i < 965 then decide (7 ≤ count958 b) else decide (8 ≤ count958 b)))))) else (if i < 979 then (if i < 972 then (if i < 969 then (if i < 967 then decide (9 ≤ count958 b) else (if i < 968 then decide (10 ≤ count958 b) else decide (11 ≤ count958 b))) else (if i < 970 then decide (12 ≤ count958 b) else (if i < 971 then decide (13 ≤ count958 b) else decide (14 ≤ count958 b)))) else (if i < 975 then (if i < 973 then decide (1 ≤ count972 b) else (if i < 974 then decide (2 ≤ count972 b) else decide (1 ≤ count974 b))) else (if i < 977 then (if i < 976 then decide (2 ≤ count974 b) else decide (3 ≤ count974 b)) else (if i < 978 then decide (1 ≤ count977 b) else decide (2 ≤ count977 b))))) else (if i < 985 then (if i < 982 then (if i < 980 then decide (1 ≤ count979 b) else (if i < 981 then decide (2 ≤ count979 b) else decide (1 ≤ count981 b))) else (if i < 983 then decide (2 ≤ count981 b) else (if i < 984 then decide (3 ≤ count981 b) else decide (4 ≤ count981 b)))) else (if i < 988 then (if i < 986 then decide (1 ≤ count985 b) else (if i < 987 then decide (2 ≤ count985 b) else decide (3 ≤ count985 b))) else (if i < 990 then (if i < 989 then decide (4 ≤ count985 b) else decide (5 ≤ count985 b)) else (if i < 991 then decide (6 ≤ count985 b) else decide (7 ≤ count985 b))))))) else (if i < 1018 then (if i < 1005 then (if i < 998 then (if i < 995 then (if i < 993 then decide (1 ≤ count992 b) else (if i < 994 then decide (2 ≤ count992 b) else decide (1 ≤ count994 b))) else (if i < 996 then decide (2 ≤ count994 b) else (if i < 997 then decide (1 ≤ count996 b) else decide (2 ≤ count996 b)))) else (if i < 1001 then (if i < 999 then decide (3 ≤ count996 b) else (if i < 1000 then decide (4 ≤ count996 b) else decide (1 ≤ count1000 b))) else (if i < 1003 then (if i < 1002 then decide (2 ≤ count1000 b) else decide (1 ≤ count1002 b)) else (if i < 1004 then decide (2 ≤ count1002 b) else decide (1 ≤ count1004 b))))) else (if i < 1011 then (if i < 1008 then (if i < 1006 then decide (2 ≤ count1004 b) else (if i < 1007 then decide (3 ≤ count1004 b) else decide (4 ≤ count1004 b))) else (if i < 1009 then decide (1 ≤ count1008 b) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (3 ≤ count1008 b)))) else (if i < 1014 then (if i < 1012 then decide (4 ≤ count1008 b) else (if i < 1013 then decide (5 ≤ count1008 b) else decide (6 ≤ count1008 b))) else (if i < 1016 then (if i < 1015 then decide (7 ≤ count1008 b) else decide (8 ≤ count1008 b)) else (if i < 1017 then decide (1 ≤ count1016 b) else decide (2 ≤ count1016 b)))))) else (if i < 1031 then (if i < 1024 then (if i < 1021 then (if i < 1019 then decide (3 ≤ count1016 b) else (if i < 1020 then decide (4 ≤ count1016 b) else decide (5 ≤ count1016 b))) else (if i < 1022 then decide (6 ≤ count1016 b) else (if i < 1023 then decide (7 ≤ count1016 b) else decide (8 ≤ count1016 b)))) else (if i < 1027 then (if i < 1025 then decide (9 ≤ count1016 b) else (if i < 1026 then decide (10 ≤ count1016 b) else decide (11 ≤ count1016 b))) else (if i < 1029 then (if i < 1028 then decide (12 ≤ count1016 b) else decide (13 ≤ count1016 b)) else (if i < 1030 then decide (14 ≤ count1016 b) else decide (15 ≤ count1016 b))))) else (if i < 1038 then (if i < 1034 then (if i < 1032 then decide (1 ≤ count1031 b) else (if i < 1033 then decide (2 ≤ count1031 b) else decide (3 ≤ count1031 b))) else (if i < 1036 then (if i < 1035 then decide (4 ≤ count1031 b) else decide (5 ≤ count1031 b)) else (if i < 1037 then decide (6 ≤ count1031 b) else decide (7 ≤ count1031 b)))) else (if i < 1041 then (if i < 1039 then decide (8 ≤ count1031 b) else (if i < 1040 then decide (9 ≤ count1031 b) else decide (10 ≤ count1031 b))) else (if i < 1043 then (if i < 1042 then decide (11 ≤ count1031 b) else decide (12 ≤ count1031 b)) else (if i < 1044 then decide (13 ≤ count1031 b) else decide (14 ≤ count1031 b))))))))) else (if i < 1149 then (if i < 1097 then (if i < 1071 then (if i < 1058 then (if i < 1051 then (if i < 1048 then (if i < 1046 then decide (15 ≤ count1031 b) else (if i < 1047 then decide (16 ≤ count1031 b) else decide (17 ≤ count1031 b))) else (if i < 1049 then decide (18 ≤ count1031 b) else (if i < 1050 then decide (1 ≤ count1049 b) else decide (2 ≤ count1049 b)))) else (if i < 1054 then (if i < 1052 then decide (3 ≤ count1049 b) else (if i < 1053 then decide (4 ≤ count1049 b) else decide (5 ≤ count1049 b))) else (if i < 1056 then (if i < 1055 then decide (6 ≤ count1049 b) else decide (7 ≤ count1049 b)) else (if i < 1057 then decide (8 ≤ count1049 b) else decide (9 ≤ count1049 b))))) else (if i < 1064 then (if i < 1061 then (if i < 1059 then decide (10 ≤ count1049 b) else (if i < 1060 then decide (11 ≤ count1049 b) else decide (12 ≤ count1049 b))) else (if i < 1062 then decide (13 ≤ count1049 b) else (if i < 1063 then decide (14 ≤ count1049 b) else decide (15 ≤ count1049 b)))) else (if i < 1067 then (if i < 1065 then decide (16 ≤ count1049 b) else (if i < 1066 then decide (17 ≤ count1049 b) else decide (18 ≤ count1049 b))) else (if i < 1069 then (if i < 1068 then decide (1 ≤ count1067 b) else decide (2 ≤ count1067 b)) else (if i < 1070 then decide (1 ≤ count1069 b) else decide (2 ≤ count1069 b)))))) else (if i < 1084 then (if i < 1077 then (if i < 1074 then (if i < 1072 then decide (3 ≤ count1069 b) else (if i < 1073 then decide (1 ≤ count1072 b) else decide (2 ≤ count1072 b))) else (if i < 1075 then decide (1 ≤ count1074 b) else (if i < 1076 then decide (2 ≤ count1074 b) else decide (1 ≤ count1076 b)))) else (if i < 1080 then (if i < 1078 then decide (2 ≤ count1076 b) else (if i < 1079 then decide (3 ≤ count1076 b) else decide (4 ≤ count1076 b))) else (if i < 1082 then (if i < 1081 then decide (1 ≤ count1080 b) else decide (2 ≤ count1080 b)) else (if i < 1083 then decide (3 ≤ count1080 b) else decide (4 ≤ count1080 b))))) else (if i < 1090 then (if i < 1087 then (if i < 1085 then decide (5 ≤ count1080 b) else (if i < 1086 then decide (6 ≤ count1080 b) else decide (7 ≤ count1080 b))) else (if i < 1088 then decide (1 ≤ count1087 b) else (if i < 1089 then decide (2 ≤ count1087 b) else decide (1 ≤ count1089 b)))) else (if i < 1093 then (if i < 1091 then decide (2 ≤ count1089 b) else (if i < 1092 then decide (3 ≤ count1089 b) else decide (1 ≤ count1092 b))) else (if i < 1095 then (if i < 1094 then decide (2 ≤ count1092 b) else decide (1 ≤ count1094 b)) else (if i < 1096 then decide (2 ≤ count1094 b) else decide (1 ≤ count1096 b))))))) else (if i < 1123 then (if i < 1110 then (if i < 1103 then (if i < 1100 then (if i < 1098 then decide (2 ≤ count1096 b) else (if i < 1099 then decide (3 ≤ count1096 b) else decide (4 ≤ count1096 b))) else (if i < 1101 then decide (1 ≤ count1100 b) else (if i < 1102 then decide (2 ≤ count1100 b) else decide (3 ≤ count1100 b)))) else (if i < 1106 then (if i < 1104 then decide (4 ≤ count1100 b) else (if i < 1105 then decide (5 ≤ count1100 b) else decide (6 ≤ count1100 b))) else (if i < 1108 then (if i < 1107 then decide (7 ≤ count1100 b) else decide (1 ≤ count1107 b)) else (if i < 1109 then decide (2 ≤ count1107 b) else decide (3 ≤ count1107 b))))) else (if i < 1116 then (if i < 1113 then (if i < 1111 then decide (4 ≤ count1107 b) else (if i < 1112 then decide (5 ≤ count1107 b) else decide (6 ≤ count1107 b))) else (if i < 1114 then decide (7 ≤ count1107 b) else (if i < 1115 then decide (8 ≤ count1107 b) else decide (9 ≤ count1107 b)))) else (if i < 1119 then (if i < 1117 then decide (10 ≤ count1107 b) else (if i < 1118 then decide (11 ≤ count1107 b) else decide (12 ≤ count1107 b))) else (if i < 1121 then (if i < 1120 then decide (13 ≤ count1107 b) else decide (14 ≤ count1107 b)) else (if i < 1122 then decide (1 ≤ count1121 b) else decide (2 ≤ count1121 b)))))) else (if i < 1136 then (if i < 1129 then (if i < 1126 then (if i < 1124 then decide (1 ≤ count1123 b) else (if i < 1125 then decide (2 ≤ count1123 b) else decide (3 ≤ count1123 b))) else (if i < 1127 then decide (1 ≤ count1126 b) else (if i < 1128 then decide (2 ≤ count1126 b) else decide (1 ≤ count1128 b)))) else (if i < 1132 then (if i < 1130 then decide (2 ≤ count1128 b) else (if i < 1131 then decide (1 ≤ count1130 b) else decide (2 ≤ count1130 b))) else (if i < 1134 then (if i < 1133 then decide (3 ≤ count1130 b) else decide (4 ≤ count1130 b)) else (if i < 1135 then decide (1 ≤ count1134 b) else decide (2 ≤ count1134 b))))) else (if i < 1142 then (if i < 1139 then (if i < 1137 then decide (3 ≤ count1134 b) else (if i < 1138 then decide (4 ≤ count1134 b) else decide (5 ≤ count1134 b))) else (if i < 1140 then decide (6 ≤ count1134 b) else (if i < 1141 then decide (7 ≤ count1134 b) else decide (1 ≤ count1141 b)))) else (if i < 1145 then (if i < 1143 then decide (2 ≤ count1141 b) else (if i < 1144 then decide (1 ≤ count1143 b) else decide (2 ≤ count1143 b))) else (if i < 1147 then (if i < 1146 then decide (1 ≤ count1145 b) else decide (2 ≤ count1145 b)) else (if i < 1148 then decide (3 ≤ count1145 b) else decide (4 ≤ count1145 b)))))))) else (if i < 1201 then (if i < 1175 then (if i < 1162 then (if i < 1155 then (if i < 1152 then (if i < 1150 then decide (1 ≤ count1149 b) else (if i < 1151 then decide (2 ≤ count1149 b) else decide (1 ≤ count1151 b))) else (if i < 1153 then decide (2 ≤ count1151 b) else (if i < 1154 then decide (1 ≤ count1153 b) else decide (2 ≤ count1153 b)))) else (if i < 1158 then (if i < 1156 then decide (3 ≤ count1153 b) else (if i < 1157 then decide (4 ≤ count1153 b) else decide (1 ≤ count1157 b))) else (if i < 1160 then (if i < 1159 then decide (2 ≤ count1157 b) else decide (3 ≤ count1157 b)) else (if i < 1161 then decide (4 ≤ count1157 b) else decide (5 ≤ count1157 b))))) else (if i < 1168 then (if i < 1165 then (if i < 1163 then decide (6 ≤ count1157 b) else (if i < 1164 then decide (7 ≤ count1157 b) else decide (8 ≤ count1157 b))) else (if i < 1166 then decide (1 ≤ count1165 b) else (if i < 1167 then decide (2 ≤ count1165 b) else decide (3 ≤ count1165 b)))) else (if i < 1171 then (if i < 1169 then decide (4 ≤ count1165 b) else (if i < 1170 then decide (5 ≤ count1165 b) else decide (6 ≤ count1165 b))) else (if i < 1173 then (if i < 1172 then decide (7 ≤ count1165 b) else decide (8 ≤ count1165 b)) else (if i < 1174 then decide (9 ≤ count1165 b) else decide (10 ≤ count1165 b)))))) else (if i < 1188 then (if i < 1181 then (if i < 1178 then (if i < 1176 then decide (11 ≤ count1165 b) else (if i < 1177 then decide (12 ≤ count1165 b) else decide (13 ≤ count1165 b))) else (if i < 1179 then decide (14 ≤ count1165 b) else (if i < 1180 then decide (15 ≤ count1165 b) else decide (1 ≤ count1180 b)))) else (if i < 1184 then (if i < 1182 then decide (2 ≤ count1180 b) else (if i < 1183 then decide (3 ≤ count1180 b) else decide (4 ≤ count1180 b))) else (if i < 1186 then (if i < 1185 then decide (5 ≤ count1180 b) else decide (6 ≤ count1180 b)) else (if i < 1187 then decide (7 ≤ count1180 b) else decide (8 ≤ count1180 b))))) else (if i < 1194 then (if i < 1191 then (if i < 1189 then decide (9 ≤ count1180 b) else (if i < 1190 then decide (10 ≤ count1180 b) else decide (11 ≤ count1180 b))) else (if i < 1192 then decide (12 ≤ count1180 b) else (if i < 1193 then decide (13 ≤ count1180 b) else decide (14 ≤ count1180 b)))) else (if i < 1197 then (if i < 1195 then decide (15 ≤ count1180 b) else (if i < 1196 then decide (16 ≤ count1180 b) else decide (17 ≤ count1180 b))) else (if i < 1199 then (if i < 1198 then decide (18 ≤ count1180 b) else decide (19 ≤ count1180 b)) else (if i < 1200 then decide (20 ≤ count1180 b) else decide (21 ≤ count1180 b))))))) else (if i < 1227 then (if i < 1214 then (if i < 1207 then (if i < 1204 then (if i < 1202 then decide (22 ≤ count1180 b) else (if i < 1203 then decide (23 ≤ count1180 b) else decide (24 ≤ count1180 b))) else (if i < 1205 then decide (25 ≤ count1180 b) else (if i < 1206 then decide (26 ≤ count1180 b) else decide (27 ≤ count1180 b)))) else (if i < 1210 then (if i < 1208 then decide (28 ≤ count1180 b) else (if i < 1209 then decide (29 ≤ count1180 b) else decide (1 ≤ count1209 b))) else (if i < 1212 then (if i < 1211 then decide (2 ≤ count1209 b) else decide (1 ≤ count1211 b)) else (if i < 1213 then decide (2 ≤ count1211 b) else decide (3 ≤ count1211 b))))) else (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (1 ≤ count1214 b) else (if i < 1216 then decide (2 ≤ count1214 b) else decide (1 ≤ count1216 b))) else (if i < 1218 then decide (2 ≤ count1216 b) else (if i < 1219 then decide (1 ≤ count1218 b) else decide (2 ≤ count1218 b)))) else (if i < 1223 then (if i < 1221 then decide (3 ≤ count1218 b) else (if i < 1222 then decide (4 ≤ count1218 b) else decide (1 ≤ count1222 b))) else (if i < 1225 then (if i < 1224 then decide (2 ≤ count1222 b) else decide (3 ≤ count1222 b)) else (if i < 1226 then decide (4 ≤ count1222 b) else decide (5 ≤ count1222 b)))))) else (if i < 1240 then (if i < 1233 then (if i < 1230 then (if i < 1228 then decide (6 ≤ count1222 b) else (if i < 1229 then decide (7 ≤ count1222 b) else decide (1 ≤ count1229 b))) else (if i < 1231 then decide (2 ≤ count1229 b) else (if i < 1232 then decide (1 ≤ count1231 b) else decide (2 ≤ count1231 b)))) else (if i < 1236 then (if i < 1234 then decide (3 ≤ count1231 b) else (if i < 1235 then decide (1 ≤ count1234 b) else decide (2 ≤ count1234 b))) else (if i < 1238 then (if i < 1237 then decide (1 ≤ count1236 b) else decide (2 ≤ count1236 b)) else (if i < 1239 then decide (1 ≤ count1238 b) else decide (2 ≤ count1238 b))))) else (if i < 1247 then (if i < 1243 then (if i < 1241 then decide (3 ≤ count1238 b) else (if i < 1242 then decide (4 ≤ count1238 b) else decide (1 ≤ count1242 b))) else (if i < 1245 then (if i < 1244 then decide (2 ≤ count1242 b) else decide (3 ≤ count1242 b)) else (if i < 1246 then decide (4 ≤ count1242 b) else decide (5 ≤ count1242 b)))) else (if i < 1250 then (if i < 1248 then decide (6 ≤ count1242 b) else (if i < 1249 then decide (7 ≤ count1242 b) else decide (1 ≤ count1249 b))) else (if i < 1252 then (if i < 1251 then decide (2 ≤ count1249 b) else decide (3 ≤ count1249 b)) else (if i < 1253 then decide (4 ≤ count1249 b) else decide (5 ≤ count1249 b)))))))))) else (if i < 1463 then (if i < 1358 then (if i < 1306 then (if i < 1280 then (if i < 1267 then (if i < 1260 then (if i < 1257 then (if i < 1255 then decide (6 ≤ count1249 b) else (if i < 1256 then decide (7 ≤ count1249 b) else decide (8 ≤ count1249 b))) else (if i < 1258 then decide (9 ≤ count1249 b) else (if i < 1259 then decide (10 ≤ count1249 b) else decide (11 ≤ count1249 b)))) else (if i < 1263 then (if i < 1261 then decide (12 ≤ count1249 b) else (if i < 1262 then decide (13 ≤ count1249 b) else decide (14 ≤ count1249 b))) else (if i < 1265 then (if i < 1264 then decide (1 ≤ count1263 b) else decide (2 ≤ count1263 b)) else (if i < 1266 then decide (1 ≤ count1265 b) else decide (2 ≤ count1265 b))))) else (if i < 1273 then (if i < 1270 then (if i < 1268 then decide (3 ≤ count1265 b) else (if i < 1269 then decide (1 ≤ count1268 b) else decide (2 ≤ count1268 b))) else (if i < 1271 then decide (1 ≤ count1270 b) else (if i < 1272 then decide (2 ≤ count1270 b) else decide (1 ≤ count1272 b)))) else (if i < 1276 then (if i < 1274 then decide (2 ≤ count1272 b) else (if i < 1275 then decide (3 ≤ count1272 b) else decide (4 ≤ count1272 b))) else (if i < 1278 then (if i < 1277 then decide (1 ≤ count1276 b) else decide (2 ≤ count1276 b)) else (if i < 1279 then decide (3 ≤ count1276 b) else decide (4 ≤ count1276 b)))))) else (if i < 1293 then (if i < 1286 then (if i < 1283 then (if i < 1281 then decide (5 ≤ count1276 b) else (if i < 1282 then decide (6 ≤ count1276 b) else decide (7 ≤ count1276 b))) else (if i < 1284 then decide (1 ≤ count1283 b) else (if i < 1285 then decide (2 ≤ count1283 b) else decide (1 ≤ count1285 b)))) else (if i < 1289 then (if i < 1287 then decide (2 ≤ count1285 b) else (if i < 1288 then decide (1 ≤ count1287 b) else decide (2 ≤ count1287 b))) else (if i < 1291 then (if i < 1290 then decide (3 ≤ count1287 b) else decide (4 ≤ count1287 b)) else (if i < 1292 then decide (1 ≤ count1291 b) else decide (2 ≤ count1291 b))))) else (if i < 1299 then (if i < 1296 then (if i < 1294 then decide (1 ≤ count1293 b) else (if i < 1295 then decide (2 ≤ count1293 b) else decide (1 ≤ count1295 b))) else (if i < 1297 then decide (2 ≤ count1295 b) else (if i < 1298 then decide (3 ≤ count1295 b) else decide (4 ≤ count1295 b)))) else (if i < 1302 then (if i < 1300 then decide (1 ≤ count1299 b) else (if i < 1301 then decide (2 ≤ count1299 b) else decide (3 ≤ count1299 b))) else (if i < 1304 then (if i < 1303 then decide (4 ≤ count1299 b) else decide (5 ≤ count1299 b)) else (if i < 1305 then decide (6 ≤ count1299 b) else decide (7 ≤ count1299 b))))))) else (if i < 1332 then (if i < 1319 then (if i < 1312 then (if i < 1309 then (if i < 1307 then decide (8 ≤ count1299 b) else (if i < 1308 then decide (1 ≤ count1307 b) else decide (2 ≤ count1307 b))) else (if i < 1310 then decide (3 ≤ count1307 b) else (if i < 1311 then decide (4 ≤ count1307 b) else decide (5 ≤ count1307 b)))) else (if i < 1315 then (if i < 1313 then decide (6 ≤ count1307 b) else (if i < 1314 then decide (7 ≤ count1307 b) else decide (8 ≤ count1307 b))) else (if i < 1317 then (if i < 1316 then decide (9 ≤ count1307 b) else decide (10 ≤ count1307 b)) else (if i < 1318 then decide (11 ≤ count1307 b) else decide (12 ≤ count1307 b))))) else (if i < 1325 then (if i < 1322 then (if i < 1320 then decide (13 ≤ count1307 b) else (if i < 1321 then decide (14 ≤ count1307 b) else decide (15 ≤ count1307 b))) else (if i < 1323 then decide (1 ≤ count1322 b) else (if i < 1324 then decide (2 ≤ count1322 b) else decide (3 ≤ count1322 b)))) else (if i < 1328 then (if i < 1326 then decide (4 ≤ count1322 b) else (if i < 1327 then decide (5 ≤ count1322 b) else decide (6 ≤ count1322 b))) else (if i < 1330 then (if i < 1329 then decide (7 ≤ count1322 b) else decide (8 ≤ count1322 b)) else (if i < 1331 then decide (9 ≤ count1322 b) else decide (10 ≤ count1322 b)))))) else (if i < 1345 then (if i < 1338 then (if i < 1335 then (if i < 1333 then decide (11 ≤ count1322 b) else (if i < 1334 then decide (12 ≤ count1322 b) else decide (13 ≤ count1322 b))) else (if i < 1336 then decide (14 ≤ count1322 b) else (if i < 1337 then decide (15 ≤ count1322 b) else decide (16 ≤ count1322 b)))) else (if i < 1341 then (if i < 1339 then decide (17 ≤ count1322 b) else (if i < 1340 then decide (18 ≤ count1322 b) else decide (19 ≤ count1322 b))) else (if i < 1343 then (if i < 1342 then decide (20 ≤ count1322 b) else decide (21 ≤ count1322 b)) else (if i < 1344 then decide (22 ≤ count1322 b) else decide (23 ≤ count1322 b))))) else (if i < 1351 then (if i < 1348 then (if i < 1346 then decide (24 ≤ count1322 b) else (if i < 1347 then decide (25 ≤ count1322 b) else decide (26 ≤ count1322 b))) else (if i < 1349 then decide (27 ≤ count1322 b) else (if i < 1350 then decide (28 ≤ count1322 b) else decide (29 ≤ count1322 b)))) else (if i < 1354 then (if i < 1352 then decide (1 ≤ count1351 b) else (if i < 1353 then decide (2 ≤ count1351 b) else decide (3 ≤ count1351 b))) else (if i < 1356 then (if i < 1355 then decide (4 ≤ count1351 b) else decide (5 ≤ count1351 b)) else (if i < 1357 then decide (6 ≤ count1351 b) else decide (7 ≤ count1351 b)))))))) else (if i < 1410 then (if i < 1384 then (if i < 1371 then (if i < 1364 then (if i < 1361 then (if i < 1359 then decide (8 ≤ count1351 b) else (if i < 1360 then decide (9 ≤ count1351 b) else decide (10 ≤ count1351 b))) else (if i < 1362 then decide (11 ≤ count1351 b) else (if i < 1363 then decide (12 ≤ count1351 b) else decide (13 ≤ count1351 b)))) else (if i < 1367 then (if i < 1365 then decide (14 ≤ count1351 b) else (if i < 1366 then decide (15 ≤ count1351 b) else decide (16 ≤ count1351 b))) else (if i < 1369 then (if i < 1368 then decide (17 ≤ count1351 b) else decide (18 ≤ count1351 b)) else (if i < 1370 then decide (19 ≤ count1351 b) else decide (20 ≤ count1351 b))))) else (if i < 1377 then (if i < 1374 then (if i < 1372 then decide (21 ≤ count1351 b) else (if i < 1373 then decide (22 ≤ count1351 b) else decide (23 ≤ count1351 b))) else (if i < 1375 then decide (24 ≤ count1351 b) else (if i < 1376 then decide (25 ≤ count1351 b) else decide (26 ≤ count1351 b)))) else (if i < 1380 then (if i < 1378 then decide (27 ≤ count1351 b) else (if i < 1379 then decide (28 ≤ count1351 b) else decide (29 ≤ count1351 b))) else (if i < 1382 then (if i < 1381 then decide (30 ≤ count1351 b) else decide (31 ≤ count1351 b)) else (if i < 1383 then decide (32 ≤ count1351 b) else decide (33 ≤ count1351 b)))))) else (if i < 1397 then (if i < 1390 then (if i < 1387 then (if i < 1385 then decide (34 ≤ count1351 b) else (if i < 1386 then decide (35 ≤ count1351 b) else decide (36 ≤ count1351 b))) else (if i < 1388 then decide (37 ≤ count1351 b) else (if i < 1389 then decide (38 ≤ count1351 b) else decide (39 ≤ count1351 b)))) else (if i < 1393 then (if i < 1391 then decide (40 ≤ count1351 b) else (if i < 1392 then decide (41 ≤ count1351 b) else decide (42 ≤ count1351 b))) else (if i < 1395 then (if i < 1394 then decide (1 ≤ count1393 b) else decide (2 ≤ count1393 b)) else (if i < 1396 then decide (1 ≤ count1395 b) else decide (2 ≤ count1395 b))))) else (if i < 1403 then (if i < 1400 then (if i < 1398 then decide (3 ≤ count1395 b) else (if i < 1399 then decide (1 ≤ count1398 b) else decide (2 ≤ count1398 b))) else (if i < 1401 then decide (1 ≤ count1400 b) else (if i < 1402 then decide (2 ≤ count1400 b) else decide (1 ≤ count1402 b)))) else (if i < 1406 then (if i < 1404 then decide (2 ≤ count1402 b) else (if i < 1405 then decide (3 ≤ count1402 b) else decide (4 ≤ count1402 b))) else (if i < 1408 then (if i < 1407 then decide (1 ≤ count1406 b) else decide (2 ≤ count1406 b)) else (if i < 1409 then decide (3 ≤ count1406 b) else decide (4 ≤ count1406 b))))))) else (if i < 1436 then (if i < 1423 then (if i < 1416 then (if i < 1413 then (if i < 1411 then decide (5 ≤ count1406 b) else (if i < 1412 then decide (6 ≤ count1406 b) else decide (7 ≤ count1406 b))) else (if i < 1414 then decide (1 ≤ count1413 b) else (if i < 1415 then decide (2 ≤ count1413 b) else decide (1 ≤ count1415 b)))) else (if i < 1419 then (if i < 1417 then decide (2 ≤ count1415 b) else (if i < 1418 then decide (3 ≤ count1415 b) else decide (1 ≤ count1418 b))) else (if i < 1421 then (if i < 1420 then decide (2 ≤ count1418 b) else decide (1 ≤ count1420 b)) else (if i < 1422 then decide (2 ≤ count1420 b) else decide (1 ≤ count1422 b))))) else (if i < 1429 then (if i < 1426 then (if i < 1424 then decide (2 ≤ count1422 b) else (if i < 1425 then decide (3 ≤ count1422 b) else decide (4 ≤ count1422 b))) else (if i < 1427 then decide (1 ≤ count1426 b) else (if i < 1428 then decide (2 ≤ count1426 b) else decide (3 ≤ count1426 b)))) else (if i < 1432 then (if i < 1430 then decide (4 ≤ count1426 b) else (if i < 1431 then decide (5 ≤ count1426 b) else decide (6 ≤ count1426 b))) else (if i < 1434 then (if i < 1433 then decide (7 ≤ count1426 b) else decide (1 ≤ count1433 b)) else (if i < 1435 then decide (2 ≤ count1433 b) else decide (3 ≤ count1433 b)))))) else (if i < 1449 then (if i < 1442 then (if i < 1439 then (if i < 1437 then decide (4 ≤ count1433 b) else (if i < 1438 then decide (5 ≤ count1433 b) else decide (6 ≤ count1433 b))) else (if i < 1440 then decide (7 ≤ count1433 b) else (if i < 1441 then decide (8 ≤ count1433 b) else decide (9 ≤ count1433 b)))) else (if i < 1445 then (if i < 1443 then decide (10 ≤ count1433 b) else (if i < 1444 then decide (11 ≤ count1433 b) else decide (12 ≤ count1433 b))) else (if i < 1447 then (if i < 1446 then decide (13 ≤ count1433 b) else decide (14 ≤ count1433 b)) else (if i < 1448 then decide (1 ≤ count1447 b) else decide (2 ≤ count1447 b))))) else (if i < 1456 then (if i < 1452 then (if i < 1450 then decide (1 ≤ count1449 b) else (if i < 1451 then decide (2 ≤ count1449 b) else decide (3 ≤ count1449 b))) else (if i < 1454 then (if i < 1453 then decide (1 ≤ count1452 b) else decide (2 ≤ count1452 b)) else (if i < 1455 then decide (1 ≤ count1454 b) else decide (2 ≤ count1454 b)))) else (if i < 1459 then (if i < 1457 then decide (1 ≤ count1456 b) else (if i < 1458 then decide (2 ≤ count1456 b) else decide (3 ≤ count1456 b))) else (if i < 1461 then (if i < 1460 then decide (4 ≤ count1456 b) else decide (1 ≤ count1460 b)) else (if i < 1462 then decide (2 ≤ count1460 b) else decide (3 ≤ count1460 b))))))))) else (if i < 1568 then (if i < 1515 then (if i < 1489 then (if i < 1476 then (if i < 1469 then (if i < 1466 then (if i < 1464 then decide (4 ≤ count1460 b) else (if i < 1465 then decide (5 ≤ count1460 b) else decide (6 ≤ count1460 b))) else (if i < 1467 then decide (7 ≤ count1460 b) else (if i < 1468 then decide (1 ≤ count1467 b) else decide (2 ≤ count1467 b)))) else (if i < 1472 then (if i < 1470 then decide (1 ≤ count1469 b) else (if i < 1471 then decide (2 ≤ count1469 b) else decide (1 ≤ count1471 b))) else (if i < 1474 then (if i < 1473 then decide (2 ≤ count1471 b) else decide (3 ≤ count1471 b)) else (if i < 1475 then decide (4 ≤ count1471 b) else decide (1 ≤ count1475 b))))) else (if i < 1482 then (if i < 1479 then (if i < 1477 then decide (2 ≤ count1475 b) else (if i < 1478 then decide (1 ≤ count1477 b) else decide (2 ≤ count1477 b))) else (if i < 1480 then decide (1 ≤ count1479 b) else (if i < 1481 then decide (2 ≤ count1479 b) else decide (3 ≤ count1479 b)))) else (if i < 1485 then (if i < 1483 then decide (4 ≤ count1479 b) else (if i < 1484 then decide (1 ≤ count1483 b) else decide (2 ≤ count1483 b))) else (if i < 1487 then (if i < 1486 then decide (3 ≤ count1483 b) else decide (4 ≤ count1483 b)) else (if i < 1488 then decide (5 ≤ count1483 b) else decide (6 ≤ count1483 b)))))) else (if i < 1502 then (if i < 1495 then (if i < 1492 then (if i < 1490 then decide (7 ≤ count1483 b) else (if i < 1491 then decide (8 ≤ count1483 b) else decide (1 ≤ count1491 b))) else (if i < 1493 then decide (2 ≤ count1491 b) else (if i < 1494 then decide (3 ≤ count1491 b) else decide (4 ≤ count1491 b)))) else (if i < 1498 then (if i < 1496 then decide (5 ≤ count1491 b) else (if i < 1497 then decide (6 ≤ count1491 b) else decide (7 ≤ count1491 b))) else (if i < 1500 then (if i < 1499 then decide (8 ≤ count1491 b) else decide (9 ≤ count1491 b)) else (if i < 1501 then decide (10 ≤ count1491 b) else decide (11 ≤ count1491 b))))) else (if i < 1508 then (if i < 1505 then (if i < 1503 then decide (12 ≤ count1491 b) else (if i < 1504 then decide (13 ≤ count1491 b) else decide (14 ≤ count1491 b))) else (if i < 1506 then decide (15 ≤ count1491 b) else (if i < 1507 then decide (1 ≤ count1506 b) else decide (2 ≤ count1506 b)))) else (if i < 1511 then (if i < 1509 then decide (3 ≤ count1506 b) else (if i < 1510 then decide (4 ≤ count1506 b) else decide (5 ≤ count1506 b))) else (if i < 1513 then (if i < 1512 then decide (6 ≤ count1506 b) else decide (7 ≤ count1506 b)) else (if i < 1514 then decide (8 ≤ count1506 b) else decide (9 ≤ count1506 b))))))) else (if i < 1541 then (if i < 1528 then (if i < 1521 then (if i < 1518 then (if i < 1516 then decide (10 ≤ count1506 b) else (if i < 1517 then decide (11 ≤ count1506 b) else decide (12 ≤ count1506 b))) else (if i < 1519 then decide (13 ≤ count1506 b) else (if i < 1520 then decide (14 ≤ count1506 b) else decide (15 ≤ count1506 b)))) else (if i < 1524 then (if i < 1522 then decide (16 ≤ count1506 b) else (if i < 1523 then decide (17 ≤ count1506 b) else decide (18 ≤ count1506 b))) else (if i < 1526 then (if i < 1525 then decide (1 ≤ count1524 b) else decide (2 ≤ count1524 b)) else (if i < 1527 then decide (1 ≤ count1526 b) else decide (2 ≤ count1526 b))))) else (if i < 1534 then (if i < 1531 then (if i < 1529 then decide (3 ≤ count1526 b) else (if i < 1530 then decide (1 ≤ count1529 b) else decide (2 ≤ count1529 b))) else (if i < 1532 then decide (1 ≤ count1531 b) else (if i < 1533 then decide (2 ≤ count1531 b) else decide (1 ≤ count1533 b)))) else (if i < 1537 then (if i < 1535 then decide (2 ≤ count1533 b) else (if i < 1536 then decide (3 ≤ count1533 b) else decide (4 ≤ count1533 b))) else (if i < 1539 then (if i < 1538 then decide (1 ≤ count1537 b) else decide (2 ≤ count1537 b)) else (if i < 1540 then decide (3 ≤ count1537 b) else decide (4 ≤ count1537 b)))))) else (if i < 1554 then (if i < 1547 then (if i < 1544 then (if i < 1542 then decide (5 ≤ count1537 b) else (if i < 1543 then decide (6 ≤ count1537 b) else decide (7 ≤ count1537 b))) else (if i < 1545 then decide (1 ≤ count1544 b) else (if i < 1546 then decide (2 ≤ count1544 b) else decide (1 ≤ count1546 b)))) else (if i < 1550 then (if i < 1548 then decide (2 ≤ count1546 b) else (if i < 1549 then decide (3 ≤ count1546 b) else decide (1 ≤ count1549 b))) else (if i < 1552 then (if i < 1551 then decide (2 ≤ count1549 b) else decide (1 ≤ count1551 b)) else (if i < 1553 then decide (2 ≤ count1551 b) else decide (1 ≤ count1553 b))))) else (if i < 1561 then (if i < 1557 then (if i < 1555 then decide (2 ≤ count1553 b) else (if i < 1556 then decide (3 ≤ count1553 b) else decide (4 ≤ count1553 b))) else (if i < 1559 then (if i < 1558 then decide (1 ≤ count1557 b) else decide (2 ≤ count1557 b)) else (if i < 1560 then decide (3 ≤ count1557 b) else decide (4 ≤ count1557 b)))) else (if i < 1564 then (if i < 1562 then decide (5 ≤ count1557 b) else (if i < 1563 then decide (6 ≤ count1557 b) else decide (7 ≤ count1557 b))) else (if i < 1566 then (if i < 1565 then decide (1 ≤ count1564 b) else decide (2 ≤ count1564 b)) else (if i < 1567 then decide (3 ≤ count1564 b) else decide (4 ≤ count1564 b)))))))) else (if i < 1620 then (if i < 1594 then (if i < 1581 then (if i < 1574 then (if i < 1571 then (if i < 1569 then decide (5 ≤ count1564 b) else (if i < 1570 then decide (6 ≤ count1564 b) else decide (7 ≤ count1564 b))) else (if i < 1572 then decide (8 ≤ count1564 b) else (if i < 1573 then decide (9 ≤ count1564 b) else decide (10 ≤ count1564 b)))) else (if i < 1577 then (if i < 1575 then decide (11 ≤ count1564 b) else (if i < 1576 then decide (12 ≤ count1564 b) else decide (13 ≤ count1564 b))) else (if i < 1579 then (if i < 1578 then decide (14 ≤ count1564 b) else decide (1 ≤ count1578 b)) else (if i < 1580 then decide (2 ≤ count1578 b) else decide (1 ≤ count1580 b))))) else (if i < 1587 then (if i < 1584 then (if i < 1582 then decide (2 ≤ count1580 b) else (if i < 1583 then decide (3 ≤ count1580 b) else decide (1 ≤ count1583 b))) else (if i < 1585 then decide (2 ≤ count1583 b) else (if i < 1586 then decide (1 ≤ count1585 b) else decide (2 ≤ count1585 b)))) else (if i < 1590 then (if i < 1588 then decide (1 ≤ count1587 b) else (if i < 1589 then decide (2 ≤ count1587 b) else decide (3 ≤ count1587 b))) else (if i < 1592 then (if i < 1591 then decide (4 ≤ count1587 b) else decide (1 ≤ count1591 b)) else (if i < 1593 then decide (2 ≤ count1591 b) else decide (3 ≤ count1591 b)))))) else (if i < 1607 then (if i < 1600 then (if i < 1597 then (if i < 1595 then decide (4 ≤ count1591 b) else (if i < 1596 then decide (5 ≤ count1591 b) else decide (6 ≤ count1591 b))) else (if i < 1598 then decide (7 ≤ count1591 b) else (if i < 1599 then decide (1 ≤ count1598 b) else decide (2 ≤ count1598 b)))) else (if i < 1603 then (if i < 1601 then decide (1 ≤ count1600 b) else (if i < 1602 then decide (2 ≤ count1600 b) else decide (1 ≤ count1602 b))) else (if i < 1605 then (if i < 1604 then decide (2 ≤ count1602 b) else decide (3 ≤ count1602 b)) else (if i < 1606 then decide (4 ≤ count1602 b) else decide (1 ≤ count1606 b))))) else (if i < 1613 then (if i < 1610 then (if i < 1608 then decide (2 ≤ count1606 b) else (if i < 1609 then decide (1 ≤ count1608 b) else decide (2 ≤ count1608 b))) else (if i < 1611 then decide (1 ≤ count1610 b) else (if i < 1612 then decide (2 ≤ count1610 b) else decide (3 ≤ count1610 b)))) else (if i < 1616 then (if i < 1614 then decide (4 ≤ count1610 b) else (if i < 1615 then decide (1 ≤ count1614 b) else decide (2 ≤ count1614 b))) else (if i < 1618 then (if i < 1617 then decide (3 ≤ count1614 b) else decide (4 ≤ count1614 b)) else (if i < 1619 then decide (5 ≤ count1614 b) else decide (6 ≤ count1614 b))))))) else (if i < 1646 then (if i < 1633 then (if i < 1626 then (if i < 1623 then (if i < 1621 then decide (7 ≤ count1614 b) else (if i < 1622 then decide (8 ≤ count1614 b) else decide (1 ≤ count1622 b))) else (if i < 1624 then decide (2 ≤ count1622 b) else (if i < 1625 then decide (3 ≤ count1622 b) else decide (4 ≤ count1622 b)))) else (if i < 1629 then (if i < 1627 then decide (5 ≤ count1622 b) else (if i < 1628 then decide (6 ≤ count1622 b) else decide (7 ≤ count1622 b))) else (if i < 1631 then (if i < 1630 then decide (8 ≤ count1622 b) else decide (9 ≤ count1622 b)) else (if i < 1632 then decide (10 ≤ count1622 b) else decide (11 ≤ count1622 b))))) else (if i < 1639 then (if i < 1636 then (if i < 1634 then decide (12 ≤ count1622 b) else (if i < 1635 then decide (13 ≤ count1622 b) else decide (14 ≤ count1622 b))) else (if i < 1637 then decide (15 ≤ count1622 b) else (if i < 1638 then decide (1 ≤ count1637 b) else decide (2 ≤ count1637 b)))) else (if i < 1642 then (if i < 1640 then decide (3 ≤ count1637 b) else (if i < 1641 then decide (4 ≤ count1637 b) else decide (5 ≤ count1637 b))) else (if i < 1644 then (if i < 1643 then decide (6 ≤ count1637 b) else decide (7 ≤ count1637 b)) else (if i < 1645 then decide (8 ≤ count1637 b) else decide (9 ≤ count1637 b)))))) else (if i < 1659 then (if i < 1652 then (if i < 1649 then (if i < 1647 then decide (10 ≤ count1637 b) else (if i < 1648 then decide (11 ≤ count1637 b) else decide (12 ≤ count1637 b))) else (if i < 1650 then decide (13 ≤ count1637 b) else (if i < 1651 then decide (14 ≤ count1637 b) else decide (15 ≤ count1637 b)))) else (if i < 1655 then (if i < 1653 then decide (16 ≤ count1637 b) else (if i < 1654 then decide (17 ≤ count1637 b) else decide (18 ≤ count1637 b))) else (if i < 1657 then (if i < 1656 then decide (1 ≤ count1655 b) else decide (2 ≤ count1655 b)) else (if i < 1658 then decide (3 ≤ count1655 b) else decide (4 ≤ count1655 b))))) else (if i < 1666 then (if i < 1662 then (if i < 1660 then decide (5 ≤ count1655 b) else (if i < 1661 then decide (6 ≤ count1655 b) else decide (7 ≤ count1655 b))) else (if i < 1664 then (if i < 1663 then decide (8 ≤ count1655 b) else decide (9 ≤ count1655 b)) else (if i < 1665 then decide (10 ≤ count1655 b) else decide (11 ≤ count1655 b)))) else (if i < 1669 then (if i < 1667 then decide (12 ≤ count1655 b) else (if i < 1668 then decide (13 ≤ count1655 b) else decide (14 ≤ count1655 b))) else (if i < 1671 then (if i < 1670 then decide (15 ≤ count1655 b) else decide (16 ≤ count1655 b)) else (if i < 1672 then decide (17 ≤ count1655 b) else decide (18 ≤ count1655 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (3 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (4 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (7 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (8 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (9 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (10 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (13 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (14 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (17 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (18 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (21 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (22 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (24 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (27 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (28 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (30 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (31 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (33 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (35 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (36 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (38 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (40 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (42 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (45 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (47 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (48 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (49 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (50 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (53 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (55 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (57 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (59 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (60 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (62 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (75 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (79 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (80 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (83 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (84 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (87 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (89 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (93 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (105 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (107 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (108 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (110 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (113 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (115 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (116 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (118 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (125 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (127 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (128 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (129 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (131 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (132 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (133 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (134 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (136 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (137 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (139 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (141 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (142 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (146 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (147 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (148 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (149 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (150 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (152 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (155 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (157 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (158 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (159 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (160 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (161 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (162 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (163 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (164 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (167 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (168 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (170 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (171 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (172 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (175 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (176 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (177 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (178 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (180 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (181 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (183 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (185 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (186 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (189 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (190 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (199 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (207 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (208 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (209 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (214 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (215 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (217 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (224 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (225 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (227 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (230 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (233 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (235 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (237 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (238 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (242 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (243 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (245 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (246 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (251 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (255 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (3 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (4 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (7 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (9 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (21 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (24 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (31 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (33 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (35 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (36 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (38 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (40 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (42 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (45 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (47 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (48 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (50 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (53 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (55 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (57 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (59 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (60 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (62 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (75 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (83 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (89 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (93 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (105 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (107 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (110 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (113 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (116 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (127 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (128 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (129 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (141 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (146 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (147 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (150 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (157 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (164 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (170 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (172 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (176 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (180 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (183 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (185 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (208 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (209 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (215 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (224 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (225 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (237 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (2 ≤ count237 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (2 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (2 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (2 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value268 (q : Snake 81) : valuation q 268 = decide (2 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value274 (q : Snake 81) : valuation q 274 = decide (2 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value284 (q : Snake 81) : valuation q 284 = decide (2 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value286 (q : Snake 81) : valuation q 286 = decide (2 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value298 (q : Snake 81) : valuation q 298 = decide (2 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value366 (q : Snake 81) : valuation q 366 = decide (2 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value370 (q : Snake 81) : valuation q 370 = decide (2 ≤ count369 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value398 (q : Snake 81) : valuation q 398 = decide (2 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value456 (q : Snake 81) : valuation q 456 = decide (2 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value458 (q : Snake 81) : valuation q 458 = decide (2 ≤ count457 (baseVal q)) := rfl
theorem value460 (q : Snake 81) : valuation q 460 = decide (2 ≤ count459 (baseVal q)) := rfl
theorem value787 (q : Snake 81) : valuation q 787 = decide (1 ≤ count787 (baseVal q)) := rfl
theorem value788 (q : Snake 81) : valuation q 788 = decide (2 ≤ count787 (baseVal q)) := rfl
theorem value789 (q : Snake 81) : valuation q 789 = decide (1 ≤ count789 (baseVal q)) := rfl
theorem value790 (q : Snake 81) : valuation q 790 = decide (2 ≤ count789 (baseVal q)) := rfl
theorem value791 (q : Snake 81) : valuation q 791 = decide (3 ≤ count789 (baseVal q)) := rfl
theorem value792 (q : Snake 81) : valuation q 792 = decide (1 ≤ count792 (baseVal q)) := rfl
theorem value793 (q : Snake 81) : valuation q 793 = decide (2 ≤ count792 (baseVal q)) := rfl
theorem value794 (q : Snake 81) : valuation q 794 = decide (1 ≤ count794 (baseVal q)) := rfl
theorem value795 (q : Snake 81) : valuation q 795 = decide (2 ≤ count794 (baseVal q)) := rfl
theorem value796 (q : Snake 81) : valuation q 796 = decide (1 ≤ count796 (baseVal q)) := rfl
theorem value797 (q : Snake 81) : valuation q 797 = decide (2 ≤ count796 (baseVal q)) := rfl
theorem value798 (q : Snake 81) : valuation q 798 = decide (3 ≤ count796 (baseVal q)) := rfl
theorem value799 (q : Snake 81) : valuation q 799 = decide (4 ≤ count796 (baseVal q)) := rfl
theorem value800 (q : Snake 81) : valuation q 800 = decide (1 ≤ count800 (baseVal q)) := rfl
theorem value801 (q : Snake 81) : valuation q 801 = decide (2 ≤ count800 (baseVal q)) := rfl
theorem value802 (q : Snake 81) : valuation q 802 = decide (3 ≤ count800 (baseVal q)) := rfl
theorem value803 (q : Snake 81) : valuation q 803 = decide (4 ≤ count800 (baseVal q)) := rfl
theorem value804 (q : Snake 81) : valuation q 804 = decide (5 ≤ count800 (baseVal q)) := rfl
theorem value805 (q : Snake 81) : valuation q 805 = decide (6 ≤ count800 (baseVal q)) := rfl
theorem value807 (q : Snake 81) : valuation q 807 = decide (1 ≤ count807 (baseVal q)) := rfl
theorem value808 (q : Snake 81) : valuation q 808 = decide (2 ≤ count807 (baseVal q)) := rfl
theorem value809 (q : Snake 81) : valuation q 809 = decide (1 ≤ count809 (baseVal q)) := rfl
theorem value810 (q : Snake 81) : valuation q 810 = decide (2 ≤ count809 (baseVal q)) := rfl
theorem value811 (q : Snake 81) : valuation q 811 = decide (3 ≤ count809 (baseVal q)) := rfl
theorem value812 (q : Snake 81) : valuation q 812 = decide (1 ≤ count812 (baseVal q)) := rfl
theorem value813 (q : Snake 81) : valuation q 813 = decide (2 ≤ count812 (baseVal q)) := rfl
theorem value814 (q : Snake 81) : valuation q 814 = decide (1 ≤ count814 (baseVal q)) := rfl
theorem value815 (q : Snake 81) : valuation q 815 = decide (2 ≤ count814 (baseVal q)) := rfl
theorem value816 (q : Snake 81) : valuation q 816 = decide (1 ≤ count816 (baseVal q)) := rfl
theorem value817 (q : Snake 81) : valuation q 817 = decide (2 ≤ count816 (baseVal q)) := rfl
theorem value818 (q : Snake 81) : valuation q 818 = decide (3 ≤ count816 (baseVal q)) := rfl
theorem value819 (q : Snake 81) : valuation q 819 = decide (4 ≤ count816 (baseVal q)) := rfl
theorem value820 (q : Snake 81) : valuation q 820 = decide (1 ≤ count820 (baseVal q)) := rfl
theorem value821 (q : Snake 81) : valuation q 821 = decide (2 ≤ count820 (baseVal q)) := rfl
theorem value822 (q : Snake 81) : valuation q 822 = decide (3 ≤ count820 (baseVal q)) := rfl
theorem value823 (q : Snake 81) : valuation q 823 = decide (4 ≤ count820 (baseVal q)) := rfl
theorem value824 (q : Snake 81) : valuation q 824 = decide (5 ≤ count820 (baseVal q)) := rfl
theorem value825 (q : Snake 81) : valuation q 825 = decide (6 ≤ count820 (baseVal q)) := rfl
theorem value827 (q : Snake 81) : valuation q 827 = decide (1 ≤ count827 (baseVal q)) := rfl
theorem value828 (q : Snake 81) : valuation q 828 = decide (2 ≤ count827 (baseVal q)) := rfl
theorem value829 (q : Snake 81) : valuation q 829 = decide (3 ≤ count827 (baseVal q)) := rfl
theorem value830 (q : Snake 81) : valuation q 830 = decide (4 ≤ count827 (baseVal q)) := rfl
theorem value831 (q : Snake 81) : valuation q 831 = decide (5 ≤ count827 (baseVal q)) := rfl
theorem value832 (q : Snake 81) : valuation q 832 = decide (6 ≤ count827 (baseVal q)) := rfl
theorem value833 (q : Snake 81) : valuation q 833 = decide (7 ≤ count827 (baseVal q)) := rfl
theorem value834 (q : Snake 81) : valuation q 834 = decide (8 ≤ count827 (baseVal q)) := rfl
theorem value835 (q : Snake 81) : valuation q 835 = decide (9 ≤ count827 (baseVal q)) := rfl
theorem value836 (q : Snake 81) : valuation q 836 = decide (10 ≤ count827 (baseVal q)) := rfl
theorem value837 (q : Snake 81) : valuation q 837 = decide (11 ≤ count827 (baseVal q)) := rfl
theorem value841 (q : Snake 81) : valuation q 841 = decide (1 ≤ count841 (baseVal q)) := rfl
theorem value842 (q : Snake 81) : valuation q 842 = decide (2 ≤ count841 (baseVal q)) := rfl
theorem value843 (q : Snake 81) : valuation q 843 = decide (1 ≤ count843 (baseVal q)) := rfl
theorem value844 (q : Snake 81) : valuation q 844 = decide (2 ≤ count843 (baseVal q)) := rfl
theorem value845 (q : Snake 81) : valuation q 845 = decide (3 ≤ count843 (baseVal q)) := rfl
theorem value846 (q : Snake 81) : valuation q 846 = decide (1 ≤ count846 (baseVal q)) := rfl
theorem value847 (q : Snake 81) : valuation q 847 = decide (2 ≤ count846 (baseVal q)) := rfl
theorem value848 (q : Snake 81) : valuation q 848 = decide (1 ≤ count848 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (1 ≤ count850 (baseVal q)) := rfl
theorem value851 (q : Snake 81) : valuation q 851 = decide (2 ≤ count850 (baseVal q)) := rfl
theorem value852 (q : Snake 81) : valuation q 852 = decide (3 ≤ count850 (baseVal q)) := rfl
theorem value854 (q : Snake 81) : valuation q 854 = decide (1 ≤ count854 (baseVal q)) := rfl
theorem value855 (q : Snake 81) : valuation q 855 = decide (2 ≤ count854 (baseVal q)) := rfl
theorem value856 (q : Snake 81) : valuation q 856 = decide (3 ≤ count854 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (4 ≤ count854 (baseVal q)) := rfl
theorem value861 (q : Snake 81) : valuation q 861 = decide (1 ≤ count861 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (1 ≤ count863 (baseVal q)) := rfl
theorem value864 (q : Snake 81) : valuation q 864 = decide (2 ≤ count863 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (1 ≤ count865 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (2 ≤ count865 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (1 ≤ count869 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (2 ≤ count869 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (1 ≤ count871 (baseVal q)) := rfl
theorem value872 (q : Snake 81) : valuation q 872 = decide (2 ≤ count871 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (1 ≤ count873 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (2 ≤ count873 (baseVal q)) := rfl
theorem value875 (q : Snake 81) : valuation q 875 = decide (3 ≤ count873 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (4 ≤ count873 (baseVal q)) := rfl
theorem value877 (q : Snake 81) : valuation q 877 = decide (1 ≤ count877 (baseVal q)) := rfl
theorem value878 (q : Snake 81) : valuation q 878 = decide (2 ≤ count877 (baseVal q)) := rfl
theorem value879 (q : Snake 81) : valuation q 879 = decide (3 ≤ count877 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (4 ≤ count877 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (5 ≤ count877 (baseVal q)) := rfl
theorem value885 (q : Snake 81) : valuation q 885 = decide (1 ≤ count885 (baseVal q)) := rfl
theorem value886 (q : Snake 81) : valuation q 886 = decide (2 ≤ count885 (baseVal q)) := rfl
theorem value887 (q : Snake 81) : valuation q 887 = decide (3 ≤ count885 (baseVal q)) := rfl
theorem value888 (q : Snake 81) : valuation q 888 = decide (4 ≤ count885 (baseVal q)) := rfl
theorem value889 (q : Snake 81) : valuation q 889 = decide (5 ≤ count885 (baseVal q)) := rfl
theorem value890 (q : Snake 81) : valuation q 890 = decide (6 ≤ count885 (baseVal q)) := rfl
theorem value891 (q : Snake 81) : valuation q 891 = decide (7 ≤ count885 (baseVal q)) := rfl
theorem value903 (q : Snake 81) : valuation q 903 = decide (4 ≤ count900 (baseVal q)) := rfl
theorem value904 (q : Snake 81) : valuation q 904 = decide (5 ≤ count900 (baseVal q)) := rfl
theorem value905 (q : Snake 81) : valuation q 905 = decide (6 ≤ count900 (baseVal q)) := rfl
theorem value906 (q : Snake 81) : valuation q 906 = decide (7 ≤ count900 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (8 ≤ count900 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (9 ≤ count900 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (10 ≤ count900 (baseVal q)) := rfl
theorem value910 (q : Snake 81) : valuation q 910 = decide (11 ≤ count900 (baseVal q)) := rfl
theorem value911 (q : Snake 81) : valuation q 911 = decide (12 ≤ count900 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (13 ≤ count900 (baseVal q)) := rfl
theorem value918 (q : Snake 81) : valuation q 918 = decide (1 ≤ count918 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (2 ≤ count918 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (1 ≤ count920 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (2 ≤ count920 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (3 ≤ count920 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (1 ≤ count923 (baseVal q)) := rfl
theorem value924 (q : Snake 81) : valuation q 924 = decide (2 ≤ count923 (baseVal q)) := rfl
theorem value925 (q : Snake 81) : valuation q 925 = decide (1 ≤ count925 (baseVal q)) := rfl
theorem value926 (q : Snake 81) : valuation q 926 = decide (2 ≤ count925 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (1 ≤ count927 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (2 ≤ count927 (baseVal q)) := rfl
theorem value929 (q : Snake 81) : valuation q 929 = decide (3 ≤ count927 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (4 ≤ count927 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (1 ≤ count931 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (2 ≤ count931 (baseVal q)) := rfl
theorem value933 (q : Snake 81) : valuation q 933 = decide (3 ≤ count931 (baseVal q)) := rfl
theorem value934 (q : Snake 81) : valuation q 934 = decide (4 ≤ count931 (baseVal q)) := rfl
theorem value935 (q : Snake 81) : valuation q 935 = decide (5 ≤ count931 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (1 ≤ count938 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (2 ≤ count938 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (1 ≤ count940 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (2 ≤ count940 (baseVal q)) := rfl
theorem value942 (q : Snake 81) : valuation q 942 = decide (3 ≤ count940 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (1 ≤ count943 (baseVal q)) := rfl
theorem value944 (q : Snake 81) : valuation q 944 = decide (2 ≤ count943 (baseVal q)) := rfl
theorem value945 (q : Snake 81) : valuation q 945 = decide (1 ≤ count945 (baseVal q)) := rfl
theorem value946 (q : Snake 81) : valuation q 946 = decide (2 ≤ count945 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (1 ≤ count947 (baseVal q)) := rfl
theorem value948 (q : Snake 81) : valuation q 948 = decide (2 ≤ count947 (baseVal q)) := rfl
theorem value949 (q : Snake 81) : valuation q 949 = decide (3 ≤ count947 (baseVal q)) := rfl
theorem value950 (q : Snake 81) : valuation q 950 = decide (4 ≤ count947 (baseVal q)) := rfl
theorem value951 (q : Snake 81) : valuation q 951 = decide (1 ≤ count951 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (2 ≤ count951 (baseVal q)) := rfl
theorem value953 (q : Snake 81) : valuation q 953 = decide (3 ≤ count951 (baseVal q)) := rfl
theorem value954 (q : Snake 81) : valuation q 954 = decide (4 ≤ count951 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (5 ≤ count951 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (6 ≤ count951 (baseVal q)) := rfl
theorem value957 (q : Snake 81) : valuation q 957 = decide (7 ≤ count951 (baseVal q)) := rfl
theorem value959 (q : Snake 81) : valuation q 959 = decide (2 ≤ count958 (baseVal q)) := rfl
theorem value960 (q : Snake 81) : valuation q 960 = decide (3 ≤ count958 (baseVal q)) := rfl
theorem value961 (q : Snake 81) : valuation q 961 = decide (4 ≤ count958 (baseVal q)) := rfl
theorem value962 (q : Snake 81) : valuation q 962 = decide (5 ≤ count958 (baseVal q)) := rfl
theorem value963 (q : Snake 81) : valuation q 963 = decide (6 ≤ count958 (baseVal q)) := rfl
theorem value964 (q : Snake 81) : valuation q 964 = decide (7 ≤ count958 (baseVal q)) := rfl
theorem value965 (q : Snake 81) : valuation q 965 = decide (8 ≤ count958 (baseVal q)) := rfl
theorem value966 (q : Snake 81) : valuation q 966 = decide (9 ≤ count958 (baseVal q)) := rfl
theorem value967 (q : Snake 81) : valuation q 967 = decide (10 ≤ count958 (baseVal q)) := rfl
theorem value972 (q : Snake 81) : valuation q 972 = decide (1 ≤ count972 (baseVal q)) := rfl
theorem value973 (q : Snake 81) : valuation q 973 = decide (2 ≤ count972 (baseVal q)) := rfl
theorem value974 (q : Snake 81) : valuation q 974 = decide (1 ≤ count974 (baseVal q)) := rfl
theorem value975 (q : Snake 81) : valuation q 975 = decide (2 ≤ count974 (baseVal q)) := rfl
theorem value976 (q : Snake 81) : valuation q 976 = decide (3 ≤ count974 (baseVal q)) := rfl
theorem value977 (q : Snake 81) : valuation q 977 = decide (1 ≤ count977 (baseVal q)) := rfl
theorem value979 (q : Snake 81) : valuation q 979 = decide (1 ≤ count979 (baseVal q)) := rfl
theorem value981 (q : Snake 81) : valuation q 981 = decide (1 ≤ count981 (baseVal q)) := rfl
theorem value982 (q : Snake 81) : valuation q 982 = decide (2 ≤ count981 (baseVal q)) := rfl
theorem value985 (q : Snake 81) : valuation q 985 = decide (1 ≤ count985 (baseVal q)) := rfl
theorem value986 (q : Snake 81) : valuation q 986 = decide (2 ≤ count985 (baseVal q)) := rfl
theorem value987 (q : Snake 81) : valuation q 987 = decide (3 ≤ count985 (baseVal q)) := rfl
theorem value988 (q : Snake 81) : valuation q 988 = decide (4 ≤ count985 (baseVal q)) := rfl
theorem value992 (q : Snake 81) : valuation q 992 = decide (1 ≤ count992 (baseVal q)) := rfl
theorem value993 (q : Snake 81) : valuation q 993 = decide (2 ≤ count992 (baseVal q)) := rfl
theorem value994 (q : Snake 81) : valuation q 994 = decide (1 ≤ count994 (baseVal q)) := rfl
theorem value996 (q : Snake 81) : valuation q 996 = decide (1 ≤ count996 (baseVal q)) := rfl
theorem value997 (q : Snake 81) : valuation q 997 = decide (2 ≤ count996 (baseVal q)) := rfl
theorem value998 (q : Snake 81) : valuation q 998 = decide (3 ≤ count996 (baseVal q)) := rfl
theorem value1000 (q : Snake 81) : valuation q 1000 = decide (1 ≤ count1000 (baseVal q)) := rfl
theorem value1001 (q : Snake 81) : valuation q 1001 = decide (2 ≤ count1000 (baseVal q)) := rfl
theorem value1002 (q : Snake 81) : valuation q 1002 = decide (1 ≤ count1002 (baseVal q)) := rfl
theorem value1004 (q : Snake 81) : valuation q 1004 = decide (1 ≤ count1004 (baseVal q)) := rfl
theorem value1005 (q : Snake 81) : valuation q 1005 = decide (2 ≤ count1004 (baseVal q)) := rfl
theorem value1006 (q : Snake 81) : valuation q 1006 = decide (3 ≤ count1004 (baseVal q)) := rfl
theorem value1009 (q : Snake 81) : valuation q 1009 = decide (2 ≤ count1008 (baseVal q)) := rfl
theorem value1010 (q : Snake 81) : valuation q 1010 = decide (3 ≤ count1008 (baseVal q)) := rfl
theorem value1011 (q : Snake 81) : valuation q 1011 = decide (4 ≤ count1008 (baseVal q)) := rfl
theorem value1012 (q : Snake 81) : valuation q 1012 = decide (5 ≤ count1008 (baseVal q)) := rfl
theorem value1017 (q : Snake 81) : valuation q 1017 = decide (2 ≤ count1016 (baseVal q)) := rfl
theorem value1018 (q : Snake 81) : valuation q 1018 = decide (3 ≤ count1016 (baseVal q)) := rfl
theorem value1019 (q : Snake 81) : valuation q 1019 = decide (4 ≤ count1016 (baseVal q)) := rfl
theorem value1020 (q : Snake 81) : valuation q 1020 = decide (5 ≤ count1016 (baseVal q)) := rfl
theorem value1021 (q : Snake 81) : valuation q 1021 = decide (6 ≤ count1016 (baseVal q)) := rfl
theorem value1022 (q : Snake 81) : valuation q 1022 = decide (7 ≤ count1016 (baseVal q)) := rfl
theorem value1035 (q : Snake 81) : valuation q 1035 = decide (5 ≤ count1031 (baseVal q)) := rfl
theorem value1036 (q : Snake 81) : valuation q 1036 = decide (6 ≤ count1031 (baseVal q)) := rfl
theorem value1037 (q : Snake 81) : valuation q 1037 = decide (7 ≤ count1031 (baseVal q)) := rfl
theorem value1038 (q : Snake 81) : valuation q 1038 = decide (8 ≤ count1031 (baseVal q)) := rfl
theorem value1039 (q : Snake 81) : valuation q 1039 = decide (9 ≤ count1031 (baseVal q)) := rfl
theorem value1040 (q : Snake 81) : valuation q 1040 = decide (10 ≤ count1031 (baseVal q)) := rfl
theorem value1041 (q : Snake 81) : valuation q 1041 = decide (11 ≤ count1031 (baseVal q)) := rfl
theorem value1042 (q : Snake 81) : valuation q 1042 = decide (12 ≤ count1031 (baseVal q)) := rfl
theorem value1043 (q : Snake 81) : valuation q 1043 = decide (13 ≤ count1031 (baseVal q)) := rfl
theorem value1044 (q : Snake 81) : valuation q 1044 = decide (14 ≤ count1031 (baseVal q)) := rfl
theorem value1066 (q : Snake 81) : valuation q 1066 = decide (18 ≤ count1049 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (1 ≤ count1393 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (2 ≤ count1393 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (1 ≤ count1395 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (2 ≤ count1395 (baseVal q)) := rfl
theorem value1397 (q : Snake 81) : valuation q 1397 = decide (3 ≤ count1395 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (1 ≤ count1398 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (2 ≤ count1398 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (1 ≤ count1400 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (2 ≤ count1400 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (1 ≤ count1402 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (2 ≤ count1402 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (3 ≤ count1402 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (1 ≤ count1406 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (2 ≤ count1406 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (3 ≤ count1406 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (4 ≤ count1406 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (1 ≤ count1413 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (1 ≤ count1415 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (2 ≤ count1415 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (1 ≤ count1418 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (2 ≤ count1418 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (1 ≤ count1420 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (2 ≤ count1420 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (1 ≤ count1422 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (2 ≤ count1422 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (3 ≤ count1422 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (1 ≤ count1426 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (2 ≤ count1426 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (3 ≤ count1426 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (4 ≤ count1426 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (3 ≤ count1433 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (4 ≤ count1433 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (1 ≤ count1447 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (2 ≤ count1447 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (1 ≤ count1449 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (2 ≤ count1449 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (1 ≤ count1456 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (1 ≤ count1460 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (2 ≤ count1460 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (3 ≤ count1460 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (1 ≤ count1477 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (2 ≤ count1477 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (1 ≤ count1479 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (2 ≤ count1479 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (1 ≤ count1483 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (2 ≤ count1483 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (1 ≤ count1491 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (3 ≤ count1491 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (4 ≤ count1491 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (4 ≤ count1506 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (5 ≤ count1506 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (6 ≤ count1506 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (7 ≤ count1506 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (1 ≤ count1524 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (1 ≤ count1526 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (2 ≤ count1526 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (2 ≤ count1529 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (1 ≤ count1531 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (2 ≤ count1531 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (1 ≤ count1533 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (2 ≤ count1533 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (3 ≤ count1533 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (4 ≤ count1533 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (3 ≤ count1537 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (4 ≤ count1537 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (5 ≤ count1537 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (1 ≤ count1544 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (2 ≤ count1544 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (1 ≤ count1546 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (2 ≤ count1546 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (3 ≤ count1546 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (1 ≤ count1549 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (1 ≤ count1553 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (2 ≤ count1553 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (3 ≤ count1557 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (4 ≤ count1557 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (5 ≤ count1557 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (7 ≤ count1564 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (8 ≤ count1564 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (9 ≤ count1564 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (1 ≤ count1578 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (1 ≤ count1583 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (1 ≤ count1587 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (1 ≤ count1591 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (2 ≤ count1591 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (3 ≤ count1591 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (1 ≤ count1598 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (1 ≤ count1600 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (2 ≤ count1600 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (1 ≤ count1602 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (2 ≤ count1602 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (3 ≤ count1602 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (1 ≤ count1606 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (1 ≤ count1608 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (1 ≤ count1610 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (2 ≤ count1610 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (1 ≤ count1614 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (2 ≤ count1614 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (3 ≤ count1614 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (3 ≤ count1622 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (4 ≤ count1622 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (5 ≤ count1622 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (6 ≤ count1622 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (11 ≤ count1637 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (12 ≤ count1637 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (13 ≤ count1637 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (14 ≤ count1637 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (18 ≤ count1655 (baseVal q)) := rfl
theorem meaningNeg116 (b : Nat → Bool) : literal (valuationOf b) (-116) = decide (1 ≤ countLit b [-116]) := by
  change literal b (-116) = decide (1 ≤ countLit b [-116])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-116) <;> decide
theorem meaningNeg114 (b : Nat → Bool) : literal (valuationOf b) (-114) = decide (1 ≤ countLit b [-114]) := by
  change literal b (-114) = decide (1 ≤ countLit b [-114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-114) <;> decide
theorem meaningNeg113 (b : Nat → Bool) : literal (valuationOf b) (-113) = decide (1 ≤ countLit b [-113]) := by
  change literal b (-113) = decide (1 ≤ countLit b [-113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-113) <;> decide
theorem meaningNeg112 (b : Nat → Bool) : literal (valuationOf b) (-112) = decide (1 ≤ countLit b [-112]) := by
  change literal b (-112) = decide (1 ≤ countLit b [-112])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-112) <;> decide
theorem meaningNeg111 (b : Nat → Bool) : literal (valuationOf b) (-111) = decide (1 ≤ countLit b [-111]) := by
  change literal b (-111) = decide (1 ≤ countLit b [-111])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-111) <;> decide
theorem meaningNeg109 (b : Nat → Bool) : literal (valuationOf b) (-109) = decide (1 ≤ countLit b [-109]) := by
  change literal b (-109) = decide (1 ≤ countLit b [-109])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-109) <;> decide
theorem meaningNeg108 (b : Nat → Bool) : literal (valuationOf b) (-108) = decide (1 ≤ countLit b [-108]) := by
  change literal b (-108) = decide (1 ≤ countLit b [-108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-108) <;> decide
theorem meaningNeg107 (b : Nat → Bool) : literal (valuationOf b) (-107) = decide (1 ≤ countLit b [-107]) := by
  change literal b (-107) = decide (1 ≤ countLit b [-107])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-107) <;> decide
theorem meaningNeg105 (b : Nat → Bool) : literal (valuationOf b) (-105) = decide (1 ≤ countLit b [-105]) := by
  change literal b (-105) = decide (1 ≤ countLit b [-105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-105) <;> decide
theorem meaningNeg104 (b : Nat → Bool) : literal (valuationOf b) (-104) = decide (1 ≤ countLit b [-104]) := by
  change literal b (-104) = decide (1 ≤ countLit b [-104])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-104) <;> decide
theorem meaningNeg103 (b : Nat → Bool) : literal (valuationOf b) (-103) = decide (1 ≤ countLit b [-103]) := by
  change literal b (-103) = decide (1 ≤ countLit b [-103])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-103) <;> decide
theorem meaningNeg101 (b : Nat → Bool) : literal (valuationOf b) (-101) = decide (1 ≤ countLit b [-101]) := by
  change literal b (-101) = decide (1 ≤ countLit b [-101])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-101) <;> decide
theorem meaningNeg100 (b : Nat → Bool) : literal (valuationOf b) (-100) = decide (1 ≤ countLit b [-100]) := by
  change literal b (-100) = decide (1 ≤ countLit b [-100])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-100) <;> decide
theorem meaningNeg99 (b : Nat → Bool) : literal (valuationOf b) (-99) = decide (1 ≤ countLit b [-99]) := by
  change literal b (-99) = decide (1 ≤ countLit b [-99])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-99) <;> decide
theorem meaningNeg97 (b : Nat → Bool) : literal (valuationOf b) (-97) = decide (1 ≤ countLit b [-97]) := by
  change literal b (-97) = decide (1 ≤ countLit b [-97])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-97) <;> decide
theorem meaningNeg95 (b : Nat → Bool) : literal (valuationOf b) (-95) = decide (1 ≤ countLit b [-95]) := by
  change literal b (-95) = decide (1 ≤ countLit b [-95])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-95) <;> decide
theorem meaningNeg94 (b : Nat → Bool) : literal (valuationOf b) (-94) = decide (1 ≤ countLit b [-94]) := by
  change literal b (-94) = decide (1 ≤ countLit b [-94])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-94) <;> decide
theorem meaningNeg92 (b : Nat → Bool) : literal (valuationOf b) (-92) = decide (1 ≤ countLit b [-92]) := by
  change literal b (-92) = decide (1 ≤ countLit b [-92])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-92) <;> decide
theorem meaningNeg91 (b : Nat → Bool) : literal (valuationOf b) (-91) = decide (1 ≤ countLit b [-91]) := by
  change literal b (-91) = decide (1 ≤ countLit b [-91])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-91) <;> decide
theorem meaningNeg90 (b : Nat → Bool) : literal (valuationOf b) (-90) = decide (1 ≤ countLit b [-90]) := by
  change literal b (-90) = decide (1 ≤ countLit b [-90])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-90) <;> decide
theorem meaningNeg89 (b : Nat → Bool) : literal (valuationOf b) (-89) = decide (1 ≤ countLit b [-89]) := by
  change literal b (-89) = decide (1 ≤ countLit b [-89])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-89) <;> decide
theorem meaningNeg88 (b : Nat → Bool) : literal (valuationOf b) (-88) = decide (1 ≤ countLit b [-88]) := by
  change literal b (-88) = decide (1 ≤ countLit b [-88])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-88) <;> decide
theorem meaningNeg87 (b : Nat → Bool) : literal (valuationOf b) (-87) = decide (1 ≤ countLit b [-87]) := by
  change literal b (-87) = decide (1 ≤ countLit b [-87])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-87) <;> decide
theorem meaningNeg86 (b : Nat → Bool) : literal (valuationOf b) (-86) = decide (1 ≤ countLit b [-86]) := by
  change literal b (-86) = decide (1 ≤ countLit b [-86])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-86) <;> decide
theorem meaningNeg85 (b : Nat → Bool) : literal (valuationOf b) (-85) = decide (1 ≤ countLit b [-85]) := by
  change literal b (-85) = decide (1 ≤ countLit b [-85])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-85) <;> decide
theorem meaningNeg84 (b : Nat → Bool) : literal (valuationOf b) (-84) = decide (1 ≤ countLit b [-84]) := by
  change literal b (-84) = decide (1 ≤ countLit b [-84])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-84) <;> decide
theorem meaningNeg83 (b : Nat → Bool) : literal (valuationOf b) (-83) = decide (1 ≤ countLit b [-83]) := by
  change literal b (-83) = decide (1 ≤ countLit b [-83])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-83) <;> decide
theorem meaningNeg82 (b : Nat → Bool) : literal (valuationOf b) (-82) = decide (1 ≤ countLit b [-82]) := by
  change literal b (-82) = decide (1 ≤ countLit b [-82])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-82) <;> decide
theorem meaningNeg81 (b : Nat → Bool) : literal (valuationOf b) (-81) = decide (1 ≤ countLit b [-81]) := by
  change literal b (-81) = decide (1 ≤ countLit b [-81])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-81) <;> decide
theorem meaningNeg79 (b : Nat → Bool) : literal (valuationOf b) (-79) = decide (1 ≤ countLit b [-79]) := by
  change literal b (-79) = decide (1 ≤ countLit b [-79])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-79) <;> decide
theorem meaningNeg78 (b : Nat → Bool) : literal (valuationOf b) (-78) = decide (1 ≤ countLit b [-78]) := by
  change literal b (-78) = decide (1 ≤ countLit b [-78])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-78) <;> decide
theorem meaningNeg77 (b : Nat → Bool) : literal (valuationOf b) (-77) = decide (1 ≤ countLit b [-77]) := by
  change literal b (-77) = decide (1 ≤ countLit b [-77])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-77) <;> decide
theorem meaningNeg76 (b : Nat → Bool) : literal (valuationOf b) (-76) = decide (1 ≤ countLit b [-76]) := by
  change literal b (-76) = decide (1 ≤ countLit b [-76])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-76) <;> decide
theorem meaningNeg75 (b : Nat → Bool) : literal (valuationOf b) (-75) = decide (1 ≤ countLit b [-75]) := by
  change literal b (-75) = decide (1 ≤ countLit b [-75])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-75) <;> decide
theorem meaningNeg74 (b : Nat → Bool) : literal (valuationOf b) (-74) = decide (1 ≤ countLit b [-74]) := by
  change literal b (-74) = decide (1 ≤ countLit b [-74])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-74) <;> decide
theorem meaningNeg73 (b : Nat → Bool) : literal (valuationOf b) (-73) = decide (1 ≤ countLit b [-73]) := by
  change literal b (-73) = decide (1 ≤ countLit b [-73])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-73) <;> decide
theorem meaningNeg72 (b : Nat → Bool) : literal (valuationOf b) (-72) = decide (1 ≤ countLit b [-72]) := by
  change literal b (-72) = decide (1 ≤ countLit b [-72])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-72) <;> decide
theorem meaningNeg71 (b : Nat → Bool) : literal (valuationOf b) (-71) = decide (1 ≤ countLit b [-71]) := by
  change literal b (-71) = decide (1 ≤ countLit b [-71])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-71) <;> decide
theorem meaningNeg70 (b : Nat → Bool) : literal (valuationOf b) (-70) = decide (1 ≤ countLit b [-70]) := by
  change literal b (-70) = decide (1 ≤ countLit b [-70])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-70) <;> decide
theorem meaningNeg69 (b : Nat → Bool) : literal (valuationOf b) (-69) = decide (1 ≤ countLit b [-69]) := by
  change literal b (-69) = decide (1 ≤ countLit b [-69])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-69) <;> decide
theorem meaningNeg68 (b : Nat → Bool) : literal (valuationOf b) (-68) = decide (1 ≤ countLit b [-68]) := by
  change literal b (-68) = decide (1 ≤ countLit b [-68])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-68) <;> decide
theorem meaningNeg67 (b : Nat → Bool) : literal (valuationOf b) (-67) = decide (1 ≤ countLit b [-67]) := by
  change literal b (-67) = decide (1 ≤ countLit b [-67])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-67) <;> decide
theorem meaningNeg66 (b : Nat → Bool) : literal (valuationOf b) (-66) = decide (1 ≤ countLit b [-66]) := by
  change literal b (-66) = decide (1 ≤ countLit b [-66])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-66) <;> decide
theorem meaningNeg65 (b : Nat → Bool) : literal (valuationOf b) (-65) = decide (1 ≤ countLit b [-65]) := by
  change literal b (-65) = decide (1 ≤ countLit b [-65])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-65) <;> decide
theorem meaningNeg64 (b : Nat → Bool) : literal (valuationOf b) (-64) = decide (1 ≤ countLit b [-64]) := by
  change literal b (-64) = decide (1 ≤ countLit b [-64])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-64) <;> decide
theorem meaningNeg63 (b : Nat → Bool) : literal (valuationOf b) (-63) = decide (1 ≤ countLit b [-63]) := by
  change literal b (-63) = decide (1 ≤ countLit b [-63])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-63) <;> decide
theorem meaningNeg62 (b : Nat → Bool) : literal (valuationOf b) (-62) = decide (1 ≤ countLit b [-62]) := by
  change literal b (-62) = decide (1 ≤ countLit b [-62])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-62) <;> decide
theorem meaningNeg61 (b : Nat → Bool) : literal (valuationOf b) (-61) = decide (1 ≤ countLit b [-61]) := by
  change literal b (-61) = decide (1 ≤ countLit b [-61])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-61) <;> decide
theorem meaningNeg60 (b : Nat → Bool) : literal (valuationOf b) (-60) = decide (1 ≤ countLit b [-60]) := by
  change literal b (-60) = decide (1 ≤ countLit b [-60])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-60) <;> decide
theorem meaningNeg59 (b : Nat → Bool) : literal (valuationOf b) (-59) = decide (1 ≤ countLit b [-59]) := by
  change literal b (-59) = decide (1 ≤ countLit b [-59])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-59) <;> decide
theorem meaningNeg58 (b : Nat → Bool) : literal (valuationOf b) (-58) = decide (1 ≤ countLit b [-58]) := by
  change literal b (-58) = decide (1 ≤ countLit b [-58])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-58) <;> decide
theorem meaningNeg57 (b : Nat → Bool) : literal (valuationOf b) (-57) = decide (1 ≤ countLit b [-57]) := by
  change literal b (-57) = decide (1 ≤ countLit b [-57])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-57) <;> decide
theorem meaningNeg56 (b : Nat → Bool) : literal (valuationOf b) (-56) = decide (1 ≤ countLit b [-56]) := by
  change literal b (-56) = decide (1 ≤ countLit b [-56])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-56) <;> decide
theorem meaningNeg55 (b : Nat → Bool) : literal (valuationOf b) (-55) = decide (1 ≤ countLit b [-55]) := by
  change literal b (-55) = decide (1 ≤ countLit b [-55])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-55) <;> decide
theorem meaningNeg54 (b : Nat → Bool) : literal (valuationOf b) (-54) = decide (1 ≤ countLit b [-54]) := by
  change literal b (-54) = decide (1 ≤ countLit b [-54])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-54) <;> decide
theorem meaningNeg52 (b : Nat → Bool) : literal (valuationOf b) (-52) = decide (1 ≤ countLit b [-52]) := by
  change literal b (-52) = decide (1 ≤ countLit b [-52])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-52) <;> decide
theorem meaningNeg50 (b : Nat → Bool) : literal (valuationOf b) (-50) = decide (1 ≤ countLit b [-50]) := by
  change literal b (-50) = decide (1 ≤ countLit b [-50])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-50) <;> decide
theorem meaningNeg48 (b : Nat → Bool) : literal (valuationOf b) (-48) = decide (1 ≤ countLit b [-48]) := by
  change literal b (-48) = decide (1 ≤ countLit b [-48])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-48) <;> decide
theorem meaningNeg44 (b : Nat → Bool) : literal (valuationOf b) (-44) = decide (1 ≤ countLit b [-44]) := by
  change literal b (-44) = decide (1 ≤ countLit b [-44])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-44) <;> decide
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
theorem meaningNeg39 (b : Nat → Bool) : literal (valuationOf b) (-39) = decide (1 ≤ countLit b [-39]) := by
  change literal b (-39) = decide (1 ≤ countLit b [-39])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-39) <;> decide
theorem meaningNeg38 (b : Nat → Bool) : literal (valuationOf b) (-38) = decide (1 ≤ countLit b [-38]) := by
  change literal b (-38) = decide (1 ≤ countLit b [-38])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-38) <;> decide
theorem meaningNeg36 (b : Nat → Bool) : literal (valuationOf b) (-36) = decide (1 ≤ countLit b [-36]) := by
  change literal b (-36) = decide (1 ≤ countLit b [-36])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-36) <;> decide
theorem meaningNeg35 (b : Nat → Bool) : literal (valuationOf b) (-35) = decide (1 ≤ countLit b [-35]) := by
  change literal b (-35) = decide (1 ≤ countLit b [-35])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-35) <;> decide
theorem meaningNeg34 (b : Nat → Bool) : literal (valuationOf b) (-34) = decide (1 ≤ countLit b [-34]) := by
  change literal b (-34) = decide (1 ≤ countLit b [-34])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-34) <;> decide
theorem meaningNeg33 (b : Nat → Bool) : literal (valuationOf b) (-33) = decide (1 ≤ countLit b [-33]) := by
  change literal b (-33) = decide (1 ≤ countLit b [-33])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-33) <;> decide
theorem meaningNeg32 (b : Nat → Bool) : literal (valuationOf b) (-32) = decide (1 ≤ countLit b [-32]) := by
  change literal b (-32) = decide (1 ≤ countLit b [-32])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-32) <;> decide
theorem meaningNeg31 (b : Nat → Bool) : literal (valuationOf b) (-31) = decide (1 ≤ countLit b [-31]) := by
  change literal b (-31) = decide (1 ≤ countLit b [-31])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-31) <;> decide
theorem meaningNeg30 (b : Nat → Bool) : literal (valuationOf b) (-30) = decide (1 ≤ countLit b [-30]) := by
  change literal b (-30) = decide (1 ≤ countLit b [-30])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-30) <;> decide
theorem meaningNeg29 (b : Nat → Bool) : literal (valuationOf b) (-29) = decide (1 ≤ countLit b [-29]) := by
  change literal b (-29) = decide (1 ≤ countLit b [-29])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-29) <;> decide
theorem meaningNeg28 (b : Nat → Bool) : literal (valuationOf b) (-28) = decide (1 ≤ countLit b [-28]) := by
  change literal b (-28) = decide (1 ≤ countLit b [-28])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-28) <;> decide
theorem meaningNeg27 (b : Nat → Bool) : literal (valuationOf b) (-27) = decide (1 ≤ countLit b [-27]) := by
  change literal b (-27) = decide (1 ≤ countLit b [-27])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-27) <;> decide
theorem meaningNeg26 (b : Nat → Bool) : literal (valuationOf b) (-26) = decide (1 ≤ countLit b [-26]) := by
  change literal b (-26) = decide (1 ≤ countLit b [-26])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-26) <;> decide
theorem meaningNeg25 (b : Nat → Bool) : literal (valuationOf b) (-25) = decide (1 ≤ countLit b [-25]) := by
  change literal b (-25) = decide (1 ≤ countLit b [-25])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-25) <;> decide
theorem meaningNeg24 (b : Nat → Bool) : literal (valuationOf b) (-24) = decide (1 ≤ countLit b [-24]) := by
  change literal b (-24) = decide (1 ≤ countLit b [-24])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-24) <;> decide
theorem meaningNeg23 (b : Nat → Bool) : literal (valuationOf b) (-23) = decide (1 ≤ countLit b [-23]) := by
  change literal b (-23) = decide (1 ≤ countLit b [-23])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-23) <;> decide
theorem meaningNeg22 (b : Nat → Bool) : literal (valuationOf b) (-22) = decide (1 ≤ countLit b [-22]) := by
  change literal b (-22) = decide (1 ≤ countLit b [-22])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-22) <;> decide
theorem meaningNeg21 (b : Nat → Bool) : literal (valuationOf b) (-21) = decide (1 ≤ countLit b [-21]) := by
  change literal b (-21) = decide (1 ≤ countLit b [-21])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-21) <;> decide
theorem meaningNeg20 (b : Nat → Bool) : literal (valuationOf b) (-20) = decide (1 ≤ countLit b [-20]) := by
  change literal b (-20) = decide (1 ≤ countLit b [-20])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-20) <;> decide
theorem meaningNeg19 (b : Nat → Bool) : literal (valuationOf b) (-19) = decide (1 ≤ countLit b [-19]) := by
  change literal b (-19) = decide (1 ≤ countLit b [-19])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-19) <;> decide
theorem meaningNeg18 (b : Nat → Bool) : literal (valuationOf b) (-18) = decide (1 ≤ countLit b [-18]) := by
  change literal b (-18) = decide (1 ≤ countLit b [-18])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-18) <;> decide
theorem meaningNeg17 (b : Nat → Bool) : literal (valuationOf b) (-17) = decide (1 ≤ countLit b [-17]) := by
  change literal b (-17) = decide (1 ≤ countLit b [-17])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-17) <;> decide
theorem meaningNeg16 (b : Nat → Bool) : literal (valuationOf b) (-16) = decide (1 ≤ countLit b [-16]) := by
  change literal b (-16) = decide (1 ≤ countLit b [-16])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-16) <;> decide
theorem meaningNeg15 (b : Nat → Bool) : literal (valuationOf b) (-15) = decide (1 ≤ countLit b [-15]) := by
  change literal b (-15) = decide (1 ≤ countLit b [-15])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-15) <;> decide
theorem meaningNeg14 (b : Nat → Bool) : literal (valuationOf b) (-14) = decide (1 ≤ countLit b [-14]) := by
  change literal b (-14) = decide (1 ≤ countLit b [-14])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-14) <;> decide
theorem meaningNeg13 (b : Nat → Bool) : literal (valuationOf b) (-13) = decide (1 ≤ countLit b [-13]) := by
  change literal b (-13) = decide (1 ≤ countLit b [-13])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-13) <;> decide
theorem meaningNeg12 (b : Nat → Bool) : literal (valuationOf b) (-12) = decide (1 ≤ countLit b [-12]) := by
  change literal b (-12) = decide (1 ≤ countLit b [-12])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-12) <;> decide
theorem meaningNeg11 (b : Nat → Bool) : literal (valuationOf b) (-11) = decide (1 ≤ countLit b [-11]) := by
  change literal b (-11) = decide (1 ≤ countLit b [-11])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-11) <;> decide
theorem meaningNeg10 (b : Nat → Bool) : literal (valuationOf b) (-10) = decide (1 ≤ countLit b [-10]) := by
  change literal b (-10) = decide (1 ≤ countLit b [-10])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-10) <;> decide
theorem meaningNeg9 (b : Nat → Bool) : literal (valuationOf b) (-9) = decide (1 ≤ countLit b [-9]) := by
  change literal b (-9) = decide (1 ≤ countLit b [-9])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-9) <;> decide
theorem meaningNeg8 (b : Nat → Bool) : literal (valuationOf b) (-8) = decide (1 ≤ countLit b [-8]) := by
  change literal b (-8) = decide (1 ≤ countLit b [-8])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-8) <;> decide
theorem meaningNeg7 (b : Nat → Bool) : literal (valuationOf b) (-7) = decide (1 ≤ countLit b [-7]) := by
  change literal b (-7) = decide (1 ≤ countLit b [-7])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-7) <;> decide
theorem meaningNeg6 (b : Nat → Bool) : literal (valuationOf b) (-6) = decide (1 ≤ countLit b [-6]) := by
  change literal b (-6) = decide (1 ≤ countLit b [-6])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-6) <;> decide
theorem meaningNeg5 (b : Nat → Bool) : literal (valuationOf b) (-5) = decide (1 ≤ countLit b [-5]) := by
  change literal b (-5) = decide (1 ≤ countLit b [-5])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-5) <;> decide
theorem meaningNeg4 (b : Nat → Bool) : literal (valuationOf b) (-4) = decide (1 ≤ countLit b [-4]) := by
  change literal b (-4) = decide (1 ≤ countLit b [-4])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-4) <;> decide
theorem meaningNeg3 (b : Nat → Bool) : literal (valuationOf b) (-3) = decide (1 ≤ countLit b [-3]) := by
  change literal b (-3) = decide (1 ≤ countLit b [-3])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-3) <;> decide
theorem meaningNeg2 (b : Nat → Bool) : literal (valuationOf b) (-2) = decide (1 ≤ countLit b [-2]) := by
  change literal b (-2) = decide (1 ≤ countLit b [-2])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-2) <;> decide
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning119 (b : Nat → Bool) : literal (valuationOf b) (119) = decide (1 ≤ countLit b [119]) := by
  change literal b (119) = decide (1 ≤ countLit b [119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (119) <;> decide
theorem meaning120 (b : Nat → Bool) : literal (valuationOf b) (120) = decide (1 ≤ countLit b [120]) := by
  change literal b (120) = decide (1 ≤ countLit b [120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (120) <;> decide
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
theorem meaning124 (b : Nat → Bool) : literal (valuationOf b) (124) = decide (1 ≤ countLit b [124]) := by
  change literal b (124) = decide (1 ≤ countLit b [124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (124) <;> decide
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
theorem meaning128 (b : Nat → Bool) : literal (valuationOf b) (128) = decide (1 ≤ countLit b [128]) := by
  change literal b (128) = decide (1 ≤ countLit b [128])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (128) <;> decide
theorem meaning129 (b : Nat → Bool) : literal (valuationOf b) (129) = decide (1 ≤ countLit b [129]) := by
  change literal b (129) = decide (1 ≤ countLit b [129])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (129) <;> decide
theorem meaning132 (b : Nat → Bool) : literal (valuationOf b) (132) = decide (1 ≤ countLit b [132]) := by
  change literal b (132) = decide (1 ≤ countLit b [132])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (132) <;> decide
theorem meaning134 (b : Nat → Bool) : literal (valuationOf b) (134) = decide (1 ≤ countLit b [134]) := by
  change literal b (134) = decide (1 ≤ countLit b [134])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (134) <;> decide
theorem meaning136 (b : Nat → Bool) : literal (valuationOf b) (136) = decide (1 ≤ countLit b [136]) := by
  change literal b (136) = decide (1 ≤ countLit b [136])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (136) <;> decide
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
theorem meaning140 (b : Nat → Bool) : literal (valuationOf b) (140) = decide (1 ≤ countLit b [140]) := by
  change literal b (140) = decide (1 ≤ countLit b [140])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (140) <;> decide
theorem meaning142 (b : Nat → Bool) : literal (valuationOf b) (142) = decide (1 ≤ countLit b [142]) := by
  change literal b (142) = decide (1 ≤ countLit b [142])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (142) <;> decide
theorem meaning145 (b : Nat → Bool) : literal (valuationOf b) (145) = decide (1 ≤ countLit b [145]) := by
  change literal b (145) = decide (1 ≤ countLit b [145])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (145) <;> decide
theorem meaning147 (b : Nat → Bool) : literal (valuationOf b) (147) = decide (1 ≤ countLit b [147]) := by
  change literal b (147) = decide (1 ≤ countLit b [147])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (147) <;> decide
theorem meaning149 (b : Nat → Bool) : literal (valuationOf b) (149) = decide (1 ≤ countLit b [149]) := by
  change literal b (149) = decide (1 ≤ countLit b [149])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (149) <;> decide
theorem meaning151 (b : Nat → Bool) : literal (valuationOf b) (151) = decide (1 ≤ countLit b [151]) := by
  change literal b (151) = decide (1 ≤ countLit b [151])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (151) <;> decide
theorem meaning153 (b : Nat → Bool) : literal (valuationOf b) (153) = decide (1 ≤ countLit b [153]) := by
  change literal b (153) = decide (1 ≤ countLit b [153])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (153) <;> decide
theorem meaning156 (b : Nat → Bool) : literal (valuationOf b) (156) = decide (1 ≤ countLit b [156]) := by
  change literal b (156) = decide (1 ≤ countLit b [156])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (156) <;> decide
theorem meaning157 (b : Nat → Bool) : literal (valuationOf b) (157) = decide (1 ≤ countLit b [157]) := by
  change literal b (157) = decide (1 ≤ countLit b [157])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (157) <;> decide
theorem meaning159 (b : Nat → Bool) : literal (valuationOf b) (159) = decide (1 ≤ countLit b [159]) := by
  change literal b (159) = decide (1 ≤ countLit b [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (159) <;> decide
theorem meaning161 (b : Nat → Bool) : literal (valuationOf b) (161) = decide (1 ≤ countLit b [161]) := by
  change literal b (161) = decide (1 ≤ countLit b [161])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (161) <;> decide
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
theorem meaning165 (b : Nat → Bool) : literal (valuationOf b) (165) = decide (1 ≤ countLit b [165]) := by
  change literal b (165) = decide (1 ≤ countLit b [165])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (165) <;> decide
theorem meaning167 (b : Nat → Bool) : literal (valuationOf b) (167) = decide (1 ≤ countLit b [167]) := by
  change literal b (167) = decide (1 ≤ countLit b [167])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (167) <;> decide
theorem meaning169 (b : Nat → Bool) : literal (valuationOf b) (169) = decide (1 ≤ countLit b [169]) := by
  change literal b (169) = decide (1 ≤ countLit b [169])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (169) <;> decide
theorem meaning170 (b : Nat → Bool) : literal (valuationOf b) (170) = decide (1 ≤ countLit b [170]) := by
  change literal b (170) = decide (1 ≤ countLit b [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (170) <;> decide
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
theorem meaning174 (b : Nat → Bool) : literal (valuationOf b) (174) = decide (1 ≤ countLit b [174]) := by
  change literal b (174) = decide (1 ≤ countLit b [174])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (174) <;> decide
theorem meaning175 (b : Nat → Bool) : literal (valuationOf b) (175) = decide (1 ≤ countLit b [175]) := by
  change literal b (175) = decide (1 ≤ countLit b [175])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (175) <;> decide
theorem meaning177 (b : Nat → Bool) : literal (valuationOf b) (177) = decide (1 ≤ countLit b [177]) := by
  change literal b (177) = decide (1 ≤ countLit b [177])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (177) <;> decide
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
theorem meaning183 (b : Nat → Bool) : literal (valuationOf b) (183) = decide (1 ≤ countLit b [183]) := by
  change literal b (183) = decide (1 ≤ countLit b [183])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (183) <;> decide
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
theorem meaning187 (b : Nat → Bool) : literal (valuationOf b) (187) = decide (1 ≤ countLit b [187]) := by
  change literal b (187) = decide (1 ≤ countLit b [187])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (187) <;> decide
theorem meaning188 (b : Nat → Bool) : literal (valuationOf b) (188) = decide (1 ≤ countLit b [188]) := by
  change literal b (188) = decide (1 ≤ countLit b [188])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (188) <;> decide
theorem meaning192 (b : Nat → Bool) : literal (valuationOf b) (192) = decide (1 ≤ countLit b [192]) := by
  change literal b (192) = decide (1 ≤ countLit b [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (192) <;> decide
theorem meaning193 (b : Nat → Bool) : literal (valuationOf b) (193) = decide (1 ≤ countLit b [193]) := by
  change literal b (193) = decide (1 ≤ countLit b [193])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (193) <;> decide
theorem meaning195 (b : Nat → Bool) : literal (valuationOf b) (195) = decide (1 ≤ countLit b [195]) := by
  change literal b (195) = decide (1 ≤ countLit b [195])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (195) <;> decide
theorem meaning196 (b : Nat → Bool) : literal (valuationOf b) (196) = decide (1 ≤ countLit b [196]) := by
  change literal b (196) = decide (1 ≤ countLit b [196])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (196) <;> decide
theorem meaning197 (b : Nat → Bool) : literal (valuationOf b) (197) = decide (1 ≤ countLit b [197]) := by
  change literal b (197) = decide (1 ≤ countLit b [197])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (197) <;> decide
theorem meaning202 (b : Nat → Bool) : literal (valuationOf b) (202) = decide (1 ≤ countLit b [202]) := by
  change literal b (202) = decide (1 ≤ countLit b [202])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (202) <;> decide
theorem meaning208 (b : Nat → Bool) : literal (valuationOf b) (208) = decide (1 ≤ countLit b [208]) := by
  change literal b (208) = decide (1 ≤ countLit b [208])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (208) <;> decide
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning212 (b : Nat → Bool) : literal (valuationOf b) (212) = decide (1 ≤ countLit b [212]) := by
  change literal b (212) = decide (1 ≤ countLit b [212])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (212) <;> decide
theorem meaning214 (b : Nat → Bool) : literal (valuationOf b) (214) = decide (1 ≤ countLit b [214]) := by
  change literal b (214) = decide (1 ≤ countLit b [214])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (214) <;> decide
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) (218) = decide (1 ≤ countLit b [218]) := by
  change literal b (218) = decide (1 ≤ countLit b [218])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (218) <;> decide
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) (219) = decide (1 ≤ countLit b [219]) := by
  change literal b (219) = decide (1 ≤ countLit b [219])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (219) <;> decide
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) (222) = decide (1 ≤ countLit b [222]) := by
  change literal b (222) = decide (1 ≤ countLit b [222])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (222) <;> decide
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) (223) = decide (1 ≤ countLit b [223]) := by
  change literal b (223) = decide (1 ≤ countLit b [223])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (223) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) 238 = decide (2 ≤ count237 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) 242 = decide (2 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) 244 = decide (2 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning248 (b : Nat → Bool) : literal (valuationOf b) 248 = decide (2 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning268 (b : Nat → Bool) : literal (valuationOf b) 268 = decide (2 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning274 (b : Nat → Bool) : literal (valuationOf b) 274 = decide (2 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning284 (b : Nat → Bool) : literal (valuationOf b) 284 = decide (2 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning286 (b : Nat → Bool) : literal (valuationOf b) 286 = decide (2 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning298 (b : Nat → Bool) : literal (valuationOf b) 298 = decide (2 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning338 (b : Nat → Bool) : literal (valuationOf b) 338 = decide (2 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning366 (b : Nat → Bool) : literal (valuationOf b) 366 = decide (2 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning370 (b : Nat → Bool) : literal (valuationOf b) 370 = decide (2 ≤ count369 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning398 (b : Nat → Bool) : literal (valuationOf b) 398 = decide (2 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning456 (b : Nat → Bool) : literal (valuationOf b) 456 = decide (2 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning458 (b : Nat → Bool) : literal (valuationOf b) 458 = decide (2 ≤ count457 b) := rfl
theorem meaning460 (b : Nat → Bool) : literal (valuationOf b) 460 = decide (2 ≤ count459 b) := rfl
theorem meaning787 (b : Nat → Bool) : literal (valuationOf b) 787 = decide (1 ≤ count787 b) := rfl
theorem meaning788 (b : Nat → Bool) : literal (valuationOf b) 788 = decide (2 ≤ count787 b) := rfl
theorem meaning789 (b : Nat → Bool) : literal (valuationOf b) 789 = decide (1 ≤ count789 b) := rfl
theorem meaning790 (b : Nat → Bool) : literal (valuationOf b) 790 = decide (2 ≤ count789 b) := rfl
theorem meaning791 (b : Nat → Bool) : literal (valuationOf b) 791 = decide (3 ≤ count789 b) := rfl
theorem meaning792 (b : Nat → Bool) : literal (valuationOf b) 792 = decide (1 ≤ count792 b) := rfl
theorem meaning793 (b : Nat → Bool) : literal (valuationOf b) 793 = decide (2 ≤ count792 b) := rfl
theorem meaning794 (b : Nat → Bool) : literal (valuationOf b) 794 = decide (1 ≤ count794 b) := rfl
theorem meaning795 (b : Nat → Bool) : literal (valuationOf b) 795 = decide (2 ≤ count794 b) := rfl
theorem meaning796 (b : Nat → Bool) : literal (valuationOf b) 796 = decide (1 ≤ count796 b) := rfl
theorem meaning797 (b : Nat → Bool) : literal (valuationOf b) 797 = decide (2 ≤ count796 b) := rfl
theorem meaning798 (b : Nat → Bool) : literal (valuationOf b) 798 = decide (3 ≤ count796 b) := rfl
theorem meaning799 (b : Nat → Bool) : literal (valuationOf b) 799 = decide (4 ≤ count796 b) := rfl
theorem meaning800 (b : Nat → Bool) : literal (valuationOf b) 800 = decide (1 ≤ count800 b) := rfl
theorem meaning801 (b : Nat → Bool) : literal (valuationOf b) 801 = decide (2 ≤ count800 b) := rfl
theorem meaning802 (b : Nat → Bool) : literal (valuationOf b) 802 = decide (3 ≤ count800 b) := rfl
theorem meaning803 (b : Nat → Bool) : literal (valuationOf b) 803 = decide (4 ≤ count800 b) := rfl
theorem meaning804 (b : Nat → Bool) : literal (valuationOf b) 804 = decide (5 ≤ count800 b) := rfl
theorem meaning805 (b : Nat → Bool) : literal (valuationOf b) 805 = decide (6 ≤ count800 b) := rfl
theorem meaning807 (b : Nat → Bool) : literal (valuationOf b) 807 = decide (1 ≤ count807 b) := rfl
theorem meaning808 (b : Nat → Bool) : literal (valuationOf b) 808 = decide (2 ≤ count807 b) := rfl
theorem meaning809 (b : Nat → Bool) : literal (valuationOf b) 809 = decide (1 ≤ count809 b) := rfl
theorem meaning810 (b : Nat → Bool) : literal (valuationOf b) 810 = decide (2 ≤ count809 b) := rfl
theorem meaning811 (b : Nat → Bool) : literal (valuationOf b) 811 = decide (3 ≤ count809 b) := rfl
theorem meaning812 (b : Nat → Bool) : literal (valuationOf b) 812 = decide (1 ≤ count812 b) := rfl
theorem meaning813 (b : Nat → Bool) : literal (valuationOf b) 813 = decide (2 ≤ count812 b) := rfl
theorem meaning814 (b : Nat → Bool) : literal (valuationOf b) 814 = decide (1 ≤ count814 b) := rfl
theorem meaning815 (b : Nat → Bool) : literal (valuationOf b) 815 = decide (2 ≤ count814 b) := rfl
theorem meaning816 (b : Nat → Bool) : literal (valuationOf b) 816 = decide (1 ≤ count816 b) := rfl
theorem meaning817 (b : Nat → Bool) : literal (valuationOf b) 817 = decide (2 ≤ count816 b) := rfl
theorem meaning818 (b : Nat → Bool) : literal (valuationOf b) 818 = decide (3 ≤ count816 b) := rfl
theorem meaning819 (b : Nat → Bool) : literal (valuationOf b) 819 = decide (4 ≤ count816 b) := rfl
theorem meaning820 (b : Nat → Bool) : literal (valuationOf b) 820 = decide (1 ≤ count820 b) := rfl
theorem meaning821 (b : Nat → Bool) : literal (valuationOf b) 821 = decide (2 ≤ count820 b) := rfl
theorem meaning822 (b : Nat → Bool) : literal (valuationOf b) 822 = decide (3 ≤ count820 b) := rfl
theorem meaning823 (b : Nat → Bool) : literal (valuationOf b) 823 = decide (4 ≤ count820 b) := rfl
theorem meaning824 (b : Nat → Bool) : literal (valuationOf b) 824 = decide (5 ≤ count820 b) := rfl
theorem meaning825 (b : Nat → Bool) : literal (valuationOf b) 825 = decide (6 ≤ count820 b) := rfl
theorem meaning827 (b : Nat → Bool) : literal (valuationOf b) 827 = decide (1 ≤ count827 b) := rfl
theorem meaning828 (b : Nat → Bool) : literal (valuationOf b) 828 = decide (2 ≤ count827 b) := rfl
theorem meaning829 (b : Nat → Bool) : literal (valuationOf b) 829 = decide (3 ≤ count827 b) := rfl
theorem meaning830 (b : Nat → Bool) : literal (valuationOf b) 830 = decide (4 ≤ count827 b) := rfl
theorem meaning831 (b : Nat → Bool) : literal (valuationOf b) 831 = decide (5 ≤ count827 b) := rfl
theorem meaning832 (b : Nat → Bool) : literal (valuationOf b) 832 = decide (6 ≤ count827 b) := rfl
theorem meaning833 (b : Nat → Bool) : literal (valuationOf b) 833 = decide (7 ≤ count827 b) := rfl
theorem meaning834 (b : Nat → Bool) : literal (valuationOf b) 834 = decide (8 ≤ count827 b) := rfl
theorem meaning835 (b : Nat → Bool) : literal (valuationOf b) 835 = decide (9 ≤ count827 b) := rfl
theorem meaning836 (b : Nat → Bool) : literal (valuationOf b) 836 = decide (10 ≤ count827 b) := rfl
theorem meaning837 (b : Nat → Bool) : literal (valuationOf b) 837 = decide (11 ≤ count827 b) := rfl
theorem meaning841 (b : Nat → Bool) : literal (valuationOf b) 841 = decide (1 ≤ count841 b) := rfl
theorem meaning842 (b : Nat → Bool) : literal (valuationOf b) 842 = decide (2 ≤ count841 b) := rfl
theorem meaning843 (b : Nat → Bool) : literal (valuationOf b) 843 = decide (1 ≤ count843 b) := rfl
theorem meaning844 (b : Nat → Bool) : literal (valuationOf b) 844 = decide (2 ≤ count843 b) := rfl
theorem meaning845 (b : Nat → Bool) : literal (valuationOf b) 845 = decide (3 ≤ count843 b) := rfl
theorem meaning846 (b : Nat → Bool) : literal (valuationOf b) 846 = decide (1 ≤ count846 b) := rfl
theorem meaning847 (b : Nat → Bool) : literal (valuationOf b) 847 = decide (2 ≤ count846 b) := rfl
theorem meaning848 (b : Nat → Bool) : literal (valuationOf b) 848 = decide (1 ≤ count848 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (1 ≤ count850 b) := rfl
theorem meaning851 (b : Nat → Bool) : literal (valuationOf b) 851 = decide (2 ≤ count850 b) := rfl
theorem meaning852 (b : Nat → Bool) : literal (valuationOf b) 852 = decide (3 ≤ count850 b) := rfl
theorem meaning854 (b : Nat → Bool) : literal (valuationOf b) 854 = decide (1 ≤ count854 b) := rfl
theorem meaning855 (b : Nat → Bool) : literal (valuationOf b) 855 = decide (2 ≤ count854 b) := rfl
theorem meaning856 (b : Nat → Bool) : literal (valuationOf b) 856 = decide (3 ≤ count854 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (4 ≤ count854 b) := rfl
theorem meaning861 (b : Nat → Bool) : literal (valuationOf b) 861 = decide (1 ≤ count861 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (1 ≤ count863 b) := rfl
theorem meaning864 (b : Nat → Bool) : literal (valuationOf b) 864 = decide (2 ≤ count863 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (1 ≤ count865 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (2 ≤ count865 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (1 ≤ count869 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (2 ≤ count869 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (1 ≤ count871 b) := rfl
theorem meaning872 (b : Nat → Bool) : literal (valuationOf b) 872 = decide (2 ≤ count871 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (1 ≤ count873 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (2 ≤ count873 b) := rfl
theorem meaning875 (b : Nat → Bool) : literal (valuationOf b) 875 = decide (3 ≤ count873 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (4 ≤ count873 b) := rfl
theorem meaning877 (b : Nat → Bool) : literal (valuationOf b) 877 = decide (1 ≤ count877 b) := rfl
theorem meaning878 (b : Nat → Bool) : literal (valuationOf b) 878 = decide (2 ≤ count877 b) := rfl
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (3 ≤ count877 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (4 ≤ count877 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (5 ≤ count877 b) := rfl
theorem meaning885 (b : Nat → Bool) : literal (valuationOf b) 885 = decide (1 ≤ count885 b) := rfl
theorem meaning886 (b : Nat → Bool) : literal (valuationOf b) 886 = decide (2 ≤ count885 b) := rfl
theorem meaning887 (b : Nat → Bool) : literal (valuationOf b) 887 = decide (3 ≤ count885 b) := rfl
theorem meaning888 (b : Nat → Bool) : literal (valuationOf b) 888 = decide (4 ≤ count885 b) := rfl
theorem meaning889 (b : Nat → Bool) : literal (valuationOf b) 889 = decide (5 ≤ count885 b) := rfl
theorem meaning890 (b : Nat → Bool) : literal (valuationOf b) 890 = decide (6 ≤ count885 b) := rfl
theorem meaning891 (b : Nat → Bool) : literal (valuationOf b) 891 = decide (7 ≤ count885 b) := rfl
theorem meaning903 (b : Nat → Bool) : literal (valuationOf b) 903 = decide (4 ≤ count900 b) := rfl
theorem meaning904 (b : Nat → Bool) : literal (valuationOf b) 904 = decide (5 ≤ count900 b) := rfl
theorem meaning905 (b : Nat → Bool) : literal (valuationOf b) 905 = decide (6 ≤ count900 b) := rfl
theorem meaning906 (b : Nat → Bool) : literal (valuationOf b) 906 = decide (7 ≤ count900 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (8 ≤ count900 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (9 ≤ count900 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (10 ≤ count900 b) := rfl
theorem meaning910 (b : Nat → Bool) : literal (valuationOf b) 910 = decide (11 ≤ count900 b) := rfl
theorem meaning911 (b : Nat → Bool) : literal (valuationOf b) 911 = decide (12 ≤ count900 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (13 ≤ count900 b) := rfl
theorem meaning918 (b : Nat → Bool) : literal (valuationOf b) 918 = decide (1 ≤ count918 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (2 ≤ count918 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (1 ≤ count920 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (2 ≤ count920 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (3 ≤ count920 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (1 ≤ count923 b) := rfl
theorem meaning924 (b : Nat → Bool) : literal (valuationOf b) 924 = decide (2 ≤ count923 b) := rfl
theorem meaning925 (b : Nat → Bool) : literal (valuationOf b) 925 = decide (1 ≤ count925 b) := rfl
theorem meaning926 (b : Nat → Bool) : literal (valuationOf b) 926 = decide (2 ≤ count925 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (1 ≤ count927 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (2 ≤ count927 b) := rfl
theorem meaning929 (b : Nat → Bool) : literal (valuationOf b) 929 = decide (3 ≤ count927 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (4 ≤ count927 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (1 ≤ count931 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (2 ≤ count931 b) := rfl
theorem meaning933 (b : Nat → Bool) : literal (valuationOf b) 933 = decide (3 ≤ count931 b) := rfl
theorem meaning934 (b : Nat → Bool) : literal (valuationOf b) 934 = decide (4 ≤ count931 b) := rfl
theorem meaning935 (b : Nat → Bool) : literal (valuationOf b) 935 = decide (5 ≤ count931 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (1 ≤ count938 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (2 ≤ count938 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (1 ≤ count940 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (2 ≤ count940 b) := rfl
theorem meaning942 (b : Nat → Bool) : literal (valuationOf b) 942 = decide (3 ≤ count940 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (1 ≤ count943 b) := rfl
theorem meaning944 (b : Nat → Bool) : literal (valuationOf b) 944 = decide (2 ≤ count943 b) := rfl
theorem meaning945 (b : Nat → Bool) : literal (valuationOf b) 945 = decide (1 ≤ count945 b) := rfl
theorem meaning946 (b : Nat → Bool) : literal (valuationOf b) 946 = decide (2 ≤ count945 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (1 ≤ count947 b) := rfl
theorem meaning948 (b : Nat → Bool) : literal (valuationOf b) 948 = decide (2 ≤ count947 b) := rfl
theorem meaning949 (b : Nat → Bool) : literal (valuationOf b) 949 = decide (3 ≤ count947 b) := rfl
theorem meaning950 (b : Nat → Bool) : literal (valuationOf b) 950 = decide (4 ≤ count947 b) := rfl
theorem meaning951 (b : Nat → Bool) : literal (valuationOf b) 951 = decide (1 ≤ count951 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (2 ≤ count951 b) := rfl
theorem meaning953 (b : Nat → Bool) : literal (valuationOf b) 953 = decide (3 ≤ count951 b) := rfl
theorem meaning954 (b : Nat → Bool) : literal (valuationOf b) 954 = decide (4 ≤ count951 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (5 ≤ count951 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (6 ≤ count951 b) := rfl
theorem meaning957 (b : Nat → Bool) : literal (valuationOf b) 957 = decide (7 ≤ count951 b) := rfl
theorem meaning959 (b : Nat → Bool) : literal (valuationOf b) 959 = decide (2 ≤ count958 b) := rfl
theorem meaning960 (b : Nat → Bool) : literal (valuationOf b) 960 = decide (3 ≤ count958 b) := rfl
theorem meaning961 (b : Nat → Bool) : literal (valuationOf b) 961 = decide (4 ≤ count958 b) := rfl
theorem meaning962 (b : Nat → Bool) : literal (valuationOf b) 962 = decide (5 ≤ count958 b) := rfl
theorem meaning963 (b : Nat → Bool) : literal (valuationOf b) 963 = decide (6 ≤ count958 b) := rfl
theorem meaning964 (b : Nat → Bool) : literal (valuationOf b) 964 = decide (7 ≤ count958 b) := rfl
theorem meaning965 (b : Nat → Bool) : literal (valuationOf b) 965 = decide (8 ≤ count958 b) := rfl
theorem meaning966 (b : Nat → Bool) : literal (valuationOf b) 966 = decide (9 ≤ count958 b) := rfl
theorem meaning967 (b : Nat → Bool) : literal (valuationOf b) 967 = decide (10 ≤ count958 b) := rfl
theorem meaning972 (b : Nat → Bool) : literal (valuationOf b) 972 = decide (1 ≤ count972 b) := rfl
theorem meaning973 (b : Nat → Bool) : literal (valuationOf b) 973 = decide (2 ≤ count972 b) := rfl
theorem meaning974 (b : Nat → Bool) : literal (valuationOf b) 974 = decide (1 ≤ count974 b) := rfl
theorem meaning975 (b : Nat → Bool) : literal (valuationOf b) 975 = decide (2 ≤ count974 b) := rfl
theorem meaning976 (b : Nat → Bool) : literal (valuationOf b) 976 = decide (3 ≤ count974 b) := rfl
theorem meaning977 (b : Nat → Bool) : literal (valuationOf b) 977 = decide (1 ≤ count977 b) := rfl
theorem meaning979 (b : Nat → Bool) : literal (valuationOf b) 979 = decide (1 ≤ count979 b) := rfl
theorem meaning981 (b : Nat → Bool) : literal (valuationOf b) 981 = decide (1 ≤ count981 b) := rfl
theorem meaning982 (b : Nat → Bool) : literal (valuationOf b) 982 = decide (2 ≤ count981 b) := rfl
theorem meaning985 (b : Nat → Bool) : literal (valuationOf b) 985 = decide (1 ≤ count985 b) := rfl
theorem meaning986 (b : Nat → Bool) : literal (valuationOf b) 986 = decide (2 ≤ count985 b) := rfl
theorem meaning987 (b : Nat → Bool) : literal (valuationOf b) 987 = decide (3 ≤ count985 b) := rfl
theorem meaning988 (b : Nat → Bool) : literal (valuationOf b) 988 = decide (4 ≤ count985 b) := rfl
theorem meaning992 (b : Nat → Bool) : literal (valuationOf b) 992 = decide (1 ≤ count992 b) := rfl
theorem meaning993 (b : Nat → Bool) : literal (valuationOf b) 993 = decide (2 ≤ count992 b) := rfl
theorem meaning994 (b : Nat → Bool) : literal (valuationOf b) 994 = decide (1 ≤ count994 b) := rfl
theorem meaning996 (b : Nat → Bool) : literal (valuationOf b) 996 = decide (1 ≤ count996 b) := rfl
theorem meaning997 (b : Nat → Bool) : literal (valuationOf b) 997 = decide (2 ≤ count996 b) := rfl
theorem meaning998 (b : Nat → Bool) : literal (valuationOf b) 998 = decide (3 ≤ count996 b) := rfl
theorem meaning1000 (b : Nat → Bool) : literal (valuationOf b) 1000 = decide (1 ≤ count1000 b) := rfl
theorem meaning1001 (b : Nat → Bool) : literal (valuationOf b) 1001 = decide (2 ≤ count1000 b) := rfl
theorem meaning1002 (b : Nat → Bool) : literal (valuationOf b) 1002 = decide (1 ≤ count1002 b) := rfl
theorem meaning1004 (b : Nat → Bool) : literal (valuationOf b) 1004 = decide (1 ≤ count1004 b) := rfl
theorem meaning1005 (b : Nat → Bool) : literal (valuationOf b) 1005 = decide (2 ≤ count1004 b) := rfl
theorem meaning1006 (b : Nat → Bool) : literal (valuationOf b) 1006 = decide (3 ≤ count1004 b) := rfl
theorem meaning1009 (b : Nat → Bool) : literal (valuationOf b) 1009 = decide (2 ≤ count1008 b) := rfl
theorem meaning1010 (b : Nat → Bool) : literal (valuationOf b) 1010 = decide (3 ≤ count1008 b) := rfl
theorem meaning1011 (b : Nat → Bool) : literal (valuationOf b) 1011 = decide (4 ≤ count1008 b) := rfl
theorem meaning1012 (b : Nat → Bool) : literal (valuationOf b) 1012 = decide (5 ≤ count1008 b) := rfl
theorem meaning1017 (b : Nat → Bool) : literal (valuationOf b) 1017 = decide (2 ≤ count1016 b) := rfl
theorem meaning1018 (b : Nat → Bool) : literal (valuationOf b) 1018 = decide (3 ≤ count1016 b) := rfl
theorem meaning1019 (b : Nat → Bool) : literal (valuationOf b) 1019 = decide (4 ≤ count1016 b) := rfl
theorem meaning1020 (b : Nat → Bool) : literal (valuationOf b) 1020 = decide (5 ≤ count1016 b) := rfl
theorem meaning1021 (b : Nat → Bool) : literal (valuationOf b) 1021 = decide (6 ≤ count1016 b) := rfl
theorem meaning1022 (b : Nat → Bool) : literal (valuationOf b) 1022 = decide (7 ≤ count1016 b) := rfl
theorem meaning1035 (b : Nat → Bool) : literal (valuationOf b) 1035 = decide (5 ≤ count1031 b) := rfl
theorem meaning1036 (b : Nat → Bool) : literal (valuationOf b) 1036 = decide (6 ≤ count1031 b) := rfl
theorem meaning1037 (b : Nat → Bool) : literal (valuationOf b) 1037 = decide (7 ≤ count1031 b) := rfl
theorem meaning1038 (b : Nat → Bool) : literal (valuationOf b) 1038 = decide (8 ≤ count1031 b) := rfl
theorem meaning1039 (b : Nat → Bool) : literal (valuationOf b) 1039 = decide (9 ≤ count1031 b) := rfl
theorem meaning1040 (b : Nat → Bool) : literal (valuationOf b) 1040 = decide (10 ≤ count1031 b) := rfl
theorem meaning1041 (b : Nat → Bool) : literal (valuationOf b) 1041 = decide (11 ≤ count1031 b) := rfl
theorem meaning1042 (b : Nat → Bool) : literal (valuationOf b) 1042 = decide (12 ≤ count1031 b) := rfl
theorem meaning1043 (b : Nat → Bool) : literal (valuationOf b) 1043 = decide (13 ≤ count1031 b) := rfl
theorem meaning1044 (b : Nat → Bool) : literal (valuationOf b) 1044 = decide (14 ≤ count1031 b) := rfl
theorem meaning1066 (b : Nat → Bool) : literal (valuationOf b) 1066 = decide (18 ≤ count1049 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (1 ≤ count1393 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (2 ≤ count1393 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (1 ≤ count1395 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (2 ≤ count1395 b) := rfl
theorem meaning1397 (b : Nat → Bool) : literal (valuationOf b) 1397 = decide (3 ≤ count1395 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (1 ≤ count1398 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (2 ≤ count1398 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (1 ≤ count1400 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (2 ≤ count1400 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (1 ≤ count1402 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (2 ≤ count1402 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (3 ≤ count1402 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (1 ≤ count1406 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (2 ≤ count1406 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (3 ≤ count1406 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (4 ≤ count1406 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (1 ≤ count1413 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (1 ≤ count1415 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (2 ≤ count1415 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (1 ≤ count1418 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (2 ≤ count1418 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (1 ≤ count1420 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (2 ≤ count1420 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (1 ≤ count1422 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (2 ≤ count1422 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (3 ≤ count1422 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (1 ≤ count1426 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (2 ≤ count1426 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (3 ≤ count1426 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (4 ≤ count1426 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (3 ≤ count1433 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (4 ≤ count1433 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (1 ≤ count1447 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (2 ≤ count1447 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (1 ≤ count1449 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (2 ≤ count1449 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (1 ≤ count1456 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (1 ≤ count1460 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (2 ≤ count1460 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (3 ≤ count1460 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (1 ≤ count1477 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (2 ≤ count1477 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (1 ≤ count1479 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (2 ≤ count1479 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (1 ≤ count1483 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (2 ≤ count1483 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (1 ≤ count1491 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (3 ≤ count1491 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (4 ≤ count1491 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (4 ≤ count1506 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (5 ≤ count1506 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (6 ≤ count1506 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (7 ≤ count1506 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (1 ≤ count1524 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (1 ≤ count1526 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (2 ≤ count1526 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (2 ≤ count1529 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (1 ≤ count1531 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (2 ≤ count1531 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (1 ≤ count1533 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (2 ≤ count1533 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (3 ≤ count1533 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (4 ≤ count1533 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (3 ≤ count1537 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (4 ≤ count1537 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (5 ≤ count1537 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (1 ≤ count1544 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (2 ≤ count1544 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (1 ≤ count1546 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (2 ≤ count1546 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (3 ≤ count1546 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (1 ≤ count1549 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (1 ≤ count1553 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (2 ≤ count1553 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (3 ≤ count1557 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (4 ≤ count1557 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (5 ≤ count1557 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (7 ≤ count1564 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (8 ≤ count1564 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (9 ≤ count1564 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (1 ≤ count1578 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (1 ≤ count1583 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (1 ≤ count1587 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (1 ≤ count1591 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (2 ≤ count1591 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (3 ≤ count1591 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (1 ≤ count1598 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (1 ≤ count1600 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (2 ≤ count1600 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (1 ≤ count1602 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (2 ≤ count1602 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (3 ≤ count1602 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (1 ≤ count1606 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (1 ≤ count1608 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (1 ≤ count1610 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (2 ≤ count1610 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (1 ≤ count1614 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (2 ≤ count1614 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (3 ≤ count1614 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (3 ≤ count1622 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (4 ≤ count1622 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (5 ≤ count1622 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (6 ≤ count1622 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (11 ≤ count1637 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (12 ≤ count1637 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (13 ≤ count1637 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (14 ≤ count1637 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (18 ≤ count1655 b) := rfl
structure Conditions (q : Snake 81) : Prop where
  head_fixed : q.vertex 0 = head
  covered : ∀ v, InPath q v → v ∈ region

theorem absent_odd_bound (q : Snake 81) (h : Conditions q) :
    (oddSide.filter (fun v => !(decide (InPath q v)))).length ≤ oddSide.length - 41 := by
  have hb := absent_side_bound q true oddSide (fun v hv hp => odd_mem v (h.covered v hv) hp)
  exact hb

theorem absent_even_bound (q : Snake 81) (h : Conditions q) :
    (evenSide.filter (fun v => !(decide (InPath q v)))).length ≤ evenSide.length - 41 := by
  have hb := absent_side_bound q false evenSide (fun v hv hp => even_mem v (h.covered v hv) hp)
  exact hb

theorem other_count_bound (q : Snake 81) (h : Conditions q) :
    (others.filter (fun v => decide (BallClauseLogic.Endpoint q v))).length ≤ 1 := by
  apply endpoint_count q others others_nodup
  rw [h.head_fixed]
  exact head_not_others

end
end Snake9.Regrowth.E112259
