import E112051Data
namespace Snake9.Regrowth.E112051
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 116 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (6 : Vertex)) else decide (InPath q (7 : Vertex))) else (if i < 6 then decide (InPath q (8 : Vertex)) else decide (InPath q (10 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (14 : Vertex)) else (if i < 9 then decide (InPath q (15 : Vertex)) else decide (InPath q (17 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (20 : Vertex)) else decide (InPath q (21 : Vertex))) else (if i < 13 then decide (InPath q (22 : Vertex)) else decide (InPath q (25 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (26 : Vertex)) else (if i < 16 then decide (InPath q (27 : Vertex)) else decide (InPath q (29 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (65 : Vertex)) else decide (InPath q (69 : Vertex))) else (if i < 20 then decide (InPath q (73 : Vertex)) else decide (InPath q (75 : Vertex))))) else (if i < 25 then (if i < 23 then (if i < 22 then decide (InPath q (79 : Vertex)) else decide (InPath q (97 : Vertex))) else (if i < 24 then decide (InPath q (104 : Vertex)) else decide (InPath q (106 : Vertex)))) else (if i < 27 then (if i < 26 then decide (InPath q (110 : Vertex)) else decide (InPath q (111 : Vertex))) else (if i < 28 then decide (InPath q (113 : Vertex)) else decide (InPath q (121 : Vertex))))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then decide (InPath q (122 : Vertex)) else (if i < 31 then decide (InPath q (123 : Vertex)) else decide (InPath q (125 : Vertex)))) else (if i < 34 then (if i < 33 then decide (InPath q (160 : Vertex)) else decide (InPath q (161 : Vertex))) else (if i < 35 then decide (InPath q (166 : Vertex)) else decide (InPath q (167 : Vertex))))) else (if i < 39 then (if i < 37 then decide (InPath q (168 : Vertex)) else (if i < 38 then decide (InPath q (170 : Vertex)) else decide (InPath q (172 : Vertex)))) else (if i < 41 then (if i < 40 then decide (InPath q (174 : Vertex)) else decide (InPath q (175 : Vertex))) else (if i < 42 then decide (InPath q (177 : Vertex)) else decide (InPath q (180 : Vertex)))))) else (if i < 50 then (if i < 46 then (if i < 44 then decide (InPath q (181 : Vertex)) else (if i < 45 then decide (InPath q (182 : Vertex)) else decide (InPath q (185 : Vertex)))) else (if i < 48 then (if i < 47 then decide (InPath q (186 : Vertex)) else decide (InPath q (187 : Vertex))) else (if i < 49 then decide (InPath q (189 : Vertex)) else decide (InPath q (288 : Vertex))))) else (if i < 54 then (if i < 52 then (if i < 51 then decide (InPath q (289 : Vertex)) else decide (InPath q (294 : Vertex))) else (if i < 53 then decide (InPath q (295 : Vertex)) else decide (InPath q (296 : Vertex)))) else (if i < 56 then (if i < 55 then decide (InPath q (298 : Vertex)) else decide (InPath q (300 : Vertex))) else (if i < 57 then decide (InPath q (302 : Vertex)) else decide (InPath q (303 : Vertex)))))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then decide (InPath q (305 : Vertex)) else (if i < 60 then decide (InPath q (308 : Vertex)) else decide (InPath q (309 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (310 : Vertex)) else decide (InPath q (313 : Vertex))) else (if i < 64 then decide (InPath q (314 : Vertex)) else decide (InPath q (315 : Vertex))))) else (if i < 68 then (if i < 66 then decide (InPath q (317 : Vertex)) else (if i < 67 then decide (InPath q (352 : Vertex)) else decide (InPath q (353 : Vertex)))) else (if i < 70 then (if i < 69 then decide (InPath q (355 : Vertex)) else decide (InPath q (357 : Vertex))) else (if i < 71 then decide (InPath q (359 : Vertex)) else decide (InPath q (361 : Vertex)))))) else (if i < 79 then (if i < 75 then (if i < 73 then decide (InPath q (363 : Vertex)) else (if i < 74 then decide (InPath q (365 : Vertex)) else decide (InPath q (366 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (367 : Vertex)) else decide (InPath q (368 : Vertex))) else (if i < 78 then decide (InPath q (370 : Vertex)) else decide (InPath q (371 : Vertex))))) else (if i < 83 then (if i < 81 then (if i < 80 then decide (InPath q (376 : Vertex)) else decide (InPath q (378 : Vertex))) else (if i < 82 then decide (InPath q (380 : Vertex)) else decide (InPath q (381 : Vertex)))) else (if i < 85 then (if i < 84 then decide (InPath q (382 : Vertex)) else decide (InPath q (416 : Vertex))) else (if i < 86 then decide (InPath q (417 : Vertex)) else decide (InPath q (418 : Vertex))))))) else (if i < 101 then (if i < 94 then (if i < 90 then (if i < 88 then decide (InPath q (419 : Vertex)) else (if i < 89 then decide (InPath q (421 : Vertex)) else decide (InPath q (422 : Vertex)))) else (if i < 92 then (if i < 91 then decide (InPath q (423 : Vertex)) else decide (InPath q (424 : Vertex))) else (if i < 93 then decide (InPath q (425 : Vertex)) else decide (InPath q (427 : Vertex))))) else (if i < 97 then (if i < 95 then decide (InPath q (428 : Vertex)) else (if i < 96 then decide (InPath q (429 : Vertex)) else decide (InPath q (431 : Vertex)))) else (if i < 99 then (if i < 98 then decide (InPath q (432 : Vertex)) else decide (InPath q (434 : Vertex))) else (if i < 100 then decide (InPath q (435 : Vertex)) else decide (InPath q (436 : Vertex)))))) else (if i < 108 then (if i < 104 then (if i < 102 then decide (InPath q (438 : Vertex)) else (if i < 103 then decide (InPath q (440 : Vertex)) else decide (InPath q (444 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (445 : Vertex)) else decide (InPath q (446 : Vertex))) else (if i < 107 then decide (InPath q (481 : Vertex)) else decide (InPath q (482 : Vertex))))) else (if i < 112 then (if i < 110 then (if i < 109 then decide (InPath q (486 : Vertex)) else decide (InPath q (487 : Vertex))) else (if i < 111 then decide (InPath q (488 : Vertex)) else decide (InPath q (490 : Vertex)))) else (if i < 114 then (if i < 113 then decide (InPath q (492 : Vertex)) else decide (InPath q (497 : Vertex))) else (if i < 115 then decide (InPath q (500 : Vertex)) else decide (InPath q (501 : Vertex))))))))) else (if i < 174 then (if i < 145 then (if i < 130 then (if i < 123 then (if i < 119 then (if i < 117 then decide (InPath q (502 : Vertex)) else (if i < 118 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 121 then (if i < 120 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else decide (BallClauseLogic.Endpoint q (7 : Vertex))) else (if i < 122 then decide (BallClauseLogic.Endpoint q (8 : Vertex)) else decide (BallClauseLogic.Endpoint q (10 : Vertex))))) else (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (14 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else decide (BallClauseLogic.Endpoint q (17 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (20 : Vertex)) else decide (BallClauseLogic.Endpoint q (21 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (25 : Vertex)))))) else (if i < 137 then (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (26 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (27 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex)))) else (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (65 : Vertex)) else decide (BallClauseLogic.Endpoint q (69 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (73 : Vertex)) else decide (BallClauseLogic.Endpoint q (75 : Vertex))))) else (if i < 141 then (if i < 139 then (if i < 138 then decide (BallClauseLogic.Endpoint q (79 : Vertex)) else decide (BallClauseLogic.Endpoint q (97 : Vertex))) else (if i < 140 then decide (BallClauseLogic.Endpoint q (104 : Vertex)) else decide (BallClauseLogic.Endpoint q (106 : Vertex)))) else (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (110 : Vertex)) else decide (BallClauseLogic.Endpoint q (111 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (113 : Vertex)) else decide (BallClauseLogic.Endpoint q (121 : Vertex))))))) else (if i < 159 then (if i < 152 then (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (122 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (123 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (166 : Vertex)) else decide (BallClauseLogic.Endpoint q (167 : Vertex))))) else (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (170 : Vertex)) else decide (BallClauseLogic.Endpoint q (172 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (174 : Vertex)) else decide (BallClauseLogic.Endpoint q (175 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (180 : Vertex)))))) else (if i < 166 then (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (182 : Vertex)) else decide (BallClauseLogic.Endpoint q (185 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (187 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (288 : Vertex))))) else (if i < 170 then (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (289 : Vertex)) else decide (BallClauseLogic.Endpoint q (294 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (295 : Vertex)) else decide (BallClauseLogic.Endpoint q (296 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (298 : Vertex)) else decide (BallClauseLogic.Endpoint q (300 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (302 : Vertex)) else decide (BallClauseLogic.Endpoint q (303 : Vertex)))))))) else (if i < 203 then (if i < 188 then (if i < 181 then (if i < 177 then (if i < 175 then decide (BallClauseLogic.Endpoint q (305 : Vertex)) else (if i < 176 then decide (BallClauseLogic.Endpoint q (308 : Vertex)) else decide (BallClauseLogic.Endpoint q (309 : Vertex)))) else (if i < 179 then (if i < 178 then decide (BallClauseLogic.Endpoint q (310 : Vertex)) else decide (BallClauseLogic.Endpoint q (313 : Vertex))) else (if i < 180 then decide (BallClauseLogic.Endpoint q (314 : Vertex)) else decide (BallClauseLogic.Endpoint q (315 : Vertex))))) else (if i < 184 then (if i < 182 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else (if i < 183 then decide (BallClauseLogic.Endpoint q (352 : Vertex)) else decide (BallClauseLogic.Endpoint q (353 : Vertex)))) else (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (355 : Vertex)) else decide (BallClauseLogic.Endpoint q (357 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (361 : Vertex)))))) else (if i < 195 then (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (363 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (365 : Vertex)) else decide (BallClauseLogic.Endpoint q (366 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (367 : Vertex)) else decide (BallClauseLogic.Endpoint q (368 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (370 : Vertex)) else decide (BallClauseLogic.Endpoint q (371 : Vertex))))) else (if i < 199 then (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (376 : Vertex)) else decide (BallClauseLogic.Endpoint q (378 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (380 : Vertex)) else decide (BallClauseLogic.Endpoint q (381 : Vertex)))) else (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (382 : Vertex)) else decide (BallClauseLogic.Endpoint q (416 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (417 : Vertex)) else decide (BallClauseLogic.Endpoint q (418 : Vertex))))))) else (if i < 218 then (if i < 210 then (if i < 206 then (if i < 204 then decide (BallClauseLogic.Endpoint q (419 : Vertex)) else (if i < 205 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex)))) else (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))))) else (if i < 214 then (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else decide (BallClauseLogic.Endpoint q (429 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (431 : Vertex)) else decide (BallClauseLogic.Endpoint q (432 : Vertex)))) else (if i < 216 then (if i < 215 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex))) else (if i < 217 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (438 : Vertex)))))) else (if i < 225 then (if i < 221 then (if i < 219 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else (if i < 220 then decide (BallClauseLogic.Endpoint q (444 : Vertex)) else decide (BallClauseLogic.Endpoint q (445 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (446 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (482 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex))))) else (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (490 : Vertex)) else decide (BallClauseLogic.Endpoint q (492 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (500 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex))))))))))
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
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count335 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171, 172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]
def count341 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]
def count343 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count347 (b : Nat → Bool) : Nat := countLit b [174, 175, 176]
def count349 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180]
def count355 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [181, 182, 183]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184, 185, 186, 187]
def count369 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [188, 189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193, 194]
def count383 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count393 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198, 199, 200, 201, 202]
def count397 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
def count399 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
def count401 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [203, 204, 205]
def count405 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count407 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209]
def count411 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206, 207, 208, 209]
def count413 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [210, 211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count421 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213, 214, 215, 216]
def count425 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]
def count427 (b : Nat → Bool) : Nat := countLit b [218, 219]
def count429 (b : Nat → Bool) : Nat := countLit b [217, 218, 219]
def count431 (b : Nat → Bool) : Nat := countLit b [220, 221]
def count433 (b : Nat → Bool) : Nat := countLit b [222, 223]
def count435 (b : Nat → Bool) : Nat := countLit b [220, 221, 222, 223]
def count437 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220, 221, 222, 223]
def count439 (b : Nat → Bool) : Nat := countLit b [224, 225]
def count441 (b : Nat → Bool) : Nat := countLit b [226, 227]
def count443 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227]
def count445 (b : Nat → Bool) : Nat := countLit b [228, 230]
def count447 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count449 (b : Nat → Bool) : Nat := countLit b [228, 230, 231, 232]
def count451 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227, 228, 230, 231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]
def count457 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]
def count459 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 232]
def count461 (b : Nat → Bool) : Nat := countLit b [3, 6]
def count463 (b : Nat → Bool) : Nat := countLit b [1, 3, 6]
def count466 (b : Nat → Bool) : Nat := countLit b [8, 9]
def count468 (b : Nat → Bool) : Nat := countLit b [10, 15]
def count470 (b : Nat → Bool) : Nat := countLit b [8, 9, 10, 15]
def count474 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 10, 15]
def count481 (b : Nat → Bool) : Nat := countLit b [17, 20]
def count483 (b : Nat → Bool) : Nat := countLit b [16, 17, 20]
def count486 (b : Nat → Bool) : Nat := countLit b [24, 26]
def count488 (b : Nat → Bool) : Nat := countLit b [27, 30]
def count490 (b : Nat → Bool) : Nat := countLit b [24, 26, 27, 30]
def count494 (b : Nat → Bool) : Nat := countLit b [16, 17, 20, 24, 26, 27, 30]
def count501 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 10, 15, 16, 17, 20, 24, 26, 27, 30]
def count515 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count517 (b : Nat → Bool) : Nat := countLit b [31, 32, 34]
def count520 (b : Nat → Bool) : Nat := countLit b [37, 38]
def count522 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count524 (b : Nat → Bool) : Nat := countLit b [37, 38, 40, 41]
def count528 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37, 38, 40, 41]
def count535 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count537 (b : Nat → Bool) : Nat := countLit b [42, 47, 48]
def count540 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count542 (b : Nat → Bool) : Nat := countLit b [54, 55]
def count544 (b : Nat → Bool) : Nat := countLit b [49, 51, 54, 55]
def count548 (b : Nat → Bool) : Nat := countLit b [42, 47, 48, 49, 51, 54, 55]
def count555 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37, 38, 40, 41, 42, 47, 48, 49, 51, 54, 55]
def count569 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 10, 15, 16, 17, 20, 24, 26, 27, 30, 31, 32, 34, 37, 38, 40, 41, 42, 47, 48, 49, 51, 54, 55]
def count597 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count599 (b : Nat → Bool) : Nat := countLit b [57, 58, 59]
def count602 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count604 (b : Nat → Bool) : Nat := countLit b [67, 70]
def count606 (b : Nat → Bool) : Nat := countLit b [64, 65, 67, 70]
def count610 (b : Nat → Bool) : Nat := countLit b [57, 58, 59, 64, 65, 67, 70]
def count617 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count619 (b : Nat → Bool) : Nat := countLit b [72, 73, 74]
def count622 (b : Nat → Bool) : Nat := countLit b [76, 78]
def count624 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count626 (b : Nat → Bool) : Nat := countLit b [76, 78, 80, 81]
def count630 (b : Nat → Bool) : Nat := countLit b [72, 73, 74, 76, 78, 80, 81]
def count637 (b : Nat → Bool) : Nat := countLit b [57, 58, 59, 64, 65, 67, 70, 72, 73, 74, 76, 78, 80, 81]
def count651 (b : Nat → Bool) : Nat := countLit b [86, 90]
def count653 (b : Nat → Bool) : Nat := countLit b [85, 86, 90]
def count656 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count658 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count660 (b : Nat → Bool) : Nat := countLit b [91, 93, 95, 97]
def count664 (b : Nat → Bool) : Nat := countLit b [85, 86, 90, 91, 93, 95, 97]
def count671 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count673 (b : Nat → Bool) : Nat := countLit b [103, 108]
def count675 (b : Nat → Bool) : Nat := countLit b [99, 101, 103, 108]
def count679 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count681 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count683 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114]
def count687 (b : Nat → Bool) : Nat := countLit b [99, 101, 103, 108, 111, 112, 113, 114]
def count695 (b : Nat → Bool) : Nat := countLit b [85, 86, 90, 91, 93, 95, 97, 99, 101, 103, 108, 111, 112, 113, 114]
def count710 (b : Nat → Bool) : Nat := countLit b [57, 58, 59, 64, 65, 67, 70, 72, 73, 74, 76, 78, 80, 81, 85, 86, 90, 91, 93, 95, 97, 99, 101, 103, 108, 111, 112, 113, 114]
def count739 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 10, 15, 16, 17, 20, 24, 26, 27, 30, 31, 32, 34, 37, 38, 40, 41, 42, 47, 48, 49, 51, 54, 55, 57, 58, 59, 64, 65, 67, 70, 72, 73, 74, 76, 78, 80, 81, 85, 86, 90, 91, 93, 95, 97, 99, 101, 103, 108, 111, 112, 113, 114]
def count781 (b : Nat → Bool) : Nat := countLit b [-3, -6]
def count783 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6]
def count786 (b : Nat → Bool) : Nat := countLit b [-8, -9]
def count788 (b : Nat → Bool) : Nat := countLit b [-10, -15]
def count790 (b : Nat → Bool) : Nat := countLit b [-8, -9, -10, -15]
def count794 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -10, -15]
def count801 (b : Nat → Bool) : Nat := countLit b [-17, -20]
def count803 (b : Nat → Bool) : Nat := countLit b [-16, -17, -20]
def count806 (b : Nat → Bool) : Nat := countLit b [-24, -26]
def count808 (b : Nat → Bool) : Nat := countLit b [-27, -30]
def count810 (b : Nat → Bool) : Nat := countLit b [-24, -26, -27, -30]
def count814 (b : Nat → Bool) : Nat := countLit b [-16, -17, -20, -24, -26, -27, -30]
def count821 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]
def count835 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count837 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34]
def count840 (b : Nat → Bool) : Nat := countLit b [-37, -38]
def count842 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count844 (b : Nat → Bool) : Nat := countLit b [-37, -38, -40, -41]
def count848 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37, -38, -40, -41]
def count855 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count857 (b : Nat → Bool) : Nat := countLit b [-42, -47, -48]
def count860 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count862 (b : Nat → Bool) : Nat := countLit b [-54, -55]
def count864 (b : Nat → Bool) : Nat := countLit b [-49, -51, -54, -55]
def count868 (b : Nat → Bool) : Nat := countLit b [-42, -47, -48, -49, -51, -54, -55]
def count875 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]
def count889 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]
def count906 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count908 (b : Nat → Bool) : Nat := countLit b [-57, -58, -59]
def count911 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count913 (b : Nat → Bool) : Nat := countLit b [-67, -70]
def count915 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67, -70]
def count919 (b : Nat → Bool) : Nat := countLit b [-57, -58, -59, -64, -65, -67, -70]
def count926 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count928 (b : Nat → Bool) : Nat := countLit b [-72, -73, -74]
def count931 (b : Nat → Bool) : Nat := countLit b [-76, -78]
def count933 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count935 (b : Nat → Bool) : Nat := countLit b [-76, -78, -80, -81]
def count939 (b : Nat → Bool) : Nat := countLit b [-72, -73, -74, -76, -78, -80, -81]
def count946 (b : Nat → Bool) : Nat := countLit b [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81]
def count960 (b : Nat → Bool) : Nat := countLit b [-86, -90]
def count962 (b : Nat → Bool) : Nat := countLit b [-85, -86, -90]
def count965 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count967 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count969 (b : Nat → Bool) : Nat := countLit b [-91, -93, -95, -97]
def count973 (b : Nat → Bool) : Nat := countLit b [-85, -86, -90, -91, -93, -95, -97]
def count980 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count982 (b : Nat → Bool) : Nat := countLit b [-103, -108]
def count984 (b : Nat → Bool) : Nat := countLit b [-99, -101, -103, -108]
def count988 (b : Nat → Bool) : Nat := countLit b [-111, -112]
def count990 (b : Nat → Bool) : Nat := countLit b [-113, -114]
def count992 (b : Nat → Bool) : Nat := countLit b [-111, -112, -113, -114]
def count996 (b : Nat → Bool) : Nat := countLit b [-99, -101, -103, -108, -111, -112, -113, -114]
def count1004 (b : Nat → Bool) : Nat := countLit b [-85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]
def count1019 (b : Nat → Bool) : Nat := countLit b [-57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]
def count1036 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30, -31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55, -57, -58, -59, -64, -65, -67, -70, -72, -73, -74, -76, -78, -80, -81, -85, -86, -90, -91, -93, -95, -97, -99, -101, -103, -108, -111, -112, -113, -114]
def count1053 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count1055 (b : Nat → Bool) : Nat := countLit b [2, 4, 5]
def count1058 (b : Nat → Bool) : Nat := countLit b [7, 11]
def count1060 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count1062 (b : Nat → Bool) : Nat := countLit b [7, 11, 12, 13]
def count1066 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 11, 12, 13]
def count1073 (b : Nat → Bool) : Nat := countLit b [18, 19]
def count1075 (b : Nat → Bool) : Nat := countLit b [14, 18, 19]
def count1078 (b : Nat → Bool) : Nat := countLit b [21, 22]
def count1080 (b : Nat → Bool) : Nat := countLit b [23, 25]
def count1082 (b : Nat → Bool) : Nat := countLit b [21, 22, 23, 25]
def count1086 (b : Nat → Bool) : Nat := countLit b [14, 18, 19, 21, 22, 23, 25]
def count1093 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 11, 12, 13, 14, 18, 19, 21, 22, 23, 25]
def count1107 (b : Nat → Bool) : Nat := countLit b [29, 33]
def count1109 (b : Nat → Bool) : Nat := countLit b [28, 29, 33]
def count1112 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count1114 (b : Nat → Bool) : Nat := countLit b [39, 43]
def count1116 (b : Nat → Bool) : Nat := countLit b [35, 36, 39, 43]
def count1120 (b : Nat → Bool) : Nat := countLit b [28, 29, 33, 35, 36, 39, 43]
def count1127 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count1129 (b : Nat → Bool) : Nat := countLit b [46, 50]
def count1131 (b : Nat → Bool) : Nat := countLit b [44, 45, 46, 50]
def count1135 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count1137 (b : Nat → Bool) : Nat := countLit b [56, 60]
def count1139 (b : Nat → Bool) : Nat := countLit b [52, 53, 56, 60]
def count1143 (b : Nat → Bool) : Nat := countLit b [44, 45, 46, 50, 52, 53, 56, 60]
def count1151 (b : Nat → Bool) : Nat := countLit b [28, 29, 33, 35, 36, 39, 43, 44, 45, 46, 50, 52, 53, 56, 60]
def count1166 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 11, 12, 13, 14, 18, 19, 21, 22, 23, 25, 28, 29, 33, 35, 36, 39, 43, 44, 45, 46, 50, 52, 53, 56, 60]
def count1195 (b : Nat → Bool) : Nat := countLit b [62, 63]
def count1197 (b : Nat → Bool) : Nat := countLit b [61, 62, 63]
def count1200 (b : Nat → Bool) : Nat := countLit b [66, 68]
def count1202 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count1204 (b : Nat → Bool) : Nat := countLit b [66, 68, 69, 71]
def count1208 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 66, 68, 69, 71]
def count1215 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count1217 (b : Nat → Bool) : Nat := countLit b [79, 82]
def count1219 (b : Nat → Bool) : Nat := countLit b [75, 77, 79, 82]
def count1223 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count1225 (b : Nat → Bool) : Nat := countLit b [87, 88]
def count1227 (b : Nat → Bool) : Nat := countLit b [83, 84, 87, 88]
def count1231 (b : Nat → Bool) : Nat := countLit b [75, 77, 79, 82, 83, 84, 87, 88]
def count1239 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 66, 68, 69, 71, 75, 77, 79, 82, 83, 84, 87, 88]
def count1254 (b : Nat → Bool) : Nat := countLit b [92, 94]
def count1256 (b : Nat → Bool) : Nat := countLit b [89, 92, 94]
def count1259 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count1261 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count1263 (b : Nat → Bool) : Nat := countLit b [96, 98, 100, 102]
def count1267 (b : Nat → Bool) : Nat := countLit b [89, 92, 94, 96, 98, 100, 102]
def count1274 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count1276 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count1278 (b : Nat → Bool) : Nat := countLit b [104, 105, 106, 107]
def count1282 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count1284 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count1286 (b : Nat → Bool) : Nat := countLit b [109, 110, 115, 116]
def count1290 (b : Nat → Bool) : Nat := countLit b [104, 105, 106, 107, 109, 110, 115, 116]
def count1298 (b : Nat → Bool) : Nat := countLit b [89, 92, 94, 96, 98, 100, 102, 104, 105, 106, 107, 109, 110, 115, 116]
def count1313 (b : Nat → Bool) : Nat := countLit b [61, 62, 63, 66, 68, 69, 71, 75, 77, 79, 82, 83, 84, 87, 88, 89, 92, 94, 96, 98, 100, 102, 104, 105, 106, 107, 109, 110, 115, 116]
def count1343 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 11, 12, 13, 14, 18, 19, 21, 22, 23, 25, 28, 29, 33, 35, 36, 39, 43, 44, 45, 46, 50, 52, 53, 56, 60, 61, 62, 63, 66, 68, 69, 71, 75, 77, 79, 82, 83, 84, 87, 88, 89, 92, 94, 96, 98, 100, 102, 104, 105, 106, 107, 109, 110, 115, 116]
def count1385 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1387 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5]
def count1390 (b : Nat → Bool) : Nat := countLit b [-7, -11]
def count1392 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count1394 (b : Nat → Bool) : Nat := countLit b [-7, -11, -12, -13]
def count1398 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -11, -12, -13]
def count1405 (b : Nat → Bool) : Nat := countLit b [-18, -19]
def count1407 (b : Nat → Bool) : Nat := countLit b [-14, -18, -19]
def count1410 (b : Nat → Bool) : Nat := countLit b [-21, -22]
def count1412 (b : Nat → Bool) : Nat := countLit b [-23, -25]
def count1414 (b : Nat → Bool) : Nat := countLit b [-21, -22, -23, -25]
def count1418 (b : Nat → Bool) : Nat := countLit b [-14, -18, -19, -21, -22, -23, -25]
def count1425 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -11, -12, -13, -14, -18, -19, -21, -22, -23, -25]
def count1439 (b : Nat → Bool) : Nat := countLit b [-29, -33]
def count1441 (b : Nat → Bool) : Nat := countLit b [-28, -29, -33]
def count1444 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count1446 (b : Nat → Bool) : Nat := countLit b [-39, -43]
def count1448 (b : Nat → Bool) : Nat := countLit b [-35, -36, -39, -43]
def count1452 (b : Nat → Bool) : Nat := countLit b [-28, -29, -33, -35, -36, -39, -43]
def count1459 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count1461 (b : Nat → Bool) : Nat := countLit b [-46, -50]
def count1463 (b : Nat → Bool) : Nat := countLit b [-44, -45, -46, -50]
def count1467 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count1469 (b : Nat → Bool) : Nat := countLit b [-56, -60]
def count1471 (b : Nat → Bool) : Nat := countLit b [-52, -53, -56, -60]
def count1475 (b : Nat → Bool) : Nat := countLit b [-44, -45, -46, -50, -52, -53, -56, -60]
def count1483 (b : Nat → Bool) : Nat := countLit b [-28, -29, -33, -35, -36, -39, -43, -44, -45, -46, -50, -52, -53, -56, -60]
def count1498 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -11, -12, -13, -14, -18, -19, -21, -22, -23, -25, -28, -29, -33, -35, -36, -39, -43, -44, -45, -46, -50, -52, -53, -56, -60]
def count1517 (b : Nat → Bool) : Nat := countLit b [-62, -63]
def count1519 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63]
def count1522 (b : Nat → Bool) : Nat := countLit b [-66, -68]
def count1524 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count1526 (b : Nat → Bool) : Nat := countLit b [-66, -68, -69, -71]
def count1530 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -66, -68, -69, -71]
def count1537 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count1539 (b : Nat → Bool) : Nat := countLit b [-79, -82]
def count1541 (b : Nat → Bool) : Nat := countLit b [-75, -77, -79, -82]
def count1545 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count1547 (b : Nat → Bool) : Nat := countLit b [-87, -88]
def count1549 (b : Nat → Bool) : Nat := countLit b [-83, -84, -87, -88]
def count1553 (b : Nat → Bool) : Nat := countLit b [-75, -77, -79, -82, -83, -84, -87, -88]
def count1561 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -66, -68, -69, -71, -75, -77, -79, -82, -83, -84, -87, -88]
def count1576 (b : Nat → Bool) : Nat := countLit b [-92, -94]
def count1578 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94]
def count1581 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count1583 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count1585 (b : Nat → Bool) : Nat := countLit b [-96, -98, -100, -102]
def count1589 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94, -96, -98, -100, -102]
def count1596 (b : Nat → Bool) : Nat := countLit b [-104, -105]
def count1598 (b : Nat → Bool) : Nat := countLit b [-106, -107]
def count1600 (b : Nat → Bool) : Nat := countLit b [-104, -105, -106, -107]
def count1604 (b : Nat → Bool) : Nat := countLit b [-109, -110]
def count1606 (b : Nat → Bool) : Nat := countLit b [-115, -116]
def count1608 (b : Nat → Bool) : Nat := countLit b [-109, -110, -115, -116]
def count1612 (b : Nat → Bool) : Nat := countLit b [-104, -105, -106, -107, -109, -110, -115, -116]
def count1620 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94, -96, -98, -100, -102, -104, -105, -106, -107, -109, -110, -115, -116]
def count1635 (b : Nat → Bool) : Nat := countLit b [-61, -62, -63, -66, -68, -69, -71, -75, -77, -79, -82, -83, -84, -87, -88, -89, -92, -94, -96, -98, -100, -102, -104, -105, -106, -107, -109, -110, -115, -116]
def count1654 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -11, -12, -13, -14, -18, -19, -21, -22, -23, -25, -28, -29, -33, -35, -36, -39, -43, -44, -45, -46, -50, -52, -53, -56, -60, -61, -62, -63, -66, -68, -69, -71, -75, -77, -79, -82, -83, -84, -87, -88, -89, -92, -94, -96, -98, -100, -102, -104, -105, -106, -107, -109, -110, -115, -116]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 836 then (if i < 418 then (if i < 209 then (if i < 104 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 19 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 17 then b 16 else (if i < 18 then b 17 else b 18))) else (if i < 22 then (if i < 20 then b 19 else (if i < 21 then b 20 else b 21)) else (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else b 25))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31))) else (if i < 35 then (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)) else (if i < 37 then (if i < 36 then b 35 else b 36) else (if i < 38 then b 37 else b 38)))) else (if i < 45 then (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44))) else (if i < 48 then (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)) else (if i < 50 then (if i < 49 then b 48 else b 49) else (if i < 51 then b 50 else b 51)))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then b 52 else (if i < 54 then b 53 else b 54)) else (if i < 56 then b 55 else (if i < 57 then b 56 else b 57))) else (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else b 64)))) else (if i < 71 then (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 69 then b 68 else (if i < 70 then b 69 else b 70))) else (if i < 74 then (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)) else (if i < 76 then (if i < 75 then b 74 else b 75) else (if i < 77 then b 76 else b 77))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90)))) else (if i < 97 then (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 95 then b 94 else (if i < 96 then b 95 else b 96))) else (if i < 100 then (if i < 98 then b 97 else (if i < 99 then b 98 else b 99)) else (if i < 102 then (if i < 101 then b 100 else b 101) else (if i < 103 then b 102 else b 103))))))) else (if i < 156 then (if i < 130 then (if i < 117 then (if i < 110 then (if i < 107 then (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)) else (if i < 108 then b 107 else (if i < 109 then b 108 else b 109))) else (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 115 then (if i < 114 then b 113 else b 114) else (if i < 116 then b 115 else b 116)))) else (if i < 123 then (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122))) else (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else b 129))))) else (if i < 143 then (if i < 136 then (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 134 then b 133 else (if i < 135 then b 134 else b 135))) else (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 141 then (if i < 140 then b 139 else b 140) else (if i < 142 then b 141 else b 142)))) else (if i < 149 then (if i < 146 then (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)) else (if i < 147 then b 146 else (if i < 148 then b 147 else b 148))) else (if i < 152 then (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)) else (if i < 154 then (if i < 153 then b 152 else b 153) else (if i < 155 then b 154 else b 155)))))) else (if i < 182 then (if i < 169 then (if i < 162 then (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 167 then (if i < 166 then b 165 else b 166) else (if i < 168 then b 167 else b 168)))) else (if i < 175 then (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174))) else (if i < 178 then (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)) else (if i < 180 then (if i < 179 then b 178 else b 179) else (if i < 181 then b 180 else b 181))))) else (if i < 195 then (if i < 188 then (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187))) else (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else b 194)))) else (if i < 202 then (if i < 198 then (if i < 196 then b 195 else (if i < 197 then b 196 else b 197)) else (if i < 200 then (if i < 199 then b 198 else b 199) else (if i < 201 then b 200 else b 201))) else (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 207 then (if i < 206 then b 205 else b 206) else (if i < 208 then b 207 else b 208)))))))) else (if i < 313 then (if i < 261 then (if i < 235 then (if i < 222 then (if i < 215 then (if i < 212 then (if i < 210 then b 209 else (if i < 211 then b 210 else b 211)) else (if i < 213 then b 212 else (if i < 214 then b 213 else b 214))) else (if i < 218 then (if i < 216 then b 215 else (if i < 217 then b 216 else b 217)) else (if i < 220 then (if i < 219 then b 218 else b 219) else (if i < 221 then b 220 else b 221)))) else (if i < 228 then (if i < 225 then (if i < 223 then b 222 else (if i < 224 then b 223 else b 224)) else (if i < 226 then b 225 else (if i < 227 then b 226 else b 227))) else (if i < 231 then (if i < 229 then b 228 else (if i < 230 then b 229 else b 230)) else (if i < 233 then (if i < 232 then b 231 else b 232) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))))) else (if i < 248 then (if i < 241 then (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))) else (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 246 then (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))))) else (if i < 254 then (if i < 251 then (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 252 then decide (1 ≤ count251 b) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)))) else (if i < 257 then (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b))) else (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))))))) else (if i < 287 then (if i < 274 then (if i < 267 then (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))) else (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 272 then (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))))) else (if i < 280 then (if i < 277 then (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))) else (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)))) else (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))))) else (if i < 300 then (if i < 293 then (if i < 290 then (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))) else (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))) else (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 298 then (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))))) else (if i < 306 then (if i < 303 then (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b))) else (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))) else (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))))))) else (if i < 365 then (if i < 339 then (if i < 326 then (if i < 319 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))) else (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 324 then (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))))) else (if i < 332 then (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 335 then (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))))) else (if i < 352 then (if i < 345 then (if i < 342 then (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))) else (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)))) else (if i < 348 then (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))) else (if i < 350 then (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b))))) else (if i < 358 then (if i < 355 then (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b))) else (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b)))) else (if i < 361 then (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))) else (if i < 363 then (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b))))))) else (if i < 391 then (if i < 378 then (if i < 371 then (if i < 368 then (if i < 366 then decide (1 ≤ count365 b) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))) else (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 376 then (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))))) else (if i < 384 then (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)))) else (if i < 387 then (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b))) else (if i < 389 then (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))))) else (if i < 404 then (if i < 397 then (if i < 394 then (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)))) else (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))))) else (if i < 411 then (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)))) else (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 416 then (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)))))))))) else (if i < 627 then (if i < 522 then (if i < 470 then (if i < 444 then (if i < 431 then (if i < 424 then (if i < 421 then (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))) else (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)))) else (if i < 427 then (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b))) else (if i < 429 then (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))))) else (if i < 437 then (if i < 434 then (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))) else (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))) else (if i < 440 then (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))) else (if i < 442 then (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)))))) else (if i < 457 then (if i < 450 then (if i < 447 then (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b))) else (if i < 448 then decide (1 ≤ count447 b) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b)))) else (if i < 453 then (if i < 451 then decide (2 ≤ count449 b) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))) else (if i < 455 then (if i < 454 then decide (1 ≤ count453 b) else decide (2 ≤ count453 b)) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))))) else (if i < 463 then (if i < 460 then (if i < 458 then decide (1 ≤ count457 b) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b))) else (if i < 461 then decide (2 ≤ count459 b) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)))) else (if i < 466 then (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (3 ≤ count463 b))) else (if i < 468 then (if i < 467 then decide (1 ≤ count466 b) else decide (2 ≤ count466 b)) else (if i < 469 then decide (1 ≤ count468 b) else decide (2 ≤ count468 b))))))) else (if i < 496 then (if i < 483 then (if i < 476 then (if i < 473 then (if i < 471 then decide (1 ≤ count470 b) else (if i < 472 then decide (2 ≤ count470 b) else decide (3 ≤ count470 b))) else (if i < 474 then decide (4 ≤ count470 b) else (if i < 475 then decide (1 ≤ count474 b) else decide (2 ≤ count474 b)))) else (if i < 479 then (if i < 477 then decide (3 ≤ count474 b) else (if i < 478 then decide (4 ≤ count474 b) else decide (5 ≤ count474 b))) else (if i < 481 then (if i < 480 then decide (6 ≤ count474 b) else decide (7 ≤ count474 b)) else (if i < 482 then decide (1 ≤ count481 b) else decide (2 ≤ count481 b))))) else (if i < 489 then (if i < 486 then (if i < 484 then decide (1 ≤ count483 b) else (if i < 485 then decide (2 ≤ count483 b) else decide (3 ≤ count483 b))) else (if i < 487 then decide (1 ≤ count486 b) else (if i < 488 then decide (2 ≤ count486 b) else decide (1 ≤ count488 b)))) else (if i < 492 then (if i < 490 then decide (2 ≤ count488 b) else (if i < 491 then decide (1 ≤ count490 b) else decide (2 ≤ count490 b))) else (if i < 494 then (if i < 493 then decide (3 ≤ count490 b) else decide (4 ≤ count490 b)) else (if i < 495 then decide (1 ≤ count494 b) else decide (2 ≤ count494 b)))))) else (if i < 509 then (if i < 502 then (if i < 499 then (if i < 497 then decide (3 ≤ count494 b) else (if i < 498 then decide (4 ≤ count494 b) else decide (5 ≤ count494 b))) else (if i < 500 then decide (6 ≤ count494 b) else (if i < 501 then decide (7 ≤ count494 b) else decide (1 ≤ count501 b)))) else (if i < 505 then (if i < 503 then decide (2 ≤ count501 b) else (if i < 504 then decide (3 ≤ count501 b) else decide (4 ≤ count501 b))) else (if i < 507 then (if i < 506 then decide (5 ≤ count501 b) else decide (6 ≤ count501 b)) else (if i < 508 then decide (7 ≤ count501 b) else decide (8 ≤ count501 b))))) else (if i < 515 then (if i < 512 then (if i < 510 then decide (9 ≤ count501 b) else (if i < 511 then decide (10 ≤ count501 b) else decide (11 ≤ count501 b))) else (if i < 513 then decide (12 ≤ count501 b) else (if i < 514 then decide (13 ≤ count501 b) else decide (14 ≤ count501 b)))) else (if i < 518 then (if i < 516 then decide (1 ≤ count515 b) else (if i < 517 then decide (2 ≤ count515 b) else decide (1 ≤ count517 b))) else (if i < 520 then (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b)) else (if i < 521 then decide (1 ≤ count520 b) else decide (2 ≤ count520 b)))))))) else (if i < 574 then (if i < 548 then (if i < 535 then (if i < 528 then (if i < 525 then (if i < 523 then decide (1 ≤ count522 b) else (if i < 524 then decide (2 ≤ count522 b) else decide (1 ≤ count524 b))) else (if i < 526 then decide (2 ≤ count524 b) else (if i < 527 then decide (3 ≤ count524 b) else decide (4 ≤ count524 b)))) else (if i < 531 then (if i < 529 then decide (1 ≤ count528 b) else (if i < 530 then decide (2 ≤ count528 b) else decide (3 ≤ count528 b))) else (if i < 533 then (if i < 532 then decide (4 ≤ count528 b) else decide (5 ≤ count528 b)) else (if i < 534 then decide (6 ≤ count528 b) else decide (7 ≤ count528 b))))) else (if i < 541 then (if i < 538 then (if i < 536 then decide (1 ≤ count535 b) else (if i < 537 then decide (2 ≤ count535 b) else decide (1 ≤ count537 b))) else (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (3 ≤ count537 b) else decide (1 ≤ count540 b)))) else (if i < 544 then (if i < 542 then decide (2 ≤ count540 b) else (if i < 543 then decide (1 ≤ count542 b) else decide (2 ≤ count542 b))) else (if i < 546 then (if i < 545 then decide (1 ≤ count544 b) else decide (2 ≤ count544 b)) else (if i < 547 then decide (3 ≤ count544 b) else decide (4 ≤ count544 b)))))) else (if i < 561 then (if i < 554 then (if i < 551 then (if i < 549 then decide (1 ≤ count548 b) else (if i < 550 then decide (2 ≤ count548 b) else decide (3 ≤ count548 b))) else (if i < 552 then decide (4 ≤ count548 b) else (if i < 553 then decide (5 ≤ count548 b) else decide (6 ≤ count548 b)))) else (if i < 557 then (if i < 555 then decide (7 ≤ count548 b) else (if i < 556 then decide (1 ≤ count555 b) else decide (2 ≤ count555 b))) else (if i < 559 then (if i < 558 then decide (3 ≤ count555 b) else decide (4 ≤ count555 b)) else (if i < 560 then decide (5 ≤ count555 b) else decide (6 ≤ count555 b))))) else (if i < 567 then (if i < 564 then (if i < 562 then decide (7 ≤ count555 b) else (if i < 563 then decide (8 ≤ count555 b) else decide (9 ≤ count555 b))) else (if i < 565 then decide (10 ≤ count555 b) else (if i < 566 then decide (11 ≤ count555 b) else decide (12 ≤ count555 b)))) else (if i < 570 then (if i < 568 then decide (13 ≤ count555 b) else (if i < 569 then decide (14 ≤ count555 b) else decide (1 ≤ count569 b))) else (if i < 572 then (if i < 571 then decide (2 ≤ count569 b) else decide (3 ≤ count569 b)) else (if i < 573 then decide (4 ≤ count569 b) else decide (5 ≤ count569 b))))))) else (if i < 600 then (if i < 587 then (if i < 580 then (if i < 577 then (if i < 575 then decide (6 ≤ count569 b) else (if i < 576 then decide (7 ≤ count569 b) else decide (8 ≤ count569 b))) else (if i < 578 then decide (9 ≤ count569 b) else (if i < 579 then decide (10 ≤ count569 b) else decide (11 ≤ count569 b)))) else (if i < 583 then (if i < 581 then decide (12 ≤ count569 b) else (if i < 582 then decide (13 ≤ count569 b) else decide (14 ≤ count569 b))) else (if i < 585 then (if i < 584 then decide (15 ≤ count569 b) else decide (16 ≤ count569 b)) else (if i < 586 then decide (17 ≤ count569 b) else decide (18 ≤ count569 b))))) else (if i < 593 then (if i < 590 then (if i < 588 then decide (19 ≤ count569 b) else (if i < 589 then decide (20 ≤ count569 b) else decide (21 ≤ count569 b))) else (if i < 591 then decide (22 ≤ count569 b) else (if i < 592 then decide (23 ≤ count569 b) else decide (24 ≤ count569 b)))) else (if i < 596 then (if i < 594 then decide (25 ≤ count569 b) else (if i < 595 then decide (26 ≤ count569 b) else decide (27 ≤ count569 b))) else (if i < 598 then (if i < 597 then decide (28 ≤ count569 b) else decide (1 ≤ count597 b)) else (if i < 599 then decide (2 ≤ count597 b) else decide (1 ≤ count599 b)))))) else (if i < 613 then (if i < 606 then (if i < 603 then (if i < 601 then decide (2 ≤ count599 b) else (if i < 602 then decide (3 ≤ count599 b) else decide (1 ≤ count602 b))) else (if i < 604 then decide (2 ≤ count602 b) else (if i < 605 then decide (1 ≤ count604 b) else decide (2 ≤ count604 b)))) else (if i < 609 then (if i < 607 then decide (1 ≤ count606 b) else (if i < 608 then decide (2 ≤ count606 b) else decide (3 ≤ count606 b))) else (if i < 611 then (if i < 610 then decide (4 ≤ count606 b) else decide (1 ≤ count610 b)) else (if i < 612 then decide (2 ≤ count610 b) else decide (3 ≤ count610 b))))) else (if i < 620 then (if i < 616 then (if i < 614 then decide (4 ≤ count610 b) else (if i < 615 then decide (5 ≤ count610 b) else decide (6 ≤ count610 b))) else (if i < 618 then (if i < 617 then decide (7 ≤ count610 b) else decide (1 ≤ count617 b)) else (if i < 619 then decide (2 ≤ count617 b) else decide (1 ≤ count619 b)))) else (if i < 623 then (if i < 621 then decide (2 ≤ count619 b) else (if i < 622 then decide (3 ≤ count619 b) else decide (1 ≤ count622 b))) else (if i < 625 then (if i < 624 then decide (2 ≤ count622 b) else decide (1 ≤ count624 b)) else (if i < 626 then decide (2 ≤ count624 b) else decide (1 ≤ count626 b))))))))) else (if i < 731 then (if i < 679 then (if i < 653 then (if i < 640 then (if i < 633 then (if i < 630 then (if i < 628 then decide (2 ≤ count626 b) else (if i < 629 then decide (3 ≤ count626 b) else decide (4 ≤ count626 b))) else (if i < 631 then decide (1 ≤ count630 b) else (if i < 632 then decide (2 ≤ count630 b) else decide (3 ≤ count630 b)))) else (if i < 636 then (if i < 634 then decide (4 ≤ count630 b) else (if i < 635 then decide (5 ≤ count630 b) else decide (6 ≤ count630 b))) else (if i < 638 then (if i < 637 then decide (7 ≤ count630 b) else decide (1 ≤ count637 b)) else (if i < 639 then decide (2 ≤ count637 b) else decide (3 ≤ count637 b))))) else (if i < 646 then (if i < 643 then (if i < 641 then decide (4 ≤ count637 b) else (if i < 642 then decide (5 ≤ count637 b) else decide (6 ≤ count637 b))) else (if i < 644 then decide (7 ≤ count637 b) else (if i < 645 then decide (8 ≤ count637 b) else decide (9 ≤ count637 b)))) else (if i < 649 then (if i < 647 then decide (10 ≤ count637 b) else (if i < 648 then decide (11 ≤ count637 b) else decide (12 ≤ count637 b))) else (if i < 651 then (if i < 650 then decide (13 ≤ count637 b) else decide (14 ≤ count637 b)) else (if i < 652 then decide (1 ≤ count651 b) else decide (2 ≤ count651 b)))))) else (if i < 666 then (if i < 659 then (if i < 656 then (if i < 654 then decide (1 ≤ count653 b) else (if i < 655 then decide (2 ≤ count653 b) else decide (3 ≤ count653 b))) else (if i < 657 then decide (1 ≤ count656 b) else (if i < 658 then decide (2 ≤ count656 b) else decide (1 ≤ count658 b)))) else (if i < 662 then (if i < 660 then decide (2 ≤ count658 b) else (if i < 661 then decide (1 ≤ count660 b) else decide (2 ≤ count660 b))) else (if i < 664 then (if i < 663 then decide (3 ≤ count660 b) else decide (4 ≤ count660 b)) else (if i < 665 then decide (1 ≤ count664 b) else decide (2 ≤ count664 b))))) else (if i < 672 then (if i < 669 then (if i < 667 then decide (3 ≤ count664 b) else (if i < 668 then decide (4 ≤ count664 b) else decide (5 ≤ count664 b))) else (if i < 670 then decide (6 ≤ count664 b) else (if i < 671 then decide (7 ≤ count664 b) else decide (1 ≤ count671 b)))) else (if i < 675 then (if i < 673 then decide (2 ≤ count671 b) else (if i < 674 then decide (1 ≤ count673 b) else decide (2 ≤ count673 b))) else (if i < 677 then (if i < 676 then decide (1 ≤ count675 b) else decide (2 ≤ count675 b)) else (if i < 678 then decide (3 ≤ count675 b) else decide (4 ≤ count675 b))))))) else (if i < 705 then (if i < 692 then (if i < 685 then (if i < 682 then (if i < 680 then decide (1 ≤ count679 b) else (if i < 681 then decide (2 ≤ count679 b) else decide (1 ≤ count681 b))) else (if i < 683 then decide (2 ≤ count681 b) else (if i < 684 then decide (1 ≤ count683 b) else decide (2 ≤ count683 b)))) else (if i < 688 then (if i < 686 then decide (3 ≤ count683 b) else (if i < 687 then decide (4 ≤ count683 b) else decide (1 ≤ count687 b))) else (if i < 690 then (if i < 689 then decide (2 ≤ count687 b) else decide (3 ≤ count687 b)) else (if i < 691 then decide (4 ≤ count687 b) else decide (5 ≤ count687 b))))) else (if i < 698 then (if i < 695 then (if i < 693 then decide (6 ≤ count687 b) else (if i < 694 then decide (7 ≤ count687 b) else decide (8 ≤ count687 b))) else (if i < 696 then decide (1 ≤ count695 b) else (if i < 697 then decide (2 ≤ count695 b) else decide (3 ≤ count695 b)))) else (if i < 701 then (if i < 699 then decide (4 ≤ count695 b) else (if i < 700 then decide (5 ≤ count695 b) else decide (6 ≤ count695 b))) else (if i < 703 then (if i < 702 then decide (7 ≤ count695 b) else decide (8 ≤ count695 b)) else (if i < 704 then decide (9 ≤ count695 b) else decide (10 ≤ count695 b)))))) else (if i < 718 then (if i < 711 then (if i < 708 then (if i < 706 then decide (11 ≤ count695 b) else (if i < 707 then decide (12 ≤ count695 b) else decide (13 ≤ count695 b))) else (if i < 709 then decide (14 ≤ count695 b) else (if i < 710 then decide (15 ≤ count695 b) else decide (1 ≤ count710 b)))) else (if i < 714 then (if i < 712 then decide (2 ≤ count710 b) else (if i < 713 then decide (3 ≤ count710 b) else decide (4 ≤ count710 b))) else (if i < 716 then (if i < 715 then decide (5 ≤ count710 b) else decide (6 ≤ count710 b)) else (if i < 717 then decide (7 ≤ count710 b) else decide (8 ≤ count710 b))))) else (if i < 724 then (if i < 721 then (if i < 719 then decide (9 ≤ count710 b) else (if i < 720 then decide (10 ≤ count710 b) else decide (11 ≤ count710 b))) else (if i < 722 then decide (12 ≤ count710 b) else (if i < 723 then decide (13 ≤ count710 b) else decide (14 ≤ count710 b)))) else (if i < 727 then (if i < 725 then decide (15 ≤ count710 b) else (if i < 726 then decide (16 ≤ count710 b) else decide (17 ≤ count710 b))) else (if i < 729 then (if i < 728 then decide (18 ≤ count710 b) else decide (19 ≤ count710 b)) else (if i < 730 then decide (20 ≤ count710 b) else decide (21 ≤ count710 b)))))))) else (if i < 783 then (if i < 757 then (if i < 744 then (if i < 737 then (if i < 734 then (if i < 732 then decide (22 ≤ count710 b) else (if i < 733 then decide (23 ≤ count710 b) else decide (24 ≤ count710 b))) else (if i < 735 then decide (25 ≤ count710 b) else (if i < 736 then decide (26 ≤ count710 b) else decide (27 ≤ count710 b)))) else (if i < 740 then (if i < 738 then decide (28 ≤ count710 b) else (if i < 739 then decide (29 ≤ count710 b) else decide (1 ≤ count739 b))) else (if i < 742 then (if i < 741 then decide (2 ≤ count739 b) else decide (3 ≤ count739 b)) else (if i < 743 then decide (4 ≤ count739 b) else decide (5 ≤ count739 b))))) else (if i < 750 then (if i < 747 then (if i < 745 then decide (6 ≤ count739 b) else (if i < 746 then decide (7 ≤ count739 b) else decide (8 ≤ count739 b))) else (if i < 748 then decide (9 ≤ count739 b) else (if i < 749 then decide (10 ≤ count739 b) else decide (11 ≤ count739 b)))) else (if i < 753 then (if i < 751 then decide (12 ≤ count739 b) else (if i < 752 then decide (13 ≤ count739 b) else decide (14 ≤ count739 b))) else (if i < 755 then (if i < 754 then decide (15 ≤ count739 b) else decide (16 ≤ count739 b)) else (if i < 756 then decide (17 ≤ count739 b) else decide (18 ≤ count739 b)))))) else (if i < 770 then (if i < 763 then (if i < 760 then (if i < 758 then decide (19 ≤ count739 b) else (if i < 759 then decide (20 ≤ count739 b) else decide (21 ≤ count739 b))) else (if i < 761 then decide (22 ≤ count739 b) else (if i < 762 then decide (23 ≤ count739 b) else decide (24 ≤ count739 b)))) else (if i < 766 then (if i < 764 then decide (25 ≤ count739 b) else (if i < 765 then decide (26 ≤ count739 b) else decide (27 ≤ count739 b))) else (if i < 768 then (if i < 767 then decide (28 ≤ count739 b) else decide (29 ≤ count739 b)) else (if i < 769 then decide (30 ≤ count739 b) else decide (31 ≤ count739 b))))) else (if i < 776 then (if i < 773 then (if i < 771 then decide (32 ≤ count739 b) else (if i < 772 then decide (33 ≤ count739 b) else decide (34 ≤ count739 b))) else (if i < 774 then decide (35 ≤ count739 b) else (if i < 775 then decide (36 ≤ count739 b) else decide (37 ≤ count739 b)))) else (if i < 779 then (if i < 777 then decide (38 ≤ count739 b) else (if i < 778 then decide (39 ≤ count739 b) else decide (40 ≤ count739 b))) else (if i < 781 then (if i < 780 then decide (41 ≤ count739 b) else decide (42 ≤ count739 b)) else (if i < 782 then decide (1 ≤ count781 b) else decide (2 ≤ count781 b))))))) else (if i < 809 then (if i < 796 then (if i < 789 then (if i < 786 then (if i < 784 then decide (1 ≤ count783 b) else (if i < 785 then decide (2 ≤ count783 b) else decide (3 ≤ count783 b))) else (if i < 787 then decide (1 ≤ count786 b) else (if i < 788 then decide (2 ≤ count786 b) else decide (1 ≤ count788 b)))) else (if i < 792 then (if i < 790 then decide (2 ≤ count788 b) else (if i < 791 then decide (1 ≤ count790 b) else decide (2 ≤ count790 b))) else (if i < 794 then (if i < 793 then decide (3 ≤ count790 b) else decide (4 ≤ count790 b)) else (if i < 795 then decide (1 ≤ count794 b) else decide (2 ≤ count794 b))))) else (if i < 802 then (if i < 799 then (if i < 797 then decide (3 ≤ count794 b) else (if i < 798 then decide (4 ≤ count794 b) else decide (5 ≤ count794 b))) else (if i < 800 then decide (6 ≤ count794 b) else (if i < 801 then decide (7 ≤ count794 b) else decide (1 ≤ count801 b)))) else (if i < 805 then (if i < 803 then decide (2 ≤ count801 b) else (if i < 804 then decide (1 ≤ count803 b) else decide (2 ≤ count803 b))) else (if i < 807 then (if i < 806 then decide (3 ≤ count803 b) else decide (1 ≤ count806 b)) else (if i < 808 then decide (2 ≤ count806 b) else decide (1 ≤ count808 b)))))) else (if i < 822 then (if i < 815 then (if i < 812 then (if i < 810 then decide (2 ≤ count808 b) else (if i < 811 then decide (1 ≤ count810 b) else decide (2 ≤ count810 b))) else (if i < 813 then decide (3 ≤ count810 b) else (if i < 814 then decide (4 ≤ count810 b) else decide (1 ≤ count814 b)))) else (if i < 818 then (if i < 816 then decide (2 ≤ count814 b) else (if i < 817 then decide (3 ≤ count814 b) else decide (4 ≤ count814 b))) else (if i < 820 then (if i < 819 then decide (5 ≤ count814 b) else decide (6 ≤ count814 b)) else (if i < 821 then decide (7 ≤ count814 b) else decide (1 ≤ count821 b))))) else (if i < 829 then (if i < 825 then (if i < 823 then decide (2 ≤ count821 b) else (if i < 824 then decide (3 ≤ count821 b) else decide (4 ≤ count821 b))) else (if i < 827 then (if i < 826 then decide (5 ≤ count821 b) else decide (6 ≤ count821 b)) else (if i < 828 then decide (7 ≤ count821 b) else decide (8 ≤ count821 b)))) else (if i < 832 then (if i < 830 then decide (9 ≤ count821 b) else (if i < 831 then decide (10 ≤ count821 b) else decide (11 ≤ count821 b))) else (if i < 834 then (if i < 833 then decide (12 ≤ count821 b) else decide (13 ≤ count821 b)) else (if i < 835 then decide (14 ≤ count821 b) else decide (1 ≤ count835 b))))))))))) else (if i < 1254 then (if i < 1045 then (if i < 940 then (if i < 888 then (if i < 862 then (if i < 849 then (if i < 842 then (if i < 839 then (if i < 837 then decide (2 ≤ count835 b) else (if i < 838 then decide (1 ≤ count837 b) else decide (2 ≤ count837 b))) else (if i < 840 then decide (3 ≤ count837 b) else (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b)))) else (if i < 845 then (if i < 843 then decide (1 ≤ count842 b) else (if i < 844 then decide (2 ≤ count842 b) else decide (1 ≤ count844 b))) else (if i < 847 then (if i < 846 then decide (2 ≤ count844 b) else decide (3 ≤ count844 b)) else (if i < 848 then decide (4 ≤ count844 b) else decide (1 ≤ count848 b))))) else (if i < 855 then (if i < 852 then (if i < 850 then decide (2 ≤ count848 b) else (if i < 851 then decide (3 ≤ count848 b) else decide (4 ≤ count848 b))) else (if i < 853 then decide (5 ≤ count848 b) else (if i < 854 then decide (6 ≤ count848 b) else decide (7 ≤ count848 b)))) else (if i < 858 then (if i < 856 then decide (1 ≤ count855 b) else (if i < 857 then decide (2 ≤ count855 b) else decide (1 ≤ count857 b))) else (if i < 860 then (if i < 859 then decide (2 ≤ count857 b) else decide (3 ≤ count857 b)) else (if i < 861 then decide (1 ≤ count860 b) else decide (2 ≤ count860 b)))))) else (if i < 875 then (if i < 868 then (if i < 865 then (if i < 863 then decide (1 ≤ count862 b) else (if i < 864 then decide (2 ≤ count862 b) else decide (1 ≤ count864 b))) else (if i < 866 then decide (2 ≤ count864 b) else (if i < 867 then decide (3 ≤ count864 b) else decide (4 ≤ count864 b)))) else (if i < 871 then (if i < 869 then decide (1 ≤ count868 b) else (if i < 870 then decide (2 ≤ count868 b) else decide (3 ≤ count868 b))) else (if i < 873 then (if i < 872 then decide (4 ≤ count868 b) else decide (5 ≤ count868 b)) else (if i < 874 then decide (6 ≤ count868 b) else decide (7 ≤ count868 b))))) else (if i < 881 then (if i < 878 then (if i < 876 then decide (1 ≤ count875 b) else (if i < 877 then decide (2 ≤ count875 b) else decide (3 ≤ count875 b))) else (if i < 879 then decide (4 ≤ count875 b) else (if i < 880 then decide (5 ≤ count875 b) else decide (6 ≤ count875 b)))) else (if i < 884 then (if i < 882 then decide (7 ≤ count875 b) else (if i < 883 then decide (8 ≤ count875 b) else decide (9 ≤ count875 b))) else (if i < 886 then (if i < 885 then decide (10 ≤ count875 b) else decide (11 ≤ count875 b)) else (if i < 887 then decide (12 ≤ count875 b) else decide (13 ≤ count875 b))))))) else (if i < 914 then (if i < 901 then (if i < 894 then (if i < 891 then (if i < 889 then decide (14 ≤ count875 b) else (if i < 890 then decide (1 ≤ count889 b) else decide (2 ≤ count889 b))) else (if i < 892 then decide (3 ≤ count889 b) else (if i < 893 then decide (4 ≤ count889 b) else decide (5 ≤ count889 b)))) else (if i < 897 then (if i < 895 then decide (6 ≤ count889 b) else (if i < 896 then decide (7 ≤ count889 b) else decide (8 ≤ count889 b))) else (if i < 899 then (if i < 898 then decide (9 ≤ count889 b) else decide (10 ≤ count889 b)) else (if i < 900 then decide (11 ≤ count889 b) else decide (12 ≤ count889 b))))) else (if i < 907 then (if i < 904 then (if i < 902 then decide (13 ≤ count889 b) else (if i < 903 then decide (14 ≤ count889 b) else decide (15 ≤ count889 b))) else (if i < 905 then decide (16 ≤ count889 b) else (if i < 906 then decide (17 ≤ count889 b) else decide (1 ≤ count906 b)))) else (if i < 910 then (if i < 908 then decide (2 ≤ count906 b) else (if i < 909 then decide (1 ≤ count908 b) else decide (2 ≤ count908 b))) else (if i < 912 then (if i < 911 then decide (3 ≤ count908 b) else decide (1 ≤ count911 b)) else (if i < 913 then decide (2 ≤ count911 b) else decide (1 ≤ count913 b)))))) else (if i < 927 then (if i < 920 then (if i < 917 then (if i < 915 then decide (2 ≤ count913 b) else (if i < 916 then decide (1 ≤ count915 b) else decide (2 ≤ count915 b))) else (if i < 918 then decide (3 ≤ count915 b) else (if i < 919 then decide (4 ≤ count915 b) else decide (1 ≤ count919 b)))) else (if i < 923 then (if i < 921 then decide (2 ≤ count919 b) else (if i < 922 then decide (3 ≤ count919 b) else decide (4 ≤ count919 b))) else (if i < 925 then (if i < 924 then decide (5 ≤ count919 b) else decide (6 ≤ count919 b)) else (if i < 926 then decide (7 ≤ count919 b) else decide (1 ≤ count926 b))))) else (if i < 933 then (if i < 930 then (if i < 928 then decide (2 ≤ count926 b) else (if i < 929 then decide (1 ≤ count928 b) else decide (2 ≤ count928 b))) else (if i < 931 then decide (3 ≤ count928 b) else (if i < 932 then decide (1 ≤ count931 b) else decide (2 ≤ count931 b)))) else (if i < 936 then (if i < 934 then decide (1 ≤ count933 b) else (if i < 935 then decide (2 ≤ count933 b) else decide (1 ≤ count935 b))) else (if i < 938 then (if i < 937 then decide (2 ≤ count935 b) else decide (3 ≤ count935 b)) else (if i < 939 then decide (4 ≤ count935 b) else decide (1 ≤ count939 b)))))))) else (if i < 992 then (if i < 966 then (if i < 953 then (if i < 946 then (if i < 943 then (if i < 941 then decide (2 ≤ count939 b) else (if i < 942 then decide (3 ≤ count939 b) else decide (4 ≤ count939 b))) else (if i < 944 then decide (5 ≤ count939 b) else (if i < 945 then decide (6 ≤ count939 b) else decide (7 ≤ count939 b)))) else (if i < 949 then (if i < 947 then decide (1 ≤ count946 b) else (if i < 948 then decide (2 ≤ count946 b) else decide (3 ≤ count946 b))) else (if i < 951 then (if i < 950 then decide (4 ≤ count946 b) else decide (5 ≤ count946 b)) else (if i < 952 then decide (6 ≤ count946 b) else decide (7 ≤ count946 b))))) else (if i < 959 then (if i < 956 then (if i < 954 then decide (8 ≤ count946 b) else (if i < 955 then decide (9 ≤ count946 b) else decide (10 ≤ count946 b))) else (if i < 957 then decide (11 ≤ count946 b) else (if i < 958 then decide (12 ≤ count946 b) else decide (13 ≤ count946 b)))) else (if i < 962 then (if i < 960 then decide (14 ≤ count946 b) else (if i < 961 then decide (1 ≤ count960 b) else decide (2 ≤ count960 b))) else (if i < 964 then (if i < 963 then decide (1 ≤ count962 b) else decide (2 ≤ count962 b)) else (if i < 965 then decide (3 ≤ count962 b) else decide (1 ≤ count965 b)))))) else (if i < 979 then (if i < 972 then (if i < 969 then (if i < 967 then decide (2 ≤ count965 b) else (if i < 968 then decide (1 ≤ count967 b) else decide (2 ≤ count967 b))) else (if i < 970 then decide (1 ≤ count969 b) else (if i < 971 then decide (2 ≤ count969 b) else decide (3 ≤ count969 b)))) else (if i < 975 then (if i < 973 then decide (4 ≤ count969 b) else (if i < 974 then decide (1 ≤ count973 b) else decide (2 ≤ count973 b))) else (if i < 977 then (if i < 976 then decide (3 ≤ count973 b) else decide (4 ≤ count973 b)) else (if i < 978 then decide (5 ≤ count973 b) else decide (6 ≤ count973 b))))) else (if i < 985 then (if i < 982 then (if i < 980 then decide (7 ≤ count973 b) else (if i < 981 then decide (1 ≤ count980 b) else decide (2 ≤ count980 b))) else (if i < 983 then decide (1 ≤ count982 b) else (if i < 984 then decide (2 ≤ count982 b) else decide (1 ≤ count984 b)))) else (if i < 988 then (if i < 986 then decide (2 ≤ count984 b) else (if i < 987 then decide (3 ≤ count984 b) else decide (4 ≤ count984 b))) else (if i < 990 then (if i < 989 then decide (1 ≤ count988 b) else decide (2 ≤ count988 b)) else (if i < 991 then decide (1 ≤ count990 b) else decide (2 ≤ count990 b))))))) else (if i < 1018 then (if i < 1005 then (if i < 998 then (if i < 995 then (if i < 993 then decide (1 ≤ count992 b) else (if i < 994 then decide (2 ≤ count992 b) else decide (3 ≤ count992 b))) else (if i < 996 then decide (4 ≤ count992 b) else (if i < 997 then decide (1 ≤ count996 b) else decide (2 ≤ count996 b)))) else (if i < 1001 then (if i < 999 then decide (3 ≤ count996 b) else (if i < 1000 then decide (4 ≤ count996 b) else decide (5 ≤ count996 b))) else (if i < 1003 then (if i < 1002 then decide (6 ≤ count996 b) else decide (7 ≤ count996 b)) else (if i < 1004 then decide (8 ≤ count996 b) else decide (1 ≤ count1004 b))))) else (if i < 1011 then (if i < 1008 then (if i < 1006 then decide (2 ≤ count1004 b) else (if i < 1007 then decide (3 ≤ count1004 b) else decide (4 ≤ count1004 b))) else (if i < 1009 then decide (5 ≤ count1004 b) else (if i < 1010 then decide (6 ≤ count1004 b) else decide (7 ≤ count1004 b)))) else (if i < 1014 then (if i < 1012 then decide (8 ≤ count1004 b) else (if i < 1013 then decide (9 ≤ count1004 b) else decide (10 ≤ count1004 b))) else (if i < 1016 then (if i < 1015 then decide (11 ≤ count1004 b) else decide (12 ≤ count1004 b)) else (if i < 1017 then decide (13 ≤ count1004 b) else decide (14 ≤ count1004 b)))))) else (if i < 1031 then (if i < 1024 then (if i < 1021 then (if i < 1019 then decide (15 ≤ count1004 b) else (if i < 1020 then decide (1 ≤ count1019 b) else decide (2 ≤ count1019 b))) else (if i < 1022 then decide (3 ≤ count1019 b) else (if i < 1023 then decide (4 ≤ count1019 b) else decide (5 ≤ count1019 b)))) else (if i < 1027 then (if i < 1025 then decide (6 ≤ count1019 b) else (if i < 1026 then decide (7 ≤ count1019 b) else decide (8 ≤ count1019 b))) else (if i < 1029 then (if i < 1028 then decide (9 ≤ count1019 b) else decide (10 ≤ count1019 b)) else (if i < 1030 then decide (11 ≤ count1019 b) else decide (12 ≤ count1019 b))))) else (if i < 1038 then (if i < 1034 then (if i < 1032 then decide (13 ≤ count1019 b) else (if i < 1033 then decide (14 ≤ count1019 b) else decide (15 ≤ count1019 b))) else (if i < 1036 then (if i < 1035 then decide (16 ≤ count1019 b) else decide (17 ≤ count1019 b)) else (if i < 1037 then decide (1 ≤ count1036 b) else decide (2 ≤ count1036 b)))) else (if i < 1041 then (if i < 1039 then decide (3 ≤ count1036 b) else (if i < 1040 then decide (4 ≤ count1036 b) else decide (5 ≤ count1036 b))) else (if i < 1043 then (if i < 1042 then decide (6 ≤ count1036 b) else decide (7 ≤ count1036 b)) else (if i < 1044 then decide (8 ≤ count1036 b) else decide (9 ≤ count1036 b))))))))) else (if i < 1149 then (if i < 1097 then (if i < 1071 then (if i < 1058 then (if i < 1051 then (if i < 1048 then (if i < 1046 then decide (10 ≤ count1036 b) else (if i < 1047 then decide (11 ≤ count1036 b) else decide (12 ≤ count1036 b))) else (if i < 1049 then decide (13 ≤ count1036 b) else (if i < 1050 then decide (14 ≤ count1036 b) else decide (15 ≤ count1036 b)))) else (if i < 1054 then (if i < 1052 then decide (16 ≤ count1036 b) else (if i < 1053 then decide (17 ≤ count1036 b) else decide (1 ≤ count1053 b))) else (if i < 1056 then (if i < 1055 then decide (2 ≤ count1053 b) else decide (1 ≤ count1055 b)) else (if i < 1057 then decide (2 ≤ count1055 b) else decide (3 ≤ count1055 b))))) else (if i < 1064 then (if i < 1061 then (if i < 1059 then decide (1 ≤ count1058 b) else (if i < 1060 then decide (2 ≤ count1058 b) else decide (1 ≤ count1060 b))) else (if i < 1062 then decide (2 ≤ count1060 b) else (if i < 1063 then decide (1 ≤ count1062 b) else decide (2 ≤ count1062 b)))) else (if i < 1067 then (if i < 1065 then decide (3 ≤ count1062 b) else (if i < 1066 then decide (4 ≤ count1062 b) else decide (1 ≤ count1066 b))) else (if i < 1069 then (if i < 1068 then decide (2 ≤ count1066 b) else decide (3 ≤ count1066 b)) else (if i < 1070 then decide (4 ≤ count1066 b) else decide (5 ≤ count1066 b)))))) else (if i < 1084 then (if i < 1077 then (if i < 1074 then (if i < 1072 then decide (6 ≤ count1066 b) else (if i < 1073 then decide (7 ≤ count1066 b) else decide (1 ≤ count1073 b))) else (if i < 1075 then decide (2 ≤ count1073 b) else (if i < 1076 then decide (1 ≤ count1075 b) else decide (2 ≤ count1075 b)))) else (if i < 1080 then (if i < 1078 then decide (3 ≤ count1075 b) else (if i < 1079 then decide (1 ≤ count1078 b) else decide (2 ≤ count1078 b))) else (if i < 1082 then (if i < 1081 then decide (1 ≤ count1080 b) else decide (2 ≤ count1080 b)) else (if i < 1083 then decide (1 ≤ count1082 b) else decide (2 ≤ count1082 b))))) else (if i < 1090 then (if i < 1087 then (if i < 1085 then decide (3 ≤ count1082 b) else (if i < 1086 then decide (4 ≤ count1082 b) else decide (1 ≤ count1086 b))) else (if i < 1088 then decide (2 ≤ count1086 b) else (if i < 1089 then decide (3 ≤ count1086 b) else decide (4 ≤ count1086 b)))) else (if i < 1093 then (if i < 1091 then decide (5 ≤ count1086 b) else (if i < 1092 then decide (6 ≤ count1086 b) else decide (7 ≤ count1086 b))) else (if i < 1095 then (if i < 1094 then decide (1 ≤ count1093 b) else decide (2 ≤ count1093 b)) else (if i < 1096 then decide (3 ≤ count1093 b) else decide (4 ≤ count1093 b))))))) else (if i < 1123 then (if i < 1110 then (if i < 1103 then (if i < 1100 then (if i < 1098 then decide (5 ≤ count1093 b) else (if i < 1099 then decide (6 ≤ count1093 b) else decide (7 ≤ count1093 b))) else (if i < 1101 then decide (8 ≤ count1093 b) else (if i < 1102 then decide (9 ≤ count1093 b) else decide (10 ≤ count1093 b)))) else (if i < 1106 then (if i < 1104 then decide (11 ≤ count1093 b) else (if i < 1105 then decide (12 ≤ count1093 b) else decide (13 ≤ count1093 b))) else (if i < 1108 then (if i < 1107 then decide (14 ≤ count1093 b) else decide (1 ≤ count1107 b)) else (if i < 1109 then decide (2 ≤ count1107 b) else decide (1 ≤ count1109 b))))) else (if i < 1116 then (if i < 1113 then (if i < 1111 then decide (2 ≤ count1109 b) else (if i < 1112 then decide (3 ≤ count1109 b) else decide (1 ≤ count1112 b))) else (if i < 1114 then decide (2 ≤ count1112 b) else (if i < 1115 then decide (1 ≤ count1114 b) else decide (2 ≤ count1114 b)))) else (if i < 1119 then (if i < 1117 then decide (1 ≤ count1116 b) else (if i < 1118 then decide (2 ≤ count1116 b) else decide (3 ≤ count1116 b))) else (if i < 1121 then (if i < 1120 then decide (4 ≤ count1116 b) else decide (1 ≤ count1120 b)) else (if i < 1122 then decide (2 ≤ count1120 b) else decide (3 ≤ count1120 b)))))) else (if i < 1136 then (if i < 1129 then (if i < 1126 then (if i < 1124 then decide (4 ≤ count1120 b) else (if i < 1125 then decide (5 ≤ count1120 b) else decide (6 ≤ count1120 b))) else (if i < 1127 then decide (7 ≤ count1120 b) else (if i < 1128 then decide (1 ≤ count1127 b) else decide (2 ≤ count1127 b)))) else (if i < 1132 then (if i < 1130 then decide (1 ≤ count1129 b) else (if i < 1131 then decide (2 ≤ count1129 b) else decide (1 ≤ count1131 b))) else (if i < 1134 then (if i < 1133 then decide (2 ≤ count1131 b) else decide (3 ≤ count1131 b)) else (if i < 1135 then decide (4 ≤ count1131 b) else decide (1 ≤ count1135 b))))) else (if i < 1142 then (if i < 1139 then (if i < 1137 then decide (2 ≤ count1135 b) else (if i < 1138 then decide (1 ≤ count1137 b) else decide (2 ≤ count1137 b))) else (if i < 1140 then decide (1 ≤ count1139 b) else (if i < 1141 then decide (2 ≤ count1139 b) else decide (3 ≤ count1139 b)))) else (if i < 1145 then (if i < 1143 then decide (4 ≤ count1139 b) else (if i < 1144 then decide (1 ≤ count1143 b) else decide (2 ≤ count1143 b))) else (if i < 1147 then (if i < 1146 then decide (3 ≤ count1143 b) else decide (4 ≤ count1143 b)) else (if i < 1148 then decide (5 ≤ count1143 b) else decide (6 ≤ count1143 b)))))))) else (if i < 1201 then (if i < 1175 then (if i < 1162 then (if i < 1155 then (if i < 1152 then (if i < 1150 then decide (7 ≤ count1143 b) else (if i < 1151 then decide (8 ≤ count1143 b) else decide (1 ≤ count1151 b))) else (if i < 1153 then decide (2 ≤ count1151 b) else (if i < 1154 then decide (3 ≤ count1151 b) else decide (4 ≤ count1151 b)))) else (if i < 1158 then (if i < 1156 then decide (5 ≤ count1151 b) else (if i < 1157 then decide (6 ≤ count1151 b) else decide (7 ≤ count1151 b))) else (if i < 1160 then (if i < 1159 then decide (8 ≤ count1151 b) else decide (9 ≤ count1151 b)) else (if i < 1161 then decide (10 ≤ count1151 b) else decide (11 ≤ count1151 b))))) else (if i < 1168 then (if i < 1165 then (if i < 1163 then decide (12 ≤ count1151 b) else (if i < 1164 then decide (13 ≤ count1151 b) else decide (14 ≤ count1151 b))) else (if i < 1166 then decide (15 ≤ count1151 b) else (if i < 1167 then decide (1 ≤ count1166 b) else decide (2 ≤ count1166 b)))) else (if i < 1171 then (if i < 1169 then decide (3 ≤ count1166 b) else (if i < 1170 then decide (4 ≤ count1166 b) else decide (5 ≤ count1166 b))) else (if i < 1173 then (if i < 1172 then decide (6 ≤ count1166 b) else decide (7 ≤ count1166 b)) else (if i < 1174 then decide (8 ≤ count1166 b) else decide (9 ≤ count1166 b)))))) else (if i < 1188 then (if i < 1181 then (if i < 1178 then (if i < 1176 then decide (10 ≤ count1166 b) else (if i < 1177 then decide (11 ≤ count1166 b) else decide (12 ≤ count1166 b))) else (if i < 1179 then decide (13 ≤ count1166 b) else (if i < 1180 then decide (14 ≤ count1166 b) else decide (15 ≤ count1166 b)))) else (if i < 1184 then (if i < 1182 then decide (16 ≤ count1166 b) else (if i < 1183 then decide (17 ≤ count1166 b) else decide (18 ≤ count1166 b))) else (if i < 1186 then (if i < 1185 then decide (19 ≤ count1166 b) else decide (20 ≤ count1166 b)) else (if i < 1187 then decide (21 ≤ count1166 b) else decide (22 ≤ count1166 b))))) else (if i < 1194 then (if i < 1191 then (if i < 1189 then decide (23 ≤ count1166 b) else (if i < 1190 then decide (24 ≤ count1166 b) else decide (25 ≤ count1166 b))) else (if i < 1192 then decide (26 ≤ count1166 b) else (if i < 1193 then decide (27 ≤ count1166 b) else decide (28 ≤ count1166 b)))) else (if i < 1197 then (if i < 1195 then decide (29 ≤ count1166 b) else (if i < 1196 then decide (1 ≤ count1195 b) else decide (2 ≤ count1195 b))) else (if i < 1199 then (if i < 1198 then decide (1 ≤ count1197 b) else decide (2 ≤ count1197 b)) else (if i < 1200 then decide (3 ≤ count1197 b) else decide (1 ≤ count1200 b))))))) else (if i < 1227 then (if i < 1214 then (if i < 1207 then (if i < 1204 then (if i < 1202 then decide (2 ≤ count1200 b) else (if i < 1203 then decide (1 ≤ count1202 b) else decide (2 ≤ count1202 b))) else (if i < 1205 then decide (1 ≤ count1204 b) else (if i < 1206 then decide (2 ≤ count1204 b) else decide (3 ≤ count1204 b)))) else (if i < 1210 then (if i < 1208 then decide (4 ≤ count1204 b) else (if i < 1209 then decide (1 ≤ count1208 b) else decide (2 ≤ count1208 b))) else (if i < 1212 then (if i < 1211 then decide (3 ≤ count1208 b) else decide (4 ≤ count1208 b)) else (if i < 1213 then decide (5 ≤ count1208 b) else decide (6 ≤ count1208 b))))) else (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (7 ≤ count1208 b) else (if i < 1216 then decide (1 ≤ count1215 b) else decide (2 ≤ count1215 b))) else (if i < 1218 then decide (1 ≤ count1217 b) else (if i < 1219 then decide (2 ≤ count1217 b) else decide (1 ≤ count1219 b)))) else (if i < 1223 then (if i < 1221 then decide (2 ≤ count1219 b) else (if i < 1222 then decide (3 ≤ count1219 b) else decide (4 ≤ count1219 b))) else (if i < 1225 then (if i < 1224 then decide (1 ≤ count1223 b) else decide (2 ≤ count1223 b)) else (if i < 1226 then decide (1 ≤ count1225 b) else decide (2 ≤ count1225 b)))))) else (if i < 1240 then (if i < 1233 then (if i < 1230 then (if i < 1228 then decide (1 ≤ count1227 b) else (if i < 1229 then decide (2 ≤ count1227 b) else decide (3 ≤ count1227 b))) else (if i < 1231 then decide (4 ≤ count1227 b) else (if i < 1232 then decide (1 ≤ count1231 b) else decide (2 ≤ count1231 b)))) else (if i < 1236 then (if i < 1234 then decide (3 ≤ count1231 b) else (if i < 1235 then decide (4 ≤ count1231 b) else decide (5 ≤ count1231 b))) else (if i < 1238 then (if i < 1237 then decide (6 ≤ count1231 b) else decide (7 ≤ count1231 b)) else (if i < 1239 then decide (8 ≤ count1231 b) else decide (1 ≤ count1239 b))))) else (if i < 1247 then (if i < 1243 then (if i < 1241 then decide (2 ≤ count1239 b) else (if i < 1242 then decide (3 ≤ count1239 b) else decide (4 ≤ count1239 b))) else (if i < 1245 then (if i < 1244 then decide (5 ≤ count1239 b) else decide (6 ≤ count1239 b)) else (if i < 1246 then decide (7 ≤ count1239 b) else decide (8 ≤ count1239 b)))) else (if i < 1250 then (if i < 1248 then decide (9 ≤ count1239 b) else (if i < 1249 then decide (10 ≤ count1239 b) else decide (11 ≤ count1239 b))) else (if i < 1252 then (if i < 1251 then decide (12 ≤ count1239 b) else decide (13 ≤ count1239 b)) else (if i < 1253 then decide (14 ≤ count1239 b) else decide (15 ≤ count1239 b)))))))))) else (if i < 1463 then (if i < 1358 then (if i < 1306 then (if i < 1280 then (if i < 1267 then (if i < 1260 then (if i < 1257 then (if i < 1255 then decide (1 ≤ count1254 b) else (if i < 1256 then decide (2 ≤ count1254 b) else decide (1 ≤ count1256 b))) else (if i < 1258 then decide (2 ≤ count1256 b) else (if i < 1259 then decide (3 ≤ count1256 b) else decide (1 ≤ count1259 b)))) else (if i < 1263 then (if i < 1261 then decide (2 ≤ count1259 b) else (if i < 1262 then decide (1 ≤ count1261 b) else decide (2 ≤ count1261 b))) else (if i < 1265 then (if i < 1264 then decide (1 ≤ count1263 b) else decide (2 ≤ count1263 b)) else (if i < 1266 then decide (3 ≤ count1263 b) else decide (4 ≤ count1263 b))))) else (if i < 1273 then (if i < 1270 then (if i < 1268 then decide (1 ≤ count1267 b) else (if i < 1269 then decide (2 ≤ count1267 b) else decide (3 ≤ count1267 b))) else (if i < 1271 then decide (4 ≤ count1267 b) else (if i < 1272 then decide (5 ≤ count1267 b) else decide (6 ≤ count1267 b)))) else (if i < 1276 then (if i < 1274 then decide (7 ≤ count1267 b) else (if i < 1275 then decide (1 ≤ count1274 b) else decide (2 ≤ count1274 b))) else (if i < 1278 then (if i < 1277 then decide (1 ≤ count1276 b) else decide (2 ≤ count1276 b)) else (if i < 1279 then decide (1 ≤ count1278 b) else decide (2 ≤ count1278 b)))))) else (if i < 1293 then (if i < 1286 then (if i < 1283 then (if i < 1281 then decide (3 ≤ count1278 b) else (if i < 1282 then decide (4 ≤ count1278 b) else decide (1 ≤ count1282 b))) else (if i < 1284 then decide (2 ≤ count1282 b) else (if i < 1285 then decide (1 ≤ count1284 b) else decide (2 ≤ count1284 b)))) else (if i < 1289 then (if i < 1287 then decide (1 ≤ count1286 b) else (if i < 1288 then decide (2 ≤ count1286 b) else decide (3 ≤ count1286 b))) else (if i < 1291 then (if i < 1290 then decide (4 ≤ count1286 b) else decide (1 ≤ count1290 b)) else (if i < 1292 then decide (2 ≤ count1290 b) else decide (3 ≤ count1290 b))))) else (if i < 1299 then (if i < 1296 then (if i < 1294 then decide (4 ≤ count1290 b) else (if i < 1295 then decide (5 ≤ count1290 b) else decide (6 ≤ count1290 b))) else (if i < 1297 then decide (7 ≤ count1290 b) else (if i < 1298 then decide (8 ≤ count1290 b) else decide (1 ≤ count1298 b)))) else (if i < 1302 then (if i < 1300 then decide (2 ≤ count1298 b) else (if i < 1301 then decide (3 ≤ count1298 b) else decide (4 ≤ count1298 b))) else (if i < 1304 then (if i < 1303 then decide (5 ≤ count1298 b) else decide (6 ≤ count1298 b)) else (if i < 1305 then decide (7 ≤ count1298 b) else decide (8 ≤ count1298 b))))))) else (if i < 1332 then (if i < 1319 then (if i < 1312 then (if i < 1309 then (if i < 1307 then decide (9 ≤ count1298 b) else (if i < 1308 then decide (10 ≤ count1298 b) else decide (11 ≤ count1298 b))) else (if i < 1310 then decide (12 ≤ count1298 b) else (if i < 1311 then decide (13 ≤ count1298 b) else decide (14 ≤ count1298 b)))) else (if i < 1315 then (if i < 1313 then decide (15 ≤ count1298 b) else (if i < 1314 then decide (1 ≤ count1313 b) else decide (2 ≤ count1313 b))) else (if i < 1317 then (if i < 1316 then decide (3 ≤ count1313 b) else decide (4 ≤ count1313 b)) else (if i < 1318 then decide (5 ≤ count1313 b) else decide (6 ≤ count1313 b))))) else (if i < 1325 then (if i < 1322 then (if i < 1320 then decide (7 ≤ count1313 b) else (if i < 1321 then decide (8 ≤ count1313 b) else decide (9 ≤ count1313 b))) else (if i < 1323 then decide (10 ≤ count1313 b) else (if i < 1324 then decide (11 ≤ count1313 b) else decide (12 ≤ count1313 b)))) else (if i < 1328 then (if i < 1326 then decide (13 ≤ count1313 b) else (if i < 1327 then decide (14 ≤ count1313 b) else decide (15 ≤ count1313 b))) else (if i < 1330 then (if i < 1329 then decide (16 ≤ count1313 b) else decide (17 ≤ count1313 b)) else (if i < 1331 then decide (18 ≤ count1313 b) else decide (19 ≤ count1313 b)))))) else (if i < 1345 then (if i < 1338 then (if i < 1335 then (if i < 1333 then decide (20 ≤ count1313 b) else (if i < 1334 then decide (21 ≤ count1313 b) else decide (22 ≤ count1313 b))) else (if i < 1336 then decide (23 ≤ count1313 b) else (if i < 1337 then decide (24 ≤ count1313 b) else decide (25 ≤ count1313 b)))) else (if i < 1341 then (if i < 1339 then decide (26 ≤ count1313 b) else (if i < 1340 then decide (27 ≤ count1313 b) else decide (28 ≤ count1313 b))) else (if i < 1343 then (if i < 1342 then decide (29 ≤ count1313 b) else decide (30 ≤ count1313 b)) else (if i < 1344 then decide (1 ≤ count1343 b) else decide (2 ≤ count1343 b))))) else (if i < 1351 then (if i < 1348 then (if i < 1346 then decide (3 ≤ count1343 b) else (if i < 1347 then decide (4 ≤ count1343 b) else decide (5 ≤ count1343 b))) else (if i < 1349 then decide (6 ≤ count1343 b) else (if i < 1350 then decide (7 ≤ count1343 b) else decide (8 ≤ count1343 b)))) else (if i < 1354 then (if i < 1352 then decide (9 ≤ count1343 b) else (if i < 1353 then decide (10 ≤ count1343 b) else decide (11 ≤ count1343 b))) else (if i < 1356 then (if i < 1355 then decide (12 ≤ count1343 b) else decide (13 ≤ count1343 b)) else (if i < 1357 then decide (14 ≤ count1343 b) else decide (15 ≤ count1343 b)))))))) else (if i < 1410 then (if i < 1384 then (if i < 1371 then (if i < 1364 then (if i < 1361 then (if i < 1359 then decide (16 ≤ count1343 b) else (if i < 1360 then decide (17 ≤ count1343 b) else decide (18 ≤ count1343 b))) else (if i < 1362 then decide (19 ≤ count1343 b) else (if i < 1363 then decide (20 ≤ count1343 b) else decide (21 ≤ count1343 b)))) else (if i < 1367 then (if i < 1365 then decide (22 ≤ count1343 b) else (if i < 1366 then decide (23 ≤ count1343 b) else decide (24 ≤ count1343 b))) else (if i < 1369 then (if i < 1368 then decide (25 ≤ count1343 b) else decide (26 ≤ count1343 b)) else (if i < 1370 then decide (27 ≤ count1343 b) else decide (28 ≤ count1343 b))))) else (if i < 1377 then (if i < 1374 then (if i < 1372 then decide (29 ≤ count1343 b) else (if i < 1373 then decide (30 ≤ count1343 b) else decide (31 ≤ count1343 b))) else (if i < 1375 then decide (32 ≤ count1343 b) else (if i < 1376 then decide (33 ≤ count1343 b) else decide (34 ≤ count1343 b)))) else (if i < 1380 then (if i < 1378 then decide (35 ≤ count1343 b) else (if i < 1379 then decide (36 ≤ count1343 b) else decide (37 ≤ count1343 b))) else (if i < 1382 then (if i < 1381 then decide (38 ≤ count1343 b) else decide (39 ≤ count1343 b)) else (if i < 1383 then decide (40 ≤ count1343 b) else decide (41 ≤ count1343 b)))))) else (if i < 1397 then (if i < 1390 then (if i < 1387 then (if i < 1385 then decide (42 ≤ count1343 b) else (if i < 1386 then decide (1 ≤ count1385 b) else decide (2 ≤ count1385 b))) else (if i < 1388 then decide (1 ≤ count1387 b) else (if i < 1389 then decide (2 ≤ count1387 b) else decide (3 ≤ count1387 b)))) else (if i < 1393 then (if i < 1391 then decide (1 ≤ count1390 b) else (if i < 1392 then decide (2 ≤ count1390 b) else decide (1 ≤ count1392 b))) else (if i < 1395 then (if i < 1394 then decide (2 ≤ count1392 b) else decide (1 ≤ count1394 b)) else (if i < 1396 then decide (2 ≤ count1394 b) else decide (3 ≤ count1394 b))))) else (if i < 1403 then (if i < 1400 then (if i < 1398 then decide (4 ≤ count1394 b) else (if i < 1399 then decide (1 ≤ count1398 b) else decide (2 ≤ count1398 b))) else (if i < 1401 then decide (3 ≤ count1398 b) else (if i < 1402 then decide (4 ≤ count1398 b) else decide (5 ≤ count1398 b)))) else (if i < 1406 then (if i < 1404 then decide (6 ≤ count1398 b) else (if i < 1405 then decide (7 ≤ count1398 b) else decide (1 ≤ count1405 b))) else (if i < 1408 then (if i < 1407 then decide (2 ≤ count1405 b) else decide (1 ≤ count1407 b)) else (if i < 1409 then decide (2 ≤ count1407 b) else decide (3 ≤ count1407 b))))))) else (if i < 1436 then (if i < 1423 then (if i < 1416 then (if i < 1413 then (if i < 1411 then decide (1 ≤ count1410 b) else (if i < 1412 then decide (2 ≤ count1410 b) else decide (1 ≤ count1412 b))) else (if i < 1414 then decide (2 ≤ count1412 b) else (if i < 1415 then decide (1 ≤ count1414 b) else decide (2 ≤ count1414 b)))) else (if i < 1419 then (if i < 1417 then decide (3 ≤ count1414 b) else (if i < 1418 then decide (4 ≤ count1414 b) else decide (1 ≤ count1418 b))) else (if i < 1421 then (if i < 1420 then decide (2 ≤ count1418 b) else decide (3 ≤ count1418 b)) else (if i < 1422 then decide (4 ≤ count1418 b) else decide (5 ≤ count1418 b))))) else (if i < 1429 then (if i < 1426 then (if i < 1424 then decide (6 ≤ count1418 b) else (if i < 1425 then decide (7 ≤ count1418 b) else decide (1 ≤ count1425 b))) else (if i < 1427 then decide (2 ≤ count1425 b) else (if i < 1428 then decide (3 ≤ count1425 b) else decide (4 ≤ count1425 b)))) else (if i < 1432 then (if i < 1430 then decide (5 ≤ count1425 b) else (if i < 1431 then decide (6 ≤ count1425 b) else decide (7 ≤ count1425 b))) else (if i < 1434 then (if i < 1433 then decide (8 ≤ count1425 b) else decide (9 ≤ count1425 b)) else (if i < 1435 then decide (10 ≤ count1425 b) else decide (11 ≤ count1425 b)))))) else (if i < 1449 then (if i < 1442 then (if i < 1439 then (if i < 1437 then decide (12 ≤ count1425 b) else (if i < 1438 then decide (13 ≤ count1425 b) else decide (14 ≤ count1425 b))) else (if i < 1440 then decide (1 ≤ count1439 b) else (if i < 1441 then decide (2 ≤ count1439 b) else decide (1 ≤ count1441 b)))) else (if i < 1445 then (if i < 1443 then decide (2 ≤ count1441 b) else (if i < 1444 then decide (3 ≤ count1441 b) else decide (1 ≤ count1444 b))) else (if i < 1447 then (if i < 1446 then decide (2 ≤ count1444 b) else decide (1 ≤ count1446 b)) else (if i < 1448 then decide (2 ≤ count1446 b) else decide (1 ≤ count1448 b))))) else (if i < 1456 then (if i < 1452 then (if i < 1450 then decide (2 ≤ count1448 b) else (if i < 1451 then decide (3 ≤ count1448 b) else decide (4 ≤ count1448 b))) else (if i < 1454 then (if i < 1453 then decide (1 ≤ count1452 b) else decide (2 ≤ count1452 b)) else (if i < 1455 then decide (3 ≤ count1452 b) else decide (4 ≤ count1452 b)))) else (if i < 1459 then (if i < 1457 then decide (5 ≤ count1452 b) else (if i < 1458 then decide (6 ≤ count1452 b) else decide (7 ≤ count1452 b))) else (if i < 1461 then (if i < 1460 then decide (1 ≤ count1459 b) else decide (2 ≤ count1459 b)) else (if i < 1462 then decide (1 ≤ count1461 b) else decide (2 ≤ count1461 b))))))))) else (if i < 1568 then (if i < 1515 then (if i < 1489 then (if i < 1476 then (if i < 1469 then (if i < 1466 then (if i < 1464 then decide (1 ≤ count1463 b) else (if i < 1465 then decide (2 ≤ count1463 b) else decide (3 ≤ count1463 b))) else (if i < 1467 then decide (4 ≤ count1463 b) else (if i < 1468 then decide (1 ≤ count1467 b) else decide (2 ≤ count1467 b)))) else (if i < 1472 then (if i < 1470 then decide (1 ≤ count1469 b) else (if i < 1471 then decide (2 ≤ count1469 b) else decide (1 ≤ count1471 b))) else (if i < 1474 then (if i < 1473 then decide (2 ≤ count1471 b) else decide (3 ≤ count1471 b)) else (if i < 1475 then decide (4 ≤ count1471 b) else decide (1 ≤ count1475 b))))) else (if i < 1482 then (if i < 1479 then (if i < 1477 then decide (2 ≤ count1475 b) else (if i < 1478 then decide (3 ≤ count1475 b) else decide (4 ≤ count1475 b))) else (if i < 1480 then decide (5 ≤ count1475 b) else (if i < 1481 then decide (6 ≤ count1475 b) else decide (7 ≤ count1475 b)))) else (if i < 1485 then (if i < 1483 then decide (8 ≤ count1475 b) else (if i < 1484 then decide (1 ≤ count1483 b) else decide (2 ≤ count1483 b))) else (if i < 1487 then (if i < 1486 then decide (3 ≤ count1483 b) else decide (4 ≤ count1483 b)) else (if i < 1488 then decide (5 ≤ count1483 b) else decide (6 ≤ count1483 b)))))) else (if i < 1502 then (if i < 1495 then (if i < 1492 then (if i < 1490 then decide (7 ≤ count1483 b) else (if i < 1491 then decide (8 ≤ count1483 b) else decide (9 ≤ count1483 b))) else (if i < 1493 then decide (10 ≤ count1483 b) else (if i < 1494 then decide (11 ≤ count1483 b) else decide (12 ≤ count1483 b)))) else (if i < 1498 then (if i < 1496 then decide (13 ≤ count1483 b) else (if i < 1497 then decide (14 ≤ count1483 b) else decide (15 ≤ count1483 b))) else (if i < 1500 then (if i < 1499 then decide (1 ≤ count1498 b) else decide (2 ≤ count1498 b)) else (if i < 1501 then decide (3 ≤ count1498 b) else decide (4 ≤ count1498 b))))) else (if i < 1508 then (if i < 1505 then (if i < 1503 then decide (5 ≤ count1498 b) else (if i < 1504 then decide (6 ≤ count1498 b) else decide (7 ≤ count1498 b))) else (if i < 1506 then decide (8 ≤ count1498 b) else (if i < 1507 then decide (9 ≤ count1498 b) else decide (10 ≤ count1498 b)))) else (if i < 1511 then (if i < 1509 then decide (11 ≤ count1498 b) else (if i < 1510 then decide (12 ≤ count1498 b) else decide (13 ≤ count1498 b))) else (if i < 1513 then (if i < 1512 then decide (14 ≤ count1498 b) else decide (15 ≤ count1498 b)) else (if i < 1514 then decide (16 ≤ count1498 b) else decide (17 ≤ count1498 b))))))) else (if i < 1541 then (if i < 1528 then (if i < 1521 then (if i < 1518 then (if i < 1516 then decide (18 ≤ count1498 b) else (if i < 1517 then decide (19 ≤ count1498 b) else decide (1 ≤ count1517 b))) else (if i < 1519 then decide (2 ≤ count1517 b) else (if i < 1520 then decide (1 ≤ count1519 b) else decide (2 ≤ count1519 b)))) else (if i < 1524 then (if i < 1522 then decide (3 ≤ count1519 b) else (if i < 1523 then decide (1 ≤ count1522 b) else decide (2 ≤ count1522 b))) else (if i < 1526 then (if i < 1525 then decide (1 ≤ count1524 b) else decide (2 ≤ count1524 b)) else (if i < 1527 then decide (1 ≤ count1526 b) else decide (2 ≤ count1526 b))))) else (if i < 1534 then (if i < 1531 then (if i < 1529 then decide (3 ≤ count1526 b) else (if i < 1530 then decide (4 ≤ count1526 b) else decide (1 ≤ count1530 b))) else (if i < 1532 then decide (2 ≤ count1530 b) else (if i < 1533 then decide (3 ≤ count1530 b) else decide (4 ≤ count1530 b)))) else (if i < 1537 then (if i < 1535 then decide (5 ≤ count1530 b) else (if i < 1536 then decide (6 ≤ count1530 b) else decide (7 ≤ count1530 b))) else (if i < 1539 then (if i < 1538 then decide (1 ≤ count1537 b) else decide (2 ≤ count1537 b)) else (if i < 1540 then decide (1 ≤ count1539 b) else decide (2 ≤ count1539 b)))))) else (if i < 1554 then (if i < 1547 then (if i < 1544 then (if i < 1542 then decide (1 ≤ count1541 b) else (if i < 1543 then decide (2 ≤ count1541 b) else decide (3 ≤ count1541 b))) else (if i < 1545 then decide (4 ≤ count1541 b) else (if i < 1546 then decide (1 ≤ count1545 b) else decide (2 ≤ count1545 b)))) else (if i < 1550 then (if i < 1548 then decide (1 ≤ count1547 b) else (if i < 1549 then decide (2 ≤ count1547 b) else decide (1 ≤ count1549 b))) else (if i < 1552 then (if i < 1551 then decide (2 ≤ count1549 b) else decide (3 ≤ count1549 b)) else (if i < 1553 then decide (4 ≤ count1549 b) else decide (1 ≤ count1553 b))))) else (if i < 1561 then (if i < 1557 then (if i < 1555 then decide (2 ≤ count1553 b) else (if i < 1556 then decide (3 ≤ count1553 b) else decide (4 ≤ count1553 b))) else (if i < 1559 then (if i < 1558 then decide (5 ≤ count1553 b) else decide (6 ≤ count1553 b)) else (if i < 1560 then decide (7 ≤ count1553 b) else decide (8 ≤ count1553 b)))) else (if i < 1564 then (if i < 1562 then decide (1 ≤ count1561 b) else (if i < 1563 then decide (2 ≤ count1561 b) else decide (3 ≤ count1561 b))) else (if i < 1566 then (if i < 1565 then decide (4 ≤ count1561 b) else decide (5 ≤ count1561 b)) else (if i < 1567 then decide (6 ≤ count1561 b) else decide (7 ≤ count1561 b)))))))) else (if i < 1620 then (if i < 1594 then (if i < 1581 then (if i < 1574 then (if i < 1571 then (if i < 1569 then decide (8 ≤ count1561 b) else (if i < 1570 then decide (9 ≤ count1561 b) else decide (10 ≤ count1561 b))) else (if i < 1572 then decide (11 ≤ count1561 b) else (if i < 1573 then decide (12 ≤ count1561 b) else decide (13 ≤ count1561 b)))) else (if i < 1577 then (if i < 1575 then decide (14 ≤ count1561 b) else (if i < 1576 then decide (15 ≤ count1561 b) else decide (1 ≤ count1576 b))) else (if i < 1579 then (if i < 1578 then decide (2 ≤ count1576 b) else decide (1 ≤ count1578 b)) else (if i < 1580 then decide (2 ≤ count1578 b) else decide (3 ≤ count1578 b))))) else (if i < 1587 then (if i < 1584 then (if i < 1582 then decide (1 ≤ count1581 b) else (if i < 1583 then decide (2 ≤ count1581 b) else decide (1 ≤ count1583 b))) else (if i < 1585 then decide (2 ≤ count1583 b) else (if i < 1586 then decide (1 ≤ count1585 b) else decide (2 ≤ count1585 b)))) else (if i < 1590 then (if i < 1588 then decide (3 ≤ count1585 b) else (if i < 1589 then decide (4 ≤ count1585 b) else decide (1 ≤ count1589 b))) else (if i < 1592 then (if i < 1591 then decide (2 ≤ count1589 b) else decide (3 ≤ count1589 b)) else (if i < 1593 then decide (4 ≤ count1589 b) else decide (5 ≤ count1589 b)))))) else (if i < 1607 then (if i < 1600 then (if i < 1597 then (if i < 1595 then decide (6 ≤ count1589 b) else (if i < 1596 then decide (7 ≤ count1589 b) else decide (1 ≤ count1596 b))) else (if i < 1598 then decide (2 ≤ count1596 b) else (if i < 1599 then decide (1 ≤ count1598 b) else decide (2 ≤ count1598 b)))) else (if i < 1603 then (if i < 1601 then decide (1 ≤ count1600 b) else (if i < 1602 then decide (2 ≤ count1600 b) else decide (3 ≤ count1600 b))) else (if i < 1605 then (if i < 1604 then decide (4 ≤ count1600 b) else decide (1 ≤ count1604 b)) else (if i < 1606 then decide (2 ≤ count1604 b) else decide (1 ≤ count1606 b))))) else (if i < 1613 then (if i < 1610 then (if i < 1608 then decide (2 ≤ count1606 b) else (if i < 1609 then decide (1 ≤ count1608 b) else decide (2 ≤ count1608 b))) else (if i < 1611 then decide (3 ≤ count1608 b) else (if i < 1612 then decide (4 ≤ count1608 b) else decide (1 ≤ count1612 b)))) else (if i < 1616 then (if i < 1614 then decide (2 ≤ count1612 b) else (if i < 1615 then decide (3 ≤ count1612 b) else decide (4 ≤ count1612 b))) else (if i < 1618 then (if i < 1617 then decide (5 ≤ count1612 b) else decide (6 ≤ count1612 b)) else (if i < 1619 then decide (7 ≤ count1612 b) else decide (8 ≤ count1612 b))))))) else (if i < 1646 then (if i < 1633 then (if i < 1626 then (if i < 1623 then (if i < 1621 then decide (1 ≤ count1620 b) else (if i < 1622 then decide (2 ≤ count1620 b) else decide (3 ≤ count1620 b))) else (if i < 1624 then decide (4 ≤ count1620 b) else (if i < 1625 then decide (5 ≤ count1620 b) else decide (6 ≤ count1620 b)))) else (if i < 1629 then (if i < 1627 then decide (7 ≤ count1620 b) else (if i < 1628 then decide (8 ≤ count1620 b) else decide (9 ≤ count1620 b))) else (if i < 1631 then (if i < 1630 then decide (10 ≤ count1620 b) else decide (11 ≤ count1620 b)) else (if i < 1632 then decide (12 ≤ count1620 b) else decide (13 ≤ count1620 b))))) else (if i < 1639 then (if i < 1636 then (if i < 1634 then decide (14 ≤ count1620 b) else (if i < 1635 then decide (15 ≤ count1620 b) else decide (1 ≤ count1635 b))) else (if i < 1637 then decide (2 ≤ count1635 b) else (if i < 1638 then decide (3 ≤ count1635 b) else decide (4 ≤ count1635 b)))) else (if i < 1642 then (if i < 1640 then decide (5 ≤ count1635 b) else (if i < 1641 then decide (6 ≤ count1635 b) else decide (7 ≤ count1635 b))) else (if i < 1644 then (if i < 1643 then decide (8 ≤ count1635 b) else decide (9 ≤ count1635 b)) else (if i < 1645 then decide (10 ≤ count1635 b) else decide (11 ≤ count1635 b)))))) else (if i < 1659 then (if i < 1652 then (if i < 1649 then (if i < 1647 then decide (12 ≤ count1635 b) else (if i < 1648 then decide (13 ≤ count1635 b) else decide (14 ≤ count1635 b))) else (if i < 1650 then decide (15 ≤ count1635 b) else (if i < 1651 then decide (16 ≤ count1635 b) else decide (17 ≤ count1635 b)))) else (if i < 1655 then (if i < 1653 then decide (18 ≤ count1635 b) else (if i < 1654 then decide (19 ≤ count1635 b) else decide (1 ≤ count1654 b))) else (if i < 1657 then (if i < 1656 then decide (2 ≤ count1654 b) else decide (3 ≤ count1654 b)) else (if i < 1658 then decide (4 ≤ count1654 b) else decide (5 ≤ count1654 b))))) else (if i < 1666 then (if i < 1662 then (if i < 1660 then decide (6 ≤ count1654 b) else (if i < 1661 then decide (7 ≤ count1654 b) else decide (8 ≤ count1654 b))) else (if i < 1664 then (if i < 1663 then decide (9 ≤ count1654 b) else decide (10 ≤ count1654 b)) else (if i < 1665 then decide (11 ≤ count1654 b) else decide (12 ≤ count1654 b)))) else (if i < 1669 then (if i < 1667 then decide (13 ≤ count1654 b) else (if i < 1668 then decide (14 ≤ count1654 b) else decide (15 ≤ count1654 b))) else (if i < 1671 then (if i < 1670 then decide (16 ≤ count1654 b) else decide (17 ≤ count1654 b)) else (if i < 1672 then decide (18 ≤ count1654 b) else decide (19 ≤ count1654 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (7 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (8 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (10 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (14 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (15 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (17 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (20 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (21 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (22 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (25 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (26 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (27 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (29 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (65 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (69 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (73 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (75 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (79 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (97 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (104 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (106 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (110 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (111 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (113 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (121 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (122 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (123 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (125 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (160 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (161 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (166 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (167 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (168 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (170 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (172 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (174 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (175 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (177 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (180 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (181 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (182 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (185 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (186 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (187 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (189 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (288 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (289 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (294 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (295 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (296 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (298 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (300 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (302 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (303 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (305 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (308 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (309 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (310 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (313 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (314 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (315 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (317 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (352 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (353 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (355 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (357 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (359 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (361 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (363 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (365 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (366 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (367 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (368 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (370 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (371 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (376 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (378 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (380 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (381 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (382 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (416 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (417 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (418 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (419 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (421 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (422 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (423 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (424 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (425 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (427 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (428 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (429 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (431 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (432 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (434 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (435 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (436 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (438 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (440 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (444 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (445 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (481 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (482 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (486 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (488 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (490 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (492 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (497 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (500 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (501 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (502 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (7 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (20 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (21 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (26 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (65 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (75 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (97 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (104 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (106 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (110 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (111 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (113 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (121 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (123 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (170 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (172 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (180 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (187 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (294 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (295 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (298 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (300 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (303 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (308 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (314 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (315 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (365 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (367 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (371 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (380 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (381 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (429 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (490 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (500 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (501 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (2 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (2 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (2 ≤ count243 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value264 (q : Snake 81) : valuation q 264 = decide (2 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value268 (q : Snake 81) : valuation q 268 = decide (2 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value274 (q : Snake 81) : valuation q 274 = decide (2 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value284 (q : Snake 81) : valuation q 284 = decide (2 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value286 (q : Snake 81) : valuation q 286 = decide (2 ≤ count285 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value460 (q : Snake 81) : valuation q 460 = decide (2 ≤ count459 (baseVal q)) := rfl
theorem value781 (q : Snake 81) : valuation q 781 = decide (1 ≤ count781 (baseVal q)) := rfl
theorem value782 (q : Snake 81) : valuation q 782 = decide (2 ≤ count781 (baseVal q)) := rfl
theorem value783 (q : Snake 81) : valuation q 783 = decide (1 ≤ count783 (baseVal q)) := rfl
theorem value784 (q : Snake 81) : valuation q 784 = decide (2 ≤ count783 (baseVal q)) := rfl
theorem value786 (q : Snake 81) : valuation q 786 = decide (1 ≤ count786 (baseVal q)) := rfl
theorem value787 (q : Snake 81) : valuation q 787 = decide (2 ≤ count786 (baseVal q)) := rfl
theorem value788 (q : Snake 81) : valuation q 788 = decide (1 ≤ count788 (baseVal q)) := rfl
theorem value789 (q : Snake 81) : valuation q 789 = decide (2 ≤ count788 (baseVal q)) := rfl
theorem value790 (q : Snake 81) : valuation q 790 = decide (1 ≤ count790 (baseVal q)) := rfl
theorem value791 (q : Snake 81) : valuation q 791 = decide (2 ≤ count790 (baseVal q)) := rfl
theorem value792 (q : Snake 81) : valuation q 792 = decide (3 ≤ count790 (baseVal q)) := rfl
theorem value793 (q : Snake 81) : valuation q 793 = decide (4 ≤ count790 (baseVal q)) := rfl
theorem value794 (q : Snake 81) : valuation q 794 = decide (1 ≤ count794 (baseVal q)) := rfl
theorem value795 (q : Snake 81) : valuation q 795 = decide (2 ≤ count794 (baseVal q)) := rfl
theorem value796 (q : Snake 81) : valuation q 796 = decide (3 ≤ count794 (baseVal q)) := rfl
theorem value797 (q : Snake 81) : valuation q 797 = decide (4 ≤ count794 (baseVal q)) := rfl
theorem value801 (q : Snake 81) : valuation q 801 = decide (1 ≤ count801 (baseVal q)) := rfl
theorem value802 (q : Snake 81) : valuation q 802 = decide (2 ≤ count801 (baseVal q)) := rfl
theorem value803 (q : Snake 81) : valuation q 803 = decide (1 ≤ count803 (baseVal q)) := rfl
theorem value804 (q : Snake 81) : valuation q 804 = decide (2 ≤ count803 (baseVal q)) := rfl
theorem value805 (q : Snake 81) : valuation q 805 = decide (3 ≤ count803 (baseVal q)) := rfl
theorem value806 (q : Snake 81) : valuation q 806 = decide (1 ≤ count806 (baseVal q)) := rfl
theorem value807 (q : Snake 81) : valuation q 807 = decide (2 ≤ count806 (baseVal q)) := rfl
theorem value808 (q : Snake 81) : valuation q 808 = decide (1 ≤ count808 (baseVal q)) := rfl
theorem value809 (q : Snake 81) : valuation q 809 = decide (2 ≤ count808 (baseVal q)) := rfl
theorem value810 (q : Snake 81) : valuation q 810 = decide (1 ≤ count810 (baseVal q)) := rfl
theorem value811 (q : Snake 81) : valuation q 811 = decide (2 ≤ count810 (baseVal q)) := rfl
theorem value812 (q : Snake 81) : valuation q 812 = decide (3 ≤ count810 (baseVal q)) := rfl
theorem value814 (q : Snake 81) : valuation q 814 = decide (1 ≤ count814 (baseVal q)) := rfl
theorem value815 (q : Snake 81) : valuation q 815 = decide (2 ≤ count814 (baseVal q)) := rfl
theorem value816 (q : Snake 81) : valuation q 816 = decide (3 ≤ count814 (baseVal q)) := rfl
theorem value817 (q : Snake 81) : valuation q 817 = decide (4 ≤ count814 (baseVal q)) := rfl
theorem value822 (q : Snake 81) : valuation q 822 = decide (2 ≤ count821 (baseVal q)) := rfl
theorem value823 (q : Snake 81) : valuation q 823 = decide (3 ≤ count821 (baseVal q)) := rfl
theorem value824 (q : Snake 81) : valuation q 824 = decide (4 ≤ count821 (baseVal q)) := rfl
theorem value825 (q : Snake 81) : valuation q 825 = decide (5 ≤ count821 (baseVal q)) := rfl
theorem value826 (q : Snake 81) : valuation q 826 = decide (6 ≤ count821 (baseVal q)) := rfl
theorem value835 (q : Snake 81) : valuation q 835 = decide (1 ≤ count835 (baseVal q)) := rfl
theorem value836 (q : Snake 81) : valuation q 836 = decide (2 ≤ count835 (baseVal q)) := rfl
theorem value837 (q : Snake 81) : valuation q 837 = decide (1 ≤ count837 (baseVal q)) := rfl
theorem value838 (q : Snake 81) : valuation q 838 = decide (2 ≤ count837 (baseVal q)) := rfl
theorem value840 (q : Snake 81) : valuation q 840 = decide (1 ≤ count840 (baseVal q)) := rfl
theorem value841 (q : Snake 81) : valuation q 841 = decide (2 ≤ count840 (baseVal q)) := rfl
theorem value842 (q : Snake 81) : valuation q 842 = decide (1 ≤ count842 (baseVal q)) := rfl
theorem value843 (q : Snake 81) : valuation q 843 = decide (2 ≤ count842 (baseVal q)) := rfl
theorem value844 (q : Snake 81) : valuation q 844 = decide (1 ≤ count844 (baseVal q)) := rfl
theorem value845 (q : Snake 81) : valuation q 845 = decide (2 ≤ count844 (baseVal q)) := rfl
theorem value846 (q : Snake 81) : valuation q 846 = decide (3 ≤ count844 (baseVal q)) := rfl
theorem value848 (q : Snake 81) : valuation q 848 = decide (1 ≤ count848 (baseVal q)) := rfl
theorem value849 (q : Snake 81) : valuation q 849 = decide (2 ≤ count848 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (3 ≤ count848 (baseVal q)) := rfl
theorem value851 (q : Snake 81) : valuation q 851 = decide (4 ≤ count848 (baseVal q)) := rfl
theorem value855 (q : Snake 81) : valuation q 855 = decide (1 ≤ count855 (baseVal q)) := rfl
theorem value856 (q : Snake 81) : valuation q 856 = decide (2 ≤ count855 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (1 ≤ count857 (baseVal q)) := rfl
theorem value858 (q : Snake 81) : valuation q 858 = decide (2 ≤ count857 (baseVal q)) := rfl
theorem value860 (q : Snake 81) : valuation q 860 = decide (1 ≤ count860 (baseVal q)) := rfl
theorem value861 (q : Snake 81) : valuation q 861 = decide (2 ≤ count860 (baseVal q)) := rfl
theorem value862 (q : Snake 81) : valuation q 862 = decide (1 ≤ count862 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (2 ≤ count862 (baseVal q)) := rfl
theorem value864 (q : Snake 81) : valuation q 864 = decide (1 ≤ count864 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (2 ≤ count864 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (3 ≤ count864 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (1 ≤ count868 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (2 ≤ count868 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (3 ≤ count868 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (4 ≤ count868 (baseVal q)) := rfl
theorem value875 (q : Snake 81) : valuation q 875 = decide (1 ≤ count875 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (2 ≤ count875 (baseVal q)) := rfl
theorem value877 (q : Snake 81) : valuation q 877 = decide (3 ≤ count875 (baseVal q)) := rfl
theorem value878 (q : Snake 81) : valuation q 878 = decide (4 ≤ count875 (baseVal q)) := rfl
theorem value879 (q : Snake 81) : valuation q 879 = decide (5 ≤ count875 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (7 ≤ count875 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (6 ≤ count889 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (7 ≤ count889 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (9 ≤ count889 (baseVal q)) := rfl
theorem value906 (q : Snake 81) : valuation q 906 = decide (1 ≤ count906 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (2 ≤ count906 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (1 ≤ count908 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (2 ≤ count908 (baseVal q)) := rfl
theorem value910 (q : Snake 81) : valuation q 910 = decide (3 ≤ count908 (baseVal q)) := rfl
theorem value911 (q : Snake 81) : valuation q 911 = decide (1 ≤ count911 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (2 ≤ count911 (baseVal q)) := rfl
theorem value913 (q : Snake 81) : valuation q 913 = decide (1 ≤ count913 (baseVal q)) := rfl
theorem value914 (q : Snake 81) : valuation q 914 = decide (2 ≤ count913 (baseVal q)) := rfl
theorem value915 (q : Snake 81) : valuation q 915 = decide (1 ≤ count915 (baseVal q)) := rfl
theorem value916 (q : Snake 81) : valuation q 916 = decide (2 ≤ count915 (baseVal q)) := rfl
theorem value917 (q : Snake 81) : valuation q 917 = decide (3 ≤ count915 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (1 ≤ count919 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (2 ≤ count919 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (3 ≤ count919 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (4 ≤ count919 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (5 ≤ count919 (baseVal q)) := rfl
theorem value926 (q : Snake 81) : valuation q 926 = decide (1 ≤ count926 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (2 ≤ count926 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (1 ≤ count928 (baseVal q)) := rfl
theorem value929 (q : Snake 81) : valuation q 929 = decide (2 ≤ count928 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (3 ≤ count928 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (1 ≤ count931 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (2 ≤ count931 (baseVal q)) := rfl
theorem value933 (q : Snake 81) : valuation q 933 = decide (1 ≤ count933 (baseVal q)) := rfl
theorem value934 (q : Snake 81) : valuation q 934 = decide (2 ≤ count933 (baseVal q)) := rfl
theorem value935 (q : Snake 81) : valuation q 935 = decide (1 ≤ count935 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (2 ≤ count935 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (3 ≤ count935 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (1 ≤ count939 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (2 ≤ count939 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (3 ≤ count939 (baseVal q)) := rfl
theorem value942 (q : Snake 81) : valuation q 942 = decide (4 ≤ count939 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (5 ≤ count939 (baseVal q)) := rfl
theorem value949 (q : Snake 81) : valuation q 949 = decide (4 ≤ count946 (baseVal q)) := rfl
theorem value950 (q : Snake 81) : valuation q 950 = decide (5 ≤ count946 (baseVal q)) := rfl
theorem value951 (q : Snake 81) : valuation q 951 = decide (6 ≤ count946 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (7 ≤ count946 (baseVal q)) := rfl
theorem value960 (q : Snake 81) : valuation q 960 = decide (1 ≤ count960 (baseVal q)) := rfl
theorem value961 (q : Snake 81) : valuation q 961 = decide (2 ≤ count960 (baseVal q)) := rfl
theorem value962 (q : Snake 81) : valuation q 962 = decide (1 ≤ count962 (baseVal q)) := rfl
theorem value963 (q : Snake 81) : valuation q 963 = decide (2 ≤ count962 (baseVal q)) := rfl
theorem value964 (q : Snake 81) : valuation q 964 = decide (3 ≤ count962 (baseVal q)) := rfl
theorem value965 (q : Snake 81) : valuation q 965 = decide (1 ≤ count965 (baseVal q)) := rfl
theorem value966 (q : Snake 81) : valuation q 966 = decide (2 ≤ count965 (baseVal q)) := rfl
theorem value967 (q : Snake 81) : valuation q 967 = decide (1 ≤ count967 (baseVal q)) := rfl
theorem value968 (q : Snake 81) : valuation q 968 = decide (2 ≤ count967 (baseVal q)) := rfl
theorem value969 (q : Snake 81) : valuation q 969 = decide (1 ≤ count969 (baseVal q)) := rfl
theorem value970 (q : Snake 81) : valuation q 970 = decide (2 ≤ count969 (baseVal q)) := rfl
theorem value971 (q : Snake 81) : valuation q 971 = decide (3 ≤ count969 (baseVal q)) := rfl
theorem value972 (q : Snake 81) : valuation q 972 = decide (4 ≤ count969 (baseVal q)) := rfl
theorem value973 (q : Snake 81) : valuation q 973 = decide (1 ≤ count973 (baseVal q)) := rfl
theorem value974 (q : Snake 81) : valuation q 974 = decide (2 ≤ count973 (baseVal q)) := rfl
theorem value975 (q : Snake 81) : valuation q 975 = decide (3 ≤ count973 (baseVal q)) := rfl
theorem value976 (q : Snake 81) : valuation q 976 = decide (4 ≤ count973 (baseVal q)) := rfl
theorem value977 (q : Snake 81) : valuation q 977 = decide (5 ≤ count973 (baseVal q)) := rfl
theorem value980 (q : Snake 81) : valuation q 980 = decide (1 ≤ count980 (baseVal q)) := rfl
theorem value981 (q : Snake 81) : valuation q 981 = decide (2 ≤ count980 (baseVal q)) := rfl
theorem value982 (q : Snake 81) : valuation q 982 = decide (1 ≤ count982 (baseVal q)) := rfl
theorem value983 (q : Snake 81) : valuation q 983 = decide (2 ≤ count982 (baseVal q)) := rfl
theorem value984 (q : Snake 81) : valuation q 984 = decide (1 ≤ count984 (baseVal q)) := rfl
theorem value985 (q : Snake 81) : valuation q 985 = decide (2 ≤ count984 (baseVal q)) := rfl
theorem value986 (q : Snake 81) : valuation q 986 = decide (3 ≤ count984 (baseVal q)) := rfl
theorem value987 (q : Snake 81) : valuation q 987 = decide (4 ≤ count984 (baseVal q)) := rfl
theorem value988 (q : Snake 81) : valuation q 988 = decide (1 ≤ count988 (baseVal q)) := rfl
theorem value989 (q : Snake 81) : valuation q 989 = decide (2 ≤ count988 (baseVal q)) := rfl
theorem value990 (q : Snake 81) : valuation q 990 = decide (1 ≤ count990 (baseVal q)) := rfl
theorem value992 (q : Snake 81) : valuation q 992 = decide (1 ≤ count992 (baseVal q)) := rfl
theorem value993 (q : Snake 81) : valuation q 993 = decide (2 ≤ count992 (baseVal q)) := rfl
theorem value994 (q : Snake 81) : valuation q 994 = decide (3 ≤ count992 (baseVal q)) := rfl
theorem value996 (q : Snake 81) : valuation q 996 = decide (1 ≤ count996 (baseVal q)) := rfl
theorem value997 (q : Snake 81) : valuation q 997 = decide (2 ≤ count996 (baseVal q)) := rfl
theorem value998 (q : Snake 81) : valuation q 998 = decide (3 ≤ count996 (baseVal q)) := rfl
theorem value999 (q : Snake 81) : valuation q 999 = decide (4 ≤ count996 (baseVal q)) := rfl
theorem value1000 (q : Snake 81) : valuation q 1000 = decide (5 ≤ count996 (baseVal q)) := rfl
theorem value1007 (q : Snake 81) : valuation q 1007 = decide (4 ≤ count1004 (baseVal q)) := rfl
theorem value1008 (q : Snake 81) : valuation q 1008 = decide (5 ≤ count1004 (baseVal q)) := rfl
theorem value1009 (q : Snake 81) : valuation q 1009 = decide (6 ≤ count1004 (baseVal q)) := rfl
theorem value1010 (q : Snake 81) : valuation q 1010 = decide (7 ≤ count1004 (baseVal q)) := rfl
theorem value1026 (q : Snake 81) : valuation q 1026 = decide (8 ≤ count1019 (baseVal q)) := rfl
theorem value1028 (q : Snake 81) : valuation q 1028 = decide (10 ≤ count1019 (baseVal q)) := rfl
theorem value1029 (q : Snake 81) : valuation q 1029 = decide (11 ≤ count1019 (baseVal q)) := rfl
theorem value1052 (q : Snake 81) : valuation q 1052 = decide (17 ≤ count1036 (baseVal q)) := rfl
theorem meaningNeg114 (b : Nat → Bool) : literal (valuationOf b) (-114) = decide (1 ≤ countLit b [-114]) := by
  change literal b (-114) = decide (1 ≤ countLit b [-114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-114) <;> decide
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
theorem meaningNeg108 (b : Nat → Bool) : literal (valuationOf b) (-108) = decide (1 ≤ countLit b [-108]) := by
  change literal b (-108) = decide (1 ≤ countLit b [-108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-108) <;> decide
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
theorem meaningNeg93 (b : Nat → Bool) : literal (valuationOf b) (-93) = decide (1 ≤ countLit b [-93]) := by
  change literal b (-93) = decide (1 ≤ countLit b [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-93) <;> decide
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
theorem meaningNeg81 (b : Nat → Bool) : literal (valuationOf b) (-81) = decide (1 ≤ countLit b [-81]) := by
  change literal b (-81) = decide (1 ≤ countLit b [-81])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-81) <;> decide
theorem meaningNeg80 (b : Nat → Bool) : literal (valuationOf b) (-80) = decide (1 ≤ countLit b [-80]) := by
  change literal b (-80) = decide (1 ≤ countLit b [-80])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-80) <;> decide
theorem meaningNeg78 (b : Nat → Bool) : literal (valuationOf b) (-78) = decide (1 ≤ countLit b [-78]) := by
  change literal b (-78) = decide (1 ≤ countLit b [-78])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-78) <;> decide
theorem meaningNeg76 (b : Nat → Bool) : literal (valuationOf b) (-76) = decide (1 ≤ countLit b [-76]) := by
  change literal b (-76) = decide (1 ≤ countLit b [-76])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-76) <;> decide
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
theorem meaningNeg70 (b : Nat → Bool) : literal (valuationOf b) (-70) = decide (1 ≤ countLit b [-70]) := by
  change literal b (-70) = decide (1 ≤ countLit b [-70])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-70) <;> decide
theorem meaningNeg67 (b : Nat → Bool) : literal (valuationOf b) (-67) = decide (1 ≤ countLit b [-67]) := by
  change literal b (-67) = decide (1 ≤ countLit b [-67])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-67) <;> decide
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
theorem meaningNeg51 (b : Nat → Bool) : literal (valuationOf b) (-51) = decide (1 ≤ countLit b [-51]) := by
  change literal b (-51) = decide (1 ≤ countLit b [-51])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-51) <;> decide
theorem meaningNeg49 (b : Nat → Bool) : literal (valuationOf b) (-49) = decide (1 ≤ countLit b [-49]) := by
  change literal b (-49) = decide (1 ≤ countLit b [-49])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-49) <;> decide
theorem meaningNeg48 (b : Nat → Bool) : literal (valuationOf b) (-48) = decide (1 ≤ countLit b [-48]) := by
  change literal b (-48) = decide (1 ≤ countLit b [-48])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-48) <;> decide
theorem meaningNeg47 (b : Nat → Bool) : literal (valuationOf b) (-47) = decide (1 ≤ countLit b [-47]) := by
  change literal b (-47) = decide (1 ≤ countLit b [-47])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-47) <;> decide
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
theorem meaningNeg41 (b : Nat → Bool) : literal (valuationOf b) (-41) = decide (1 ≤ countLit b [-41]) := by
  change literal b (-41) = decide (1 ≤ countLit b [-41])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-41) <;> decide
theorem meaningNeg40 (b : Nat → Bool) : literal (valuationOf b) (-40) = decide (1 ≤ countLit b [-40]) := by
  change literal b (-40) = decide (1 ≤ countLit b [-40])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-40) <;> decide
theorem meaningNeg38 (b : Nat → Bool) : literal (valuationOf b) (-38) = decide (1 ≤ countLit b [-38]) := by
  change literal b (-38) = decide (1 ≤ countLit b [-38])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-38) <;> decide
theorem meaningNeg37 (b : Nat → Bool) : literal (valuationOf b) (-37) = decide (1 ≤ countLit b [-37]) := by
  change literal b (-37) = decide (1 ≤ countLit b [-37])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-37) <;> decide
theorem meaningNeg34 (b : Nat → Bool) : literal (valuationOf b) (-34) = decide (1 ≤ countLit b [-34]) := by
  change literal b (-34) = decide (1 ≤ countLit b [-34])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-34) <;> decide
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
theorem meaningNeg24 (b : Nat → Bool) : literal (valuationOf b) (-24) = decide (1 ≤ countLit b [-24]) := by
  change literal b (-24) = decide (1 ≤ countLit b [-24])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-24) <;> decide
theorem meaningNeg20 (b : Nat → Bool) : literal (valuationOf b) (-20) = decide (1 ≤ countLit b [-20]) := by
  change literal b (-20) = decide (1 ≤ countLit b [-20])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-20) <;> decide
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
theorem meaningNeg6 (b : Nat → Bool) : literal (valuationOf b) (-6) = decide (1 ≤ countLit b [-6]) := by
  change literal b (-6) = decide (1 ≤ countLit b [-6])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-6) <;> decide
theorem meaningNeg3 (b : Nat → Bool) : literal (valuationOf b) (-3) = decide (1 ≤ countLit b [-3]) := by
  change literal b (-3) = decide (1 ≤ countLit b [-3])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-3) <;> decide
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning118 (b : Nat → Bool) : literal (valuationOf b) (118) = decide (1 ≤ countLit b [118]) := by
  change literal b (118) = decide (1 ≤ countLit b [118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (118) <;> decide
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
theorem meaning123 (b : Nat → Bool) : literal (valuationOf b) (123) = decide (1 ≤ countLit b [123]) := by
  change literal b (123) = decide (1 ≤ countLit b [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (123) <;> decide
theorem meaning127 (b : Nat → Bool) : literal (valuationOf b) (127) = decide (1 ≤ countLit b [127]) := by
  change literal b (127) = decide (1 ≤ countLit b [127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (127) <;> decide
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
theorem meaning130 (b : Nat → Bool) : literal (valuationOf b) (130) = decide (1 ≤ countLit b [130]) := by
  change literal b (130) = decide (1 ≤ countLit b [130])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (130) <;> decide
theorem meaning134 (b : Nat → Bool) : literal (valuationOf b) (134) = decide (1 ≤ countLit b [134]) := by
  change literal b (134) = decide (1 ≤ countLit b [134])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (134) <;> decide
theorem meaning135 (b : Nat → Bool) : literal (valuationOf b) (135) = decide (1 ≤ countLit b [135]) := by
  change literal b (135) = decide (1 ≤ countLit b [135])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (135) <;> decide
theorem meaning137 (b : Nat → Bool) : literal (valuationOf b) (137) = decide (1 ≤ countLit b [137]) := by
  change literal b (137) = decide (1 ≤ countLit b [137])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (137) <;> decide
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
theorem meaning139 (b : Nat → Bool) : literal (valuationOf b) (139) = decide (1 ≤ countLit b [139]) := by
  change literal b (139) = decide (1 ≤ countLit b [139])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (139) <;> decide
theorem meaning141 (b : Nat → Bool) : literal (valuationOf b) (141) = decide (1 ≤ countLit b [141]) := by
  change literal b (141) = decide (1 ≤ countLit b [141])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (141) <;> decide
theorem meaning144 (b : Nat → Bool) : literal (valuationOf b) (144) = decide (1 ≤ countLit b [144]) := by
  change literal b (144) = decide (1 ≤ countLit b [144])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (144) <;> decide
theorem meaning145 (b : Nat → Bool) : literal (valuationOf b) (145) = decide (1 ≤ countLit b [145]) := by
  change literal b (145) = decide (1 ≤ countLit b [145])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (145) <;> decide
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
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
theorem meaning162 (b : Nat → Bool) : literal (valuationOf b) (162) = decide (1 ≤ countLit b [162]) := by
  change literal b (162) = decide (1 ≤ countLit b [162])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (162) <;> decide
theorem meaning168 (b : Nat → Bool) : literal (valuationOf b) (168) = decide (1 ≤ countLit b [168]) := by
  change literal b (168) = decide (1 ≤ countLit b [168])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (168) <;> decide
theorem meaning169 (b : Nat → Bool) : literal (valuationOf b) (169) = decide (1 ≤ countLit b [169]) := by
  change literal b (169) = decide (1 ≤ countLit b [169])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (169) <;> decide
theorem meaning177 (b : Nat → Bool) : literal (valuationOf b) (177) = decide (1 ≤ countLit b [177]) := by
  change literal b (177) = decide (1 ≤ countLit b [177])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (177) <;> decide
theorem meaning179 (b : Nat → Bool) : literal (valuationOf b) (179) = decide (1 ≤ countLit b [179]) := by
  change literal b (179) = decide (1 ≤ countLit b [179])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (179) <;> decide
theorem meaning184 (b : Nat → Bool) : literal (valuationOf b) (184) = decide (1 ≤ countLit b [184]) := by
  change literal b (184) = decide (1 ≤ countLit b [184])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (184) <;> decide
theorem meaning191 (b : Nat → Bool) : literal (valuationOf b) (191) = decide (1 ≤ countLit b [191]) := by
  change literal b (191) = decide (1 ≤ countLit b [191])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (191) <;> decide
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
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
theorem meaning226 (b : Nat → Bool) : literal (valuationOf b) (226) = decide (1 ≤ countLit b [226]) := by
  change literal b (226) = decide (1 ≤ countLit b [226])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (226) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) 238 = decide (2 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) 242 = decide (2 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) 244 = decide (2 ≤ count243 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning264 (b : Nat → Bool) : literal (valuationOf b) 264 = decide (2 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning268 (b : Nat → Bool) : literal (valuationOf b) 268 = decide (2 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning274 (b : Nat → Bool) : literal (valuationOf b) 274 = decide (2 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning284 (b : Nat → Bool) : literal (valuationOf b) 284 = decide (2 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning286 (b : Nat → Bool) : literal (valuationOf b) 286 = decide (2 ≤ count285 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning460 (b : Nat → Bool) : literal (valuationOf b) 460 = decide (2 ≤ count459 b) := rfl
theorem meaning781 (b : Nat → Bool) : literal (valuationOf b) 781 = decide (1 ≤ count781 b) := rfl
theorem meaning782 (b : Nat → Bool) : literal (valuationOf b) 782 = decide (2 ≤ count781 b) := rfl
theorem meaning783 (b : Nat → Bool) : literal (valuationOf b) 783 = decide (1 ≤ count783 b) := rfl
theorem meaning784 (b : Nat → Bool) : literal (valuationOf b) 784 = decide (2 ≤ count783 b) := rfl
theorem meaning786 (b : Nat → Bool) : literal (valuationOf b) 786 = decide (1 ≤ count786 b) := rfl
theorem meaning787 (b : Nat → Bool) : literal (valuationOf b) 787 = decide (2 ≤ count786 b) := rfl
theorem meaning788 (b : Nat → Bool) : literal (valuationOf b) 788 = decide (1 ≤ count788 b) := rfl
theorem meaning789 (b : Nat → Bool) : literal (valuationOf b) 789 = decide (2 ≤ count788 b) := rfl
theorem meaning790 (b : Nat → Bool) : literal (valuationOf b) 790 = decide (1 ≤ count790 b) := rfl
theorem meaning791 (b : Nat → Bool) : literal (valuationOf b) 791 = decide (2 ≤ count790 b) := rfl
theorem meaning792 (b : Nat → Bool) : literal (valuationOf b) 792 = decide (3 ≤ count790 b) := rfl
theorem meaning793 (b : Nat → Bool) : literal (valuationOf b) 793 = decide (4 ≤ count790 b) := rfl
theorem meaning794 (b : Nat → Bool) : literal (valuationOf b) 794 = decide (1 ≤ count794 b) := rfl
theorem meaning795 (b : Nat → Bool) : literal (valuationOf b) 795 = decide (2 ≤ count794 b) := rfl
theorem meaning796 (b : Nat → Bool) : literal (valuationOf b) 796 = decide (3 ≤ count794 b) := rfl
theorem meaning797 (b : Nat → Bool) : literal (valuationOf b) 797 = decide (4 ≤ count794 b) := rfl
theorem meaning801 (b : Nat → Bool) : literal (valuationOf b) 801 = decide (1 ≤ count801 b) := rfl
theorem meaning802 (b : Nat → Bool) : literal (valuationOf b) 802 = decide (2 ≤ count801 b) := rfl
theorem meaning803 (b : Nat → Bool) : literal (valuationOf b) 803 = decide (1 ≤ count803 b) := rfl
theorem meaning804 (b : Nat → Bool) : literal (valuationOf b) 804 = decide (2 ≤ count803 b) := rfl
theorem meaning805 (b : Nat → Bool) : literal (valuationOf b) 805 = decide (3 ≤ count803 b) := rfl
theorem meaning806 (b : Nat → Bool) : literal (valuationOf b) 806 = decide (1 ≤ count806 b) := rfl
theorem meaning807 (b : Nat → Bool) : literal (valuationOf b) 807 = decide (2 ≤ count806 b) := rfl
theorem meaning808 (b : Nat → Bool) : literal (valuationOf b) 808 = decide (1 ≤ count808 b) := rfl
theorem meaning809 (b : Nat → Bool) : literal (valuationOf b) 809 = decide (2 ≤ count808 b) := rfl
theorem meaning810 (b : Nat → Bool) : literal (valuationOf b) 810 = decide (1 ≤ count810 b) := rfl
theorem meaning811 (b : Nat → Bool) : literal (valuationOf b) 811 = decide (2 ≤ count810 b) := rfl
theorem meaning812 (b : Nat → Bool) : literal (valuationOf b) 812 = decide (3 ≤ count810 b) := rfl
theorem meaning814 (b : Nat → Bool) : literal (valuationOf b) 814 = decide (1 ≤ count814 b) := rfl
theorem meaning815 (b : Nat → Bool) : literal (valuationOf b) 815 = decide (2 ≤ count814 b) := rfl
theorem meaning816 (b : Nat → Bool) : literal (valuationOf b) 816 = decide (3 ≤ count814 b) := rfl
theorem meaning817 (b : Nat → Bool) : literal (valuationOf b) 817 = decide (4 ≤ count814 b) := rfl
theorem meaning822 (b : Nat → Bool) : literal (valuationOf b) 822 = decide (2 ≤ count821 b) := rfl
theorem meaning823 (b : Nat → Bool) : literal (valuationOf b) 823 = decide (3 ≤ count821 b) := rfl
theorem meaning824 (b : Nat → Bool) : literal (valuationOf b) 824 = decide (4 ≤ count821 b) := rfl
theorem meaning825 (b : Nat → Bool) : literal (valuationOf b) 825 = decide (5 ≤ count821 b) := rfl
theorem meaning826 (b : Nat → Bool) : literal (valuationOf b) 826 = decide (6 ≤ count821 b) := rfl
theorem meaning835 (b : Nat → Bool) : literal (valuationOf b) 835 = decide (1 ≤ count835 b) := rfl
theorem meaning836 (b : Nat → Bool) : literal (valuationOf b) 836 = decide (2 ≤ count835 b) := rfl
theorem meaning837 (b : Nat → Bool) : literal (valuationOf b) 837 = decide (1 ≤ count837 b) := rfl
theorem meaning838 (b : Nat → Bool) : literal (valuationOf b) 838 = decide (2 ≤ count837 b) := rfl
theorem meaning840 (b : Nat → Bool) : literal (valuationOf b) 840 = decide (1 ≤ count840 b) := rfl
theorem meaning841 (b : Nat → Bool) : literal (valuationOf b) 841 = decide (2 ≤ count840 b) := rfl
theorem meaning842 (b : Nat → Bool) : literal (valuationOf b) 842 = decide (1 ≤ count842 b) := rfl
theorem meaning843 (b : Nat → Bool) : literal (valuationOf b) 843 = decide (2 ≤ count842 b) := rfl
theorem meaning844 (b : Nat → Bool) : literal (valuationOf b) 844 = decide (1 ≤ count844 b) := rfl
theorem meaning845 (b : Nat → Bool) : literal (valuationOf b) 845 = decide (2 ≤ count844 b) := rfl
theorem meaning846 (b : Nat → Bool) : literal (valuationOf b) 846 = decide (3 ≤ count844 b) := rfl
theorem meaning848 (b : Nat → Bool) : literal (valuationOf b) 848 = decide (1 ≤ count848 b) := rfl
theorem meaning849 (b : Nat → Bool) : literal (valuationOf b) 849 = decide (2 ≤ count848 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (3 ≤ count848 b) := rfl
theorem meaning851 (b : Nat → Bool) : literal (valuationOf b) 851 = decide (4 ≤ count848 b) := rfl
theorem meaning855 (b : Nat → Bool) : literal (valuationOf b) 855 = decide (1 ≤ count855 b) := rfl
theorem meaning856 (b : Nat → Bool) : literal (valuationOf b) 856 = decide (2 ≤ count855 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (1 ≤ count857 b) := rfl
theorem meaning858 (b : Nat → Bool) : literal (valuationOf b) 858 = decide (2 ≤ count857 b) := rfl
theorem meaning860 (b : Nat → Bool) : literal (valuationOf b) 860 = decide (1 ≤ count860 b) := rfl
theorem meaning861 (b : Nat → Bool) : literal (valuationOf b) 861 = decide (2 ≤ count860 b) := rfl
theorem meaning862 (b : Nat → Bool) : literal (valuationOf b) 862 = decide (1 ≤ count862 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (2 ≤ count862 b) := rfl
theorem meaning864 (b : Nat → Bool) : literal (valuationOf b) 864 = decide (1 ≤ count864 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (2 ≤ count864 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (3 ≤ count864 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (1 ≤ count868 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (2 ≤ count868 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (3 ≤ count868 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (4 ≤ count868 b) := rfl
theorem meaning875 (b : Nat → Bool) : literal (valuationOf b) 875 = decide (1 ≤ count875 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (2 ≤ count875 b) := rfl
theorem meaning877 (b : Nat → Bool) : literal (valuationOf b) 877 = decide (3 ≤ count875 b) := rfl
theorem meaning878 (b : Nat → Bool) : literal (valuationOf b) 878 = decide (4 ≤ count875 b) := rfl
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (5 ≤ count875 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (7 ≤ count875 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (6 ≤ count889 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (7 ≤ count889 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (9 ≤ count889 b) := rfl
theorem meaning906 (b : Nat → Bool) : literal (valuationOf b) 906 = decide (1 ≤ count906 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (2 ≤ count906 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (1 ≤ count908 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (2 ≤ count908 b) := rfl
theorem meaning910 (b : Nat → Bool) : literal (valuationOf b) 910 = decide (3 ≤ count908 b) := rfl
theorem meaning911 (b : Nat → Bool) : literal (valuationOf b) 911 = decide (1 ≤ count911 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (2 ≤ count911 b) := rfl
theorem meaning913 (b : Nat → Bool) : literal (valuationOf b) 913 = decide (1 ≤ count913 b) := rfl
theorem meaning914 (b : Nat → Bool) : literal (valuationOf b) 914 = decide (2 ≤ count913 b) := rfl
theorem meaning915 (b : Nat → Bool) : literal (valuationOf b) 915 = decide (1 ≤ count915 b) := rfl
theorem meaning916 (b : Nat → Bool) : literal (valuationOf b) 916 = decide (2 ≤ count915 b) := rfl
theorem meaning917 (b : Nat → Bool) : literal (valuationOf b) 917 = decide (3 ≤ count915 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (1 ≤ count919 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (2 ≤ count919 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (3 ≤ count919 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (4 ≤ count919 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (5 ≤ count919 b) := rfl
theorem meaning926 (b : Nat → Bool) : literal (valuationOf b) 926 = decide (1 ≤ count926 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (2 ≤ count926 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (1 ≤ count928 b) := rfl
theorem meaning929 (b : Nat → Bool) : literal (valuationOf b) 929 = decide (2 ≤ count928 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (3 ≤ count928 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (1 ≤ count931 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (2 ≤ count931 b) := rfl
theorem meaning933 (b : Nat → Bool) : literal (valuationOf b) 933 = decide (1 ≤ count933 b) := rfl
theorem meaning934 (b : Nat → Bool) : literal (valuationOf b) 934 = decide (2 ≤ count933 b) := rfl
theorem meaning935 (b : Nat → Bool) : literal (valuationOf b) 935 = decide (1 ≤ count935 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (2 ≤ count935 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (3 ≤ count935 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (1 ≤ count939 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (2 ≤ count939 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (3 ≤ count939 b) := rfl
theorem meaning942 (b : Nat → Bool) : literal (valuationOf b) 942 = decide (4 ≤ count939 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (5 ≤ count939 b) := rfl
theorem meaning949 (b : Nat → Bool) : literal (valuationOf b) 949 = decide (4 ≤ count946 b) := rfl
theorem meaning950 (b : Nat → Bool) : literal (valuationOf b) 950 = decide (5 ≤ count946 b) := rfl
theorem meaning951 (b : Nat → Bool) : literal (valuationOf b) 951 = decide (6 ≤ count946 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (7 ≤ count946 b) := rfl
theorem meaning960 (b : Nat → Bool) : literal (valuationOf b) 960 = decide (1 ≤ count960 b) := rfl
theorem meaning961 (b : Nat → Bool) : literal (valuationOf b) 961 = decide (2 ≤ count960 b) := rfl
theorem meaning962 (b : Nat → Bool) : literal (valuationOf b) 962 = decide (1 ≤ count962 b) := rfl
theorem meaning963 (b : Nat → Bool) : literal (valuationOf b) 963 = decide (2 ≤ count962 b) := rfl
theorem meaning964 (b : Nat → Bool) : literal (valuationOf b) 964 = decide (3 ≤ count962 b) := rfl
theorem meaning965 (b : Nat → Bool) : literal (valuationOf b) 965 = decide (1 ≤ count965 b) := rfl
theorem meaning966 (b : Nat → Bool) : literal (valuationOf b) 966 = decide (2 ≤ count965 b) := rfl
theorem meaning967 (b : Nat → Bool) : literal (valuationOf b) 967 = decide (1 ≤ count967 b) := rfl
theorem meaning968 (b : Nat → Bool) : literal (valuationOf b) 968 = decide (2 ≤ count967 b) := rfl
theorem meaning969 (b : Nat → Bool) : literal (valuationOf b) 969 = decide (1 ≤ count969 b) := rfl
theorem meaning970 (b : Nat → Bool) : literal (valuationOf b) 970 = decide (2 ≤ count969 b) := rfl
theorem meaning971 (b : Nat → Bool) : literal (valuationOf b) 971 = decide (3 ≤ count969 b) := rfl
theorem meaning972 (b : Nat → Bool) : literal (valuationOf b) 972 = decide (4 ≤ count969 b) := rfl
theorem meaning973 (b : Nat → Bool) : literal (valuationOf b) 973 = decide (1 ≤ count973 b) := rfl
theorem meaning974 (b : Nat → Bool) : literal (valuationOf b) 974 = decide (2 ≤ count973 b) := rfl
theorem meaning975 (b : Nat → Bool) : literal (valuationOf b) 975 = decide (3 ≤ count973 b) := rfl
theorem meaning976 (b : Nat → Bool) : literal (valuationOf b) 976 = decide (4 ≤ count973 b) := rfl
theorem meaning977 (b : Nat → Bool) : literal (valuationOf b) 977 = decide (5 ≤ count973 b) := rfl
theorem meaning980 (b : Nat → Bool) : literal (valuationOf b) 980 = decide (1 ≤ count980 b) := rfl
theorem meaning981 (b : Nat → Bool) : literal (valuationOf b) 981 = decide (2 ≤ count980 b) := rfl
theorem meaning982 (b : Nat → Bool) : literal (valuationOf b) 982 = decide (1 ≤ count982 b) := rfl
theorem meaning983 (b : Nat → Bool) : literal (valuationOf b) 983 = decide (2 ≤ count982 b) := rfl
theorem meaning984 (b : Nat → Bool) : literal (valuationOf b) 984 = decide (1 ≤ count984 b) := rfl
theorem meaning985 (b : Nat → Bool) : literal (valuationOf b) 985 = decide (2 ≤ count984 b) := rfl
theorem meaning986 (b : Nat → Bool) : literal (valuationOf b) 986 = decide (3 ≤ count984 b) := rfl
theorem meaning987 (b : Nat → Bool) : literal (valuationOf b) 987 = decide (4 ≤ count984 b) := rfl
theorem meaning988 (b : Nat → Bool) : literal (valuationOf b) 988 = decide (1 ≤ count988 b) := rfl
theorem meaning989 (b : Nat → Bool) : literal (valuationOf b) 989 = decide (2 ≤ count988 b) := rfl
theorem meaning990 (b : Nat → Bool) : literal (valuationOf b) 990 = decide (1 ≤ count990 b) := rfl
theorem meaning992 (b : Nat → Bool) : literal (valuationOf b) 992 = decide (1 ≤ count992 b) := rfl
theorem meaning993 (b : Nat → Bool) : literal (valuationOf b) 993 = decide (2 ≤ count992 b) := rfl
theorem meaning994 (b : Nat → Bool) : literal (valuationOf b) 994 = decide (3 ≤ count992 b) := rfl
theorem meaning996 (b : Nat → Bool) : literal (valuationOf b) 996 = decide (1 ≤ count996 b) := rfl
theorem meaning997 (b : Nat → Bool) : literal (valuationOf b) 997 = decide (2 ≤ count996 b) := rfl
theorem meaning998 (b : Nat → Bool) : literal (valuationOf b) 998 = decide (3 ≤ count996 b) := rfl
theorem meaning999 (b : Nat → Bool) : literal (valuationOf b) 999 = decide (4 ≤ count996 b) := rfl
theorem meaning1000 (b : Nat → Bool) : literal (valuationOf b) 1000 = decide (5 ≤ count996 b) := rfl
theorem meaning1007 (b : Nat → Bool) : literal (valuationOf b) 1007 = decide (4 ≤ count1004 b) := rfl
theorem meaning1008 (b : Nat → Bool) : literal (valuationOf b) 1008 = decide (5 ≤ count1004 b) := rfl
theorem meaning1009 (b : Nat → Bool) : literal (valuationOf b) 1009 = decide (6 ≤ count1004 b) := rfl
theorem meaning1010 (b : Nat → Bool) : literal (valuationOf b) 1010 = decide (7 ≤ count1004 b) := rfl
theorem meaning1026 (b : Nat → Bool) : literal (valuationOf b) 1026 = decide (8 ≤ count1019 b) := rfl
theorem meaning1028 (b : Nat → Bool) : literal (valuationOf b) 1028 = decide (10 ≤ count1019 b) := rfl
theorem meaning1029 (b : Nat → Bool) : literal (valuationOf b) 1029 = decide (11 ≤ count1019 b) := rfl
theorem meaning1052 (b : Nat → Bool) : literal (valuationOf b) 1052 = decide (17 ≤ count1036 b) := rfl
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
end Snake9.Regrowth.E112051
