import E112152Data
namespace Snake9.Regrowth.E112152
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 120 then (if i < 60 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (9 : Vertex)) else decide (InPath q (17 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (19 : Vertex)) else decide (InPath q (25 : Vertex))) else (if i < 6 then decide (InPath q (33 : Vertex)) else decide (InPath q (35 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (39 : Vertex)) else decide (InPath q (41 : Vertex))) else (if i < 10 then decide (InPath q (45 : Vertex)) else decide (InPath q (96 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (98 : Vertex)) else decide (InPath q (102 : Vertex))) else (if i < 14 then decide (InPath q (103 : Vertex)) else decide (InPath q (104 : Vertex)))))) else (if i < 22 then (if i < 18 then (if i < 16 then decide (InPath q (105 : Vertex)) else (if i < 17 then decide (InPath q (110 : Vertex)) else decide (InPath q (111 : Vertex)))) else (if i < 20 then (if i < 19 then decide (InPath q (113 : Vertex)) else decide (InPath q (114 : Vertex))) else (if i < 21 then decide (InPath q (115 : Vertex)) else decide (InPath q (117 : Vertex))))) else (if i < 26 then (if i < 24 then (if i < 23 then decide (InPath q (121 : Vertex)) else decide (InPath q (124 : Vertex))) else (if i < 25 then decide (InPath q (125 : Vertex)) else decide (InPath q (126 : Vertex)))) else (if i < 28 then (if i < 27 then decide (InPath q (160 : Vertex)) else decide (InPath q (162 : Vertex))) else (if i < 29 then decide (InPath q (166 : Vertex)) else decide (InPath q (167 : Vertex))))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then decide (InPath q (168 : Vertex)) else (if i < 32 then decide (InPath q (169 : Vertex)) else decide (InPath q (170 : Vertex)))) else (if i < 35 then (if i < 34 then decide (InPath q (174 : Vertex)) else decide (InPath q (175 : Vertex))) else (if i < 36 then decide (InPath q (177 : Vertex)) else decide (InPath q (178 : Vertex))))) else (if i < 41 then (if i < 39 then (if i < 38 then decide (InPath q (179 : Vertex)) else decide (InPath q (181 : Vertex))) else (if i < 40 then decide (InPath q (185 : Vertex)) else decide (InPath q (188 : Vertex)))) else (if i < 43 then (if i < 42 then decide (InPath q (189 : Vertex)) else decide (InPath q (190 : Vertex))) else (if i < 44 then decide (InPath q (225 : Vertex)) else decide (InPath q (227 : Vertex)))))) else (if i < 52 then (if i < 48 then (if i < 46 then decide (InPath q (228 : Vertex)) else (if i < 47 then decide (InPath q (229 : Vertex)) else decide (InPath q (230 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (234 : Vertex)) else decide (InPath q (235 : Vertex))) else (if i < 51 then decide (InPath q (236 : Vertex)) else decide (InPath q (237 : Vertex))))) else (if i < 56 then (if i < 54 then (if i < 53 then decide (InPath q (240 : Vertex)) else decide (InPath q (244 : Vertex))) else (if i < 55 then decide (InPath q (246 : Vertex)) else decide (InPath q (247 : Vertex)))) else (if i < 58 then (if i < 57 then decide (InPath q (248 : Vertex)) else decide (InPath q (249 : Vertex))) else (if i < 59 then decide (InPath q (250 : Vertex)) else decide (InPath q (251 : Vertex)))))))) else (if i < 90 then (if i < 75 then (if i < 67 then (if i < 63 then (if i < 61 then decide (InPath q (255 : Vertex)) else (if i < 62 then decide (InPath q (353 : Vertex)) else decide (InPath q (355 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (357 : Vertex)) else decide (InPath q (358 : Vertex))) else (if i < 66 then decide (InPath q (361 : Vertex)) else decide (InPath q (363 : Vertex))))) else (if i < 71 then (if i < 69 then (if i < 68 then decide (InPath q (364 : Vertex)) else decide (InPath q (365 : Vertex))) else (if i < 70 then decide (InPath q (368 : Vertex)) else decide (InPath q (372 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (373 : Vertex)) else decide (InPath q (374 : Vertex))) else (if i < 74 then decide (InPath q (375 : Vertex)) else decide (InPath q (376 : Vertex)))))) else (if i < 82 then (if i < 78 then (if i < 76 then decide (InPath q (378 : Vertex)) else (if i < 77 then decide (InPath q (379 : Vertex)) else decide (InPath q (383 : Vertex)))) else (if i < 80 then (if i < 79 then decide (InPath q (417 : Vertex)) else decide (InPath q (419 : Vertex))) else (if i < 81 then decide (InPath q (421 : Vertex)) else decide (InPath q (422 : Vertex))))) else (if i < 86 then (if i < 84 then (if i < 83 then decide (InPath q (423 : Vertex)) else decide (InPath q (424 : Vertex))) else (if i < 85 then decide (InPath q (425 : Vertex)) else decide (InPath q (427 : Vertex)))) else (if i < 88 then (if i < 87 then decide (InPath q (428 : Vertex)) else decide (InPath q (429 : Vertex))) else (if i < 89 then decide (InPath q (431 : Vertex)) else decide (InPath q (432 : Vertex))))))) else (if i < 105 then (if i < 97 then (if i < 93 then (if i < 91 then decide (InPath q (434 : Vertex)) else (if i < 92 then decide (InPath q (436 : Vertex)) else decide (InPath q (437 : Vertex)))) else (if i < 95 then (if i < 94 then decide (InPath q (438 : Vertex)) else decide (InPath q (440 : Vertex))) else (if i < 96 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex))))) else (if i < 101 then (if i < 99 then (if i < 98 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex))) else (if i < 100 then decide (InPath q (481 : Vertex)) else decide (InPath q (482 : Vertex)))) else (if i < 103 then (if i < 102 then decide (InPath q (483 : Vertex)) else decide (InPath q (485 : Vertex))) else (if i < 104 then decide (InPath q (486 : Vertex)) else decide (InPath q (488 : Vertex)))))) else (if i < 112 then (if i < 108 then (if i < 106 then decide (InPath q (490 : Vertex)) else (if i < 107 then decide (InPath q (492 : Vertex)) else decide (InPath q (493 : Vertex)))) else (if i < 110 then (if i < 109 then decide (InPath q (494 : Vertex)) else decide (InPath q (495 : Vertex))) else (if i < 111 then decide (InPath q (497 : Vertex)) else decide (InPath q (498 : Vertex))))) else (if i < 116 then (if i < 114 then (if i < 113 then decide (InPath q (499 : Vertex)) else decide (InPath q (501 : Vertex))) else (if i < 115 then decide (InPath q (502 : Vertex)) else decide (InPath q (503 : Vertex)))) else (if i < 118 then (if i < 117 then decide (InPath q (505 : Vertex)) else decide (InPath q (508 : Vertex))) else (if i < 119 then decide (InPath q (509 : Vertex)) else decide (InPath q (510 : Vertex))))))))) else (if i < 180 then (if i < 150 then (if i < 135 then (if i < 127 then (if i < 123 then (if i < 121 then decide (InPath q (511 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (9 : Vertex)) else decide (BallClauseLogic.Endpoint q (17 : Vertex)))) else (if i < 125 then (if i < 124 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (25 : Vertex))) else (if i < 126 then decide (BallClauseLogic.Endpoint q (33 : Vertex)) else decide (BallClauseLogic.Endpoint q (35 : Vertex))))) else (if i < 131 then (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (39 : Vertex)) else decide (BallClauseLogic.Endpoint q (41 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (45 : Vertex)) else decide (BallClauseLogic.Endpoint q (96 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (98 : Vertex)) else decide (BallClauseLogic.Endpoint q (102 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (104 : Vertex)))))) else (if i < 142 then (if i < 138 then (if i < 136 then decide (BallClauseLogic.Endpoint q (105 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (110 : Vertex)) else decide (BallClauseLogic.Endpoint q (111 : Vertex)))) else (if i < 140 then (if i < 139 then decide (BallClauseLogic.Endpoint q (113 : Vertex)) else decide (BallClauseLogic.Endpoint q (114 : Vertex))) else (if i < 141 then decide (BallClauseLogic.Endpoint q (115 : Vertex)) else decide (BallClauseLogic.Endpoint q (117 : Vertex))))) else (if i < 146 then (if i < 144 then (if i < 143 then decide (BallClauseLogic.Endpoint q (121 : Vertex)) else decide (BallClauseLogic.Endpoint q (124 : Vertex))) else (if i < 145 then decide (BallClauseLogic.Endpoint q (125 : Vertex)) else decide (BallClauseLogic.Endpoint q (126 : Vertex)))) else (if i < 148 then (if i < 147 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (162 : Vertex))) else (if i < 149 then decide (BallClauseLogic.Endpoint q (166 : Vertex)) else decide (BallClauseLogic.Endpoint q (167 : Vertex))))))) else (if i < 165 then (if i < 157 then (if i < 153 then (if i < 151 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else (if i < 152 then decide (BallClauseLogic.Endpoint q (169 : Vertex)) else decide (BallClauseLogic.Endpoint q (170 : Vertex)))) else (if i < 155 then (if i < 154 then decide (BallClauseLogic.Endpoint q (174 : Vertex)) else decide (BallClauseLogic.Endpoint q (175 : Vertex))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (178 : Vertex))))) else (if i < 161 then (if i < 159 then (if i < 158 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (181 : Vertex))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (185 : Vertex)) else decide (BallClauseLogic.Endpoint q (188 : Vertex)))) else (if i < 163 then (if i < 162 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (190 : Vertex))) else (if i < 164 then decide (BallClauseLogic.Endpoint q (225 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex)))))) else (if i < 172 then (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (234 : Vertex)) else decide (BallClauseLogic.Endpoint q (235 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else decide (BallClauseLogic.Endpoint q (237 : Vertex))))) else (if i < 176 then (if i < 174 then (if i < 173 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (244 : Vertex))) else (if i < 175 then decide (BallClauseLogic.Endpoint q (246 : Vertex)) else decide (BallClauseLogic.Endpoint q (247 : Vertex)))) else (if i < 178 then (if i < 177 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else decide (BallClauseLogic.Endpoint q (249 : Vertex))) else (if i < 179 then decide (BallClauseLogic.Endpoint q (250 : Vertex)) else decide (BallClauseLogic.Endpoint q (251 : Vertex)))))))) else (if i < 210 then (if i < 195 then (if i < 187 then (if i < 183 then (if i < 181 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else (if i < 182 then decide (BallClauseLogic.Endpoint q (353 : Vertex)) else decide (BallClauseLogic.Endpoint q (355 : Vertex)))) else (if i < 185 then (if i < 184 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (358 : Vertex))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (361 : Vertex)) else decide (BallClauseLogic.Endpoint q (363 : Vertex))))) else (if i < 191 then (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (364 : Vertex)) else decide (BallClauseLogic.Endpoint q (365 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (368 : Vertex)) else decide (BallClauseLogic.Endpoint q (372 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (373 : Vertex)) else decide (BallClauseLogic.Endpoint q (374 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (375 : Vertex)) else decide (BallClauseLogic.Endpoint q (376 : Vertex)))))) else (if i < 202 then (if i < 198 then (if i < 196 then decide (BallClauseLogic.Endpoint q (378 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else decide (BallClauseLogic.Endpoint q (383 : Vertex)))) else (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (417 : Vertex)) else decide (BallClauseLogic.Endpoint q (419 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex))))) else (if i < 206 then (if i < 204 then (if i < 203 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))) else (if i < 205 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex)))) else (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else decide (BallClauseLogic.Endpoint q (429 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (431 : Vertex)) else decide (BallClauseLogic.Endpoint q (432 : Vertex))))))) else (if i < 225 then (if i < 217 then (if i < 213 then (if i < 211 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else (if i < 212 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex)))) else (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (438 : Vertex)) else decide (BallClauseLogic.Endpoint q (440 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (442 : Vertex)) else decide (BallClauseLogic.Endpoint q (443 : Vertex))))) else (if i < 221 then (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else decide (BallClauseLogic.Endpoint q (480 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (482 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (483 : Vertex)) else decide (BallClauseLogic.Endpoint q (485 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))))) else (if i < 233 then (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (490 : Vertex)) else decide (BallClauseLogic.Endpoint q (492 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (494 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else decide (BallClauseLogic.Endpoint q (499 : Vertex))))) else (if i < 237 then (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (503 : Vertex)) else decide (BallClauseLogic.Endpoint q (505 : Vertex)))) else (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (508 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (510 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count241 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [121, 122, 123]
def count245 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count247 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127]
def count253 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count289 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145, 146, 147, 148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count295 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156]
def count309 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count313 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count347 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179]
def count349 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178, 179]
def count351 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]
def count353 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]
def count355 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179]
def count357 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [180, 181, 182]
def count361 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count363 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186]
def count367 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186]
def count369 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [191, 192, 194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195]
def count385 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count393 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201, 202]
def count397 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count401 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count407 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210]
def count409 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206, 207, 208, 209, 210]
def count411 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210]
def count415 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [211, 212, 213]
def count419 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count421 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count423 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214, 215, 216, 217]
def count427 (b : Nat → Bool) : Nat := countLit b [218, 219]
def count429 (b : Nat → Bool) : Nat := countLit b [220, 221]
def count431 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221]
def count433 (b : Nat → Bool) : Nat := countLit b [222, 223]
def count435 (b : Nat → Bool) : Nat := countLit b [224, 225]
def count437 (b : Nat → Bool) : Nat := countLit b [222, 223, 224, 225]
def count439 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224, 225]
def count441 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]
def count443 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [226, 227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count451 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [226, 227, 228, 229, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count459 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count465 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236, 237, 238, 239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]
def count473 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]
def count475 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]
def count477 (b : Nat → Bool) : Nat := countLit b [2, 5]
def count479 (b : Nat → Bool) : Nat := countLit b [1, 2, 5]
def count482 (b : Nat → Bool) : Nat := countLit b [7, 9]
def count484 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count486 (b : Nat → Bool) : Nat := countLit b [7, 9, 10, 12]
def count490 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 9, 10, 12]
def count497 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count499 (b : Nat → Bool) : Nat := countLit b [18, 19]
def count501 (b : Nat → Bool) : Nat := countLit b [15, 17, 18, 19]
def count505 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count507 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count509 (b : Nat → Bool) : Nat := countLit b [24, 25, 26, 28]
def count513 (b : Nat → Bool) : Nat := countLit b [15, 17, 18, 19, 24, 25, 26, 28]
def count521 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 9, 10, 12, 15, 17, 18, 19, 24, 25, 26, 28]
def count536 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count538 (b : Nat → Bool) : Nat := countLit b [31, 32, 34]
def count541 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count543 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count545 (b : Nat → Bool) : Nat := countLit b [35, 36, 41, 42]
def count549 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 35, 36, 41, 42]
def count556 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count558 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count560 (b : Nat → Bool) : Nat := countLit b [43, 45, 49, 51]
def count564 (b : Nat → Bool) : Nat := countLit b [52, 54]
def count566 (b : Nat → Bool) : Nat := countLit b [57, 58]
def count568 (b : Nat → Bool) : Nat := countLit b [52, 54, 57, 58]
def count572 (b : Nat → Bool) : Nat := countLit b [43, 45, 49, 51, 52, 54, 57, 58]
def count580 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 35, 36, 41, 42, 43, 45, 49, 51, 52, 54, 57, 58]
def count595 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 9, 10, 12, 15, 17, 18, 19, 24, 25, 26, 28, 31, 32, 34, 35, 36, 41, 42, 43, 45, 49, 51, 52, 54, 57, 58]
def count625 (b : Nat → Bool) : Nat := countLit b [61, 66]
def count627 (b : Nat → Bool) : Nat := countLit b [60, 61, 66]
def count630 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count632 (b : Nat → Bool) : Nat := countLit b [71, 72]
def count634 (b : Nat → Bool) : Nat := countLit b [68, 69, 71, 72]
def count638 (b : Nat → Bool) : Nat := countLit b [60, 61, 66, 68, 69, 71, 72]
def count645 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count647 (b : Nat → Bool) : Nat := countLit b [78, 82]
def count649 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 82]
def count653 (b : Nat → Bool) : Nat := countLit b [83, 85]
def count655 (b : Nat → Bool) : Nat := countLit b [87, 89]
def count657 (b : Nat → Bool) : Nat := countLit b [83, 85, 87, 89]
def count661 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 82, 83, 85, 87, 89]
def count669 (b : Nat → Bool) : Nat := countLit b [60, 61, 66, 68, 69, 71, 72, 75, 77, 78, 82, 83, 85, 87, 89]
def count684 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count686 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count688 (b : Nat → Bool) : Nat := countLit b [92, 93, 95, 97]
def count692 (b : Nat → Bool) : Nat := countLit b [98, 101]
def count694 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count696 (b : Nat → Bool) : Nat := countLit b [98, 101, 102, 103]
def count700 (b : Nat → Bool) : Nat := countLit b [92, 93, 95, 97, 98, 101, 102, 103]
def count708 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count710 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count712 (b : Nat → Bool) : Nat := countLit b [105, 106, 109, 110]
def count716 (b : Nat → Bool) : Nat := countLit b [111, 115]
def count718 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count720 (b : Nat → Bool) : Nat := countLit b [111, 115, 118, 119]
def count724 (b : Nat → Bool) : Nat := countLit b [105, 106, 109, 110, 111, 115, 118, 119]
def count732 (b : Nat → Bool) : Nat := countLit b [92, 93, 95, 97, 98, 101, 102, 103, 105, 106, 109, 110, 111, 115, 118, 119]
def count748 (b : Nat → Bool) : Nat := countLit b [60, 61, 66, 68, 69, 71, 72, 75, 77, 78, 82, 83, 85, 87, 89, 92, 93, 95, 97, 98, 101, 102, 103, 105, 106, 109, 110, 111, 115, 118, 119]
def count779 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 9, 10, 12, 15, 17, 18, 19, 24, 25, 26, 28, 31, 32, 34, 35, 36, 41, 42, 43, 45, 49, 51, 52, 54, 57, 58, 60, 61, 66, 68, 69, 71, 72, 75, 77, 78, 82, 83, 85, 87, 89, 92, 93, 95, 97, 98, 101, 102, 103, 105, 106, 109, 110, 111, 115, 118, 119]
def count821 (b : Nat → Bool) : Nat := countLit b [-2, -5]
def count823 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5]
def count826 (b : Nat → Bool) : Nat := countLit b [-7, -9]
def count828 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count830 (b : Nat → Bool) : Nat := countLit b [-7, -9, -10, -12]
def count834 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -9, -10, -12]
def count841 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count843 (b : Nat → Bool) : Nat := countLit b [-18, -19]
def count845 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18, -19]
def count849 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count851 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count853 (b : Nat → Bool) : Nat := countLit b [-24, -25, -26, -28]
def count857 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18, -19, -24, -25, -26, -28]
def count865 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -9, -10, -12, -15, -17, -18, -19, -24, -25, -26, -28]
def count880 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count882 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34]
def count885 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count887 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count889 (b : Nat → Bool) : Nat := countLit b [-35, -36, -41, -42]
def count893 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -35, -36, -41, -42]
def count900 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count902 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count904 (b : Nat → Bool) : Nat := countLit b [-43, -45, -49, -51]
def count908 (b : Nat → Bool) : Nat := countLit b [-52, -54]
def count910 (b : Nat → Bool) : Nat := countLit b [-57, -58]
def count912 (b : Nat → Bool) : Nat := countLit b [-52, -54, -57, -58]
def count916 (b : Nat → Bool) : Nat := countLit b [-43, -45, -49, -51, -52, -54, -57, -58]
def count924 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -35, -36, -41, -42, -43, -45, -49, -51, -52, -54, -57, -58]
def count939 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -9, -10, -12, -15, -17, -18, -19, -24, -25, -26, -28, -31, -32, -34, -35, -36, -41, -42, -43, -45, -49, -51, -52, -54, -57, -58]
def count960 (b : Nat → Bool) : Nat := countLit b [-61, -66]
def count962 (b : Nat → Bool) : Nat := countLit b [-60, -61, -66]
def count965 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count967 (b : Nat → Bool) : Nat := countLit b [-71, -72]
def count969 (b : Nat → Bool) : Nat := countLit b [-68, -69, -71, -72]
def count973 (b : Nat → Bool) : Nat := countLit b [-60, -61, -66, -68, -69, -71, -72]
def count980 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count982 (b : Nat → Bool) : Nat := countLit b [-78, -82]
def count984 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -82]
def count988 (b : Nat → Bool) : Nat := countLit b [-83, -85]
def count990 (b : Nat → Bool) : Nat := countLit b [-87, -89]
def count992 (b : Nat → Bool) : Nat := countLit b [-83, -85, -87, -89]
def count996 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -82, -83, -85, -87, -89]
def count1004 (b : Nat → Bool) : Nat := countLit b [-60, -61, -66, -68, -69, -71, -72, -75, -77, -78, -82, -83, -85, -87, -89]
def count1019 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1021 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count1023 (b : Nat → Bool) : Nat := countLit b [-92, -93, -95, -97]
def count1027 (b : Nat → Bool) : Nat := countLit b [-98, -101]
def count1029 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1031 (b : Nat → Bool) : Nat := countLit b [-98, -101, -102, -103]
def count1035 (b : Nat → Bool) : Nat := countLit b [-92, -93, -95, -97, -98, -101, -102, -103]
def count1043 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count1045 (b : Nat → Bool) : Nat := countLit b [-109, -110]
def count1047 (b : Nat → Bool) : Nat := countLit b [-105, -106, -109, -110]
def count1051 (b : Nat → Bool) : Nat := countLit b [-111, -115]
def count1053 (b : Nat → Bool) : Nat := countLit b [-118, -119]
def count1055 (b : Nat → Bool) : Nat := countLit b [-111, -115, -118, -119]
def count1059 (b : Nat → Bool) : Nat := countLit b [-105, -106, -109, -110, -111, -115, -118, -119]
def count1067 (b : Nat → Bool) : Nat := countLit b [-92, -93, -95, -97, -98, -101, -102, -103, -105, -106, -109, -110, -111, -115, -118, -119]
def count1083 (b : Nat → Bool) : Nat := countLit b [-60, -61, -66, -68, -69, -71, -72, -75, -77, -78, -82, -83, -85, -87, -89, -92, -93, -95, -97, -98, -101, -102, -103, -105, -106, -109, -110, -111, -115, -118, -119]
def count1104 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -9, -10, -12, -15, -17, -18, -19, -24, -25, -26, -28, -31, -32, -34, -35, -36, -41, -42, -43, -45, -49, -51, -52, -54, -57, -58, -60, -61, -66, -68, -69, -71, -72, -75, -77, -78, -82, -83, -85, -87, -89, -92, -93, -95, -97, -98, -101, -102, -103, -105, -106, -109, -110, -111, -115, -118, -119]
def count1125 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count1127 (b : Nat → Bool) : Nat := countLit b [3, 4, 6]
def count1130 (b : Nat → Bool) : Nat := countLit b [8, 11]
def count1132 (b : Nat → Bool) : Nat := countLit b [13, 14]
def count1134 (b : Nat → Bool) : Nat := countLit b [8, 11, 13, 14]
def count1138 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 11, 13, 14]
def count1145 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count1147 (b : Nat → Bool) : Nat := countLit b [16, 20, 21]
def count1150 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count1152 (b : Nat → Bool) : Nat := countLit b [27, 29]
def count1154 (b : Nat → Bool) : Nat := countLit b [22, 23, 27, 29]
def count1158 (b : Nat → Bool) : Nat := countLit b [16, 20, 21, 22, 23, 27, 29]
def count1165 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 11, 13, 14, 16, 20, 21, 22, 23, 27, 29]
def count1179 (b : Nat → Bool) : Nat := countLit b [33, 37]
def count1181 (b : Nat → Bool) : Nat := countLit b [30, 33, 37]
def count1184 (b : Nat → Bool) : Nat := countLit b [38, 39]
def count1186 (b : Nat → Bool) : Nat := countLit b [40, 44]
def count1188 (b : Nat → Bool) : Nat := countLit b [38, 39, 40, 44]
def count1192 (b : Nat → Bool) : Nat := countLit b [30, 33, 37, 38, 39, 40, 44]
def count1199 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count1201 (b : Nat → Bool) : Nat := countLit b [48, 50]
def count1203 (b : Nat → Bool) : Nat := countLit b [46, 47, 48, 50]
def count1207 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count1209 (b : Nat → Bool) : Nat := countLit b [56, 59]
def count1211 (b : Nat → Bool) : Nat := countLit b [53, 55, 56, 59]
def count1215 (b : Nat → Bool) : Nat := countLit b [46, 47, 48, 50, 53, 55, 56, 59]
def count1223 (b : Nat → Bool) : Nat := countLit b [30, 33, 37, 38, 39, 40, 44, 46, 47, 48, 50, 53, 55, 56, 59]
def count1238 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 11, 13, 14, 16, 20, 21, 22, 23, 27, 29, 30, 33, 37, 38, 39, 40, 44, 46, 47, 48, 50, 53, 55, 56, 59]
def count1267 (b : Nat → Bool) : Nat := countLit b [63, 64]
def count1269 (b : Nat → Bool) : Nat := countLit b [62, 63, 64]
def count1272 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count1274 (b : Nat → Bool) : Nat := countLit b [70, 73]
def count1276 (b : Nat → Bool) : Nat := countLit b [65, 67, 70, 73]
def count1280 (b : Nat → Bool) : Nat := countLit b [62, 63, 64, 65, 67, 70, 73]
def count1287 (b : Nat → Bool) : Nat := countLit b [74, 76]
def count1289 (b : Nat → Bool) : Nat := countLit b [79, 80]
def count1291 (b : Nat → Bool) : Nat := countLit b [74, 76, 79, 80]
def count1295 (b : Nat → Bool) : Nat := countLit b [81, 84]
def count1297 (b : Nat → Bool) : Nat := countLit b [86, 88]
def count1299 (b : Nat → Bool) : Nat := countLit b [81, 84, 86, 88]
def count1303 (b : Nat → Bool) : Nat := countLit b [74, 76, 79, 80, 81, 84, 86, 88]
def count1311 (b : Nat → Bool) : Nat := countLit b [62, 63, 64, 65, 67, 70, 73, 74, 76, 79, 80, 81, 84, 86, 88]
def count1326 (b : Nat → Bool) : Nat := countLit b [91, 94]
def count1328 (b : Nat → Bool) : Nat := countLit b [90, 91, 94]
def count1331 (b : Nat → Bool) : Nat := countLit b [96, 99]
def count1333 (b : Nat → Bool) : Nat := countLit b [100, 104]
def count1335 (b : Nat → Bool) : Nat := countLit b [96, 99, 100, 104]
def count1339 (b : Nat → Bool) : Nat := countLit b [90, 91, 94, 96, 99, 100, 104]
def count1346 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count1348 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count1350 (b : Nat → Bool) : Nat := countLit b [107, 108, 112, 113]
def count1354 (b : Nat → Bool) : Nat := countLit b [114, 116]
def count1356 (b : Nat → Bool) : Nat := countLit b [117, 120]
def count1358 (b : Nat → Bool) : Nat := countLit b [114, 116, 117, 120]
def count1362 (b : Nat → Bool) : Nat := countLit b [107, 108, 112, 113, 114, 116, 117, 120]
def count1370 (b : Nat → Bool) : Nat := countLit b [90, 91, 94, 96, 99, 100, 104, 107, 108, 112, 113, 114, 116, 117, 120]
def count1385 (b : Nat → Bool) : Nat := countLit b [62, 63, 64, 65, 67, 70, 73, 74, 76, 79, 80, 81, 84, 86, 88, 90, 91, 94, 96, 99, 100, 104, 107, 108, 112, 113, 114, 116, 117, 120]
def count1415 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 11, 13, 14, 16, 20, 21, 22, 23, 27, 29, 30, 33, 37, 38, 39, 40, 44, 46, 47, 48, 50, 53, 55, 56, 59, 62, 63, 64, 65, 67, 70, 73, 74, 76, 79, 80, 81, 84, 86, 88, 90, 91, 94, 96, 99, 100, 104, 107, 108, 112, 113, 114, 116, 117, 120]
def count1457 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count1459 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6]
def count1462 (b : Nat → Bool) : Nat := countLit b [-8, -11]
def count1464 (b : Nat → Bool) : Nat := countLit b [-13, -14]
def count1466 (b : Nat → Bool) : Nat := countLit b [-8, -11, -13, -14]
def count1470 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -11, -13, -14]
def count1477 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count1479 (b : Nat → Bool) : Nat := countLit b [-16, -20, -21]
def count1482 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count1484 (b : Nat → Bool) : Nat := countLit b [-27, -29]
def count1486 (b : Nat → Bool) : Nat := countLit b [-22, -23, -27, -29]
def count1490 (b : Nat → Bool) : Nat := countLit b [-16, -20, -21, -22, -23, -27, -29]
def count1497 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]
def count1511 (b : Nat → Bool) : Nat := countLit b [-33, -37]
def count1513 (b : Nat → Bool) : Nat := countLit b [-30, -33, -37]
def count1516 (b : Nat → Bool) : Nat := countLit b [-38, -39]
def count1518 (b : Nat → Bool) : Nat := countLit b [-40, -44]
def count1520 (b : Nat → Bool) : Nat := countLit b [-38, -39, -40, -44]
def count1524 (b : Nat → Bool) : Nat := countLit b [-30, -33, -37, -38, -39, -40, -44]
def count1531 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count1533 (b : Nat → Bool) : Nat := countLit b [-48, -50]
def count1535 (b : Nat → Bool) : Nat := countLit b [-46, -47, -48, -50]
def count1539 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count1541 (b : Nat → Bool) : Nat := countLit b [-56, -59]
def count1543 (b : Nat → Bool) : Nat := countLit b [-53, -55, -56, -59]
def count1547 (b : Nat → Bool) : Nat := countLit b [-46, -47, -48, -50, -53, -55, -56, -59]
def count1555 (b : Nat → Bool) : Nat := countLit b [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]
def count1570 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]
def count1589 (b : Nat → Bool) : Nat := countLit b [-63, -64]
def count1591 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64]
def count1594 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count1596 (b : Nat → Bool) : Nat := countLit b [-70, -73]
def count1598 (b : Nat → Bool) : Nat := countLit b [-65, -67, -70, -73]
def count1602 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64, -65, -67, -70, -73]
def count1609 (b : Nat → Bool) : Nat := countLit b [-74, -76]
def count1611 (b : Nat → Bool) : Nat := countLit b [-79, -80]
def count1613 (b : Nat → Bool) : Nat := countLit b [-74, -76, -79, -80]
def count1617 (b : Nat → Bool) : Nat := countLit b [-81, -84]
def count1619 (b : Nat → Bool) : Nat := countLit b [-86, -88]
def count1621 (b : Nat → Bool) : Nat := countLit b [-81, -84, -86, -88]
def count1625 (b : Nat → Bool) : Nat := countLit b [-74, -76, -79, -80, -81, -84, -86, -88]
def count1633 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88]
def count1648 (b : Nat → Bool) : Nat := countLit b [-91, -94]
def count1650 (b : Nat → Bool) : Nat := countLit b [-90, -91, -94]
def count1653 (b : Nat → Bool) : Nat := countLit b [-96, -99]
def count1655 (b : Nat → Bool) : Nat := countLit b [-100, -104]
def count1657 (b : Nat → Bool) : Nat := countLit b [-96, -99, -100, -104]
def count1661 (b : Nat → Bool) : Nat := countLit b [-90, -91, -94, -96, -99, -100, -104]
def count1668 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1670 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1672 (b : Nat → Bool) : Nat := countLit b [-107, -108, -112, -113]
def count1676 (b : Nat → Bool) : Nat := countLit b [-114, -116]
def count1678 (b : Nat → Bool) : Nat := countLit b [-117, -120]
def count1680 (b : Nat → Bool) : Nat := countLit b [-114, -116, -117, -120]
def count1684 (b : Nat → Bool) : Nat := countLit b [-107, -108, -112, -113, -114, -116, -117, -120]
def count1692 (b : Nat → Bool) : Nat := countLit b [-90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]
def count1707 (b : Nat → Bool) : Nat := countLit b [-62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]
def count1726 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29, -30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59, -62, -63, -64, -65, -67, -70, -73, -74, -76, -79, -80, -81, -84, -86, -88, -90, -91, -94, -96, -99, -100, -104, -107, -108, -112, -113, -114, -116, -117, -120]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 872 then (if i < 436 then (if i < 218 then (if i < 109 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 20 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 18 then (if i < 17 then b 16 else b 17) else (if i < 19 then b 18 else b 19))) else (if i < 23 then (if i < 21 then b 20 else (if i < 22 then b 21 else b 22)) else (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else b 26))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 31 then b 30 else (if i < 32 then b 31 else b 32))) else (if i < 36 then (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)) else (if i < 38 then (if i < 37 then b 36 else b 37) else (if i < 39 then b 38 else b 39)))) else (if i < 47 then (if i < 43 then (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)) else (if i < 45 then (if i < 44 then b 43 else b 44) else (if i < 46 then b 45 else b 46))) else (if i < 50 then (if i < 48 then b 47 else (if i < 49 then b 48 else b 49)) else (if i < 52 then (if i < 51 then b 50 else b 51) else (if i < 53 then b 52 else b 53)))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)) else (if i < 58 then b 57 else (if i < 59 then b 58 else b 59))) else (if i < 63 then (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)) else (if i < 65 then (if i < 64 then b 63 else b 64) else (if i < 66 then b 65 else b 66)))) else (if i < 74 then (if i < 70 then (if i < 68 then b 67 else (if i < 69 then b 68 else b 69)) else (if i < 72 then (if i < 71 then b 70 else b 71) else (if i < 73 then b 72 else b 73))) else (if i < 77 then (if i < 75 then b 74 else (if i < 76 then b 75 else b 76)) else (if i < 79 then (if i < 78 then b 77 else b 78) else (if i < 80 then b 79 else b 80))))) else (if i < 95 then (if i < 88 then (if i < 84 then (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)) else (if i < 86 then (if i < 85 then b 84 else b 85) else (if i < 87 then b 86 else b 87))) else (if i < 91 then (if i < 89 then b 88 else (if i < 90 then b 89 else b 90)) else (if i < 93 then (if i < 92 then b 91 else b 92) else (if i < 94 then b 93 else b 94)))) else (if i < 102 then (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 100 then (if i < 99 then b 98 else b 99) else (if i < 101 then b 100 else b 101))) else (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 107 then (if i < 106 then b 105 else b 106) else (if i < 108 then b 107 else b 108))))))) else (if i < 163 then (if i < 136 then (if i < 122 then (if i < 115 then (if i < 112 then (if i < 110 then b 109 else (if i < 111 then b 110 else b 111)) else (if i < 113 then b 112 else (if i < 114 then b 113 else b 114))) else (if i < 118 then (if i < 116 then b 115 else (if i < 117 then b 116 else b 117)) else (if i < 120 then (if i < 119 then b 118 else b 119) else (if i < 121 then b 120 else b 121)))) else (if i < 129 then (if i < 125 then (if i < 123 then b 122 else (if i < 124 then b 123 else b 124)) else (if i < 127 then (if i < 126 then b 125 else b 126) else (if i < 128 then b 127 else b 128))) else (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 134 then (if i < 133 then b 132 else b 133) else (if i < 135 then b 134 else b 135))))) else (if i < 149 then (if i < 142 then (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 140 then b 139 else (if i < 141 then b 140 else b 141))) else (if i < 145 then (if i < 143 then b 142 else (if i < 144 then b 143 else b 144)) else (if i < 147 then (if i < 146 then b 145 else b 146) else (if i < 148 then b 147 else b 148)))) else (if i < 156 then (if i < 152 then (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)) else (if i < 154 then (if i < 153 then b 152 else b 153) else (if i < 155 then b 154 else b 155))) else (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 161 then (if i < 160 then b 159 else b 160) else (if i < 162 then b 161 else b 162)))))) else (if i < 190 then (if i < 176 then (if i < 169 then (if i < 166 then (if i < 164 then b 163 else (if i < 165 then b 164 else b 165)) else (if i < 167 then b 166 else (if i < 168 then b 167 else b 168))) else (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 174 then (if i < 173 then b 172 else b 173) else (if i < 175 then b 174 else b 175)))) else (if i < 183 then (if i < 179 then (if i < 177 then b 176 else (if i < 178 then b 177 else b 178)) else (if i < 181 then (if i < 180 then b 179 else b 180) else (if i < 182 then b 181 else b 182))) else (if i < 186 then (if i < 184 then b 183 else (if i < 185 then b 184 else b 185)) else (if i < 188 then (if i < 187 then b 186 else b 187) else (if i < 189 then b 188 else b 189))))) else (if i < 204 then (if i < 197 then (if i < 193 then (if i < 191 then b 190 else (if i < 192 then b 191 else b 192)) else (if i < 195 then (if i < 194 then b 193 else b 194) else (if i < 196 then b 195 else b 196))) else (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 202 then (if i < 201 then b 200 else b 201) else (if i < 203 then b 202 else b 203)))) else (if i < 211 then (if i < 207 then (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)) else (if i < 209 then (if i < 208 then b 207 else b 208) else (if i < 210 then b 209 else b 210))) else (if i < 214 then (if i < 212 then b 211 else (if i < 213 then b 212 else b 213)) else (if i < 216 then (if i < 215 then b 214 else b 215) else (if i < 217 then b 216 else b 217)))))))) else (if i < 327 then (if i < 272 then (if i < 245 then (if i < 231 then (if i < 224 then (if i < 221 then (if i < 219 then b 218 else (if i < 220 then b 219 else b 220)) else (if i < 222 then b 221 else (if i < 223 then b 222 else b 223))) else (if i < 227 then (if i < 225 then b 224 else (if i < 226 then b 225 else b 226)) else (if i < 229 then (if i < 228 then b 227 else b 228) else (if i < 230 then b 229 else b 230)))) else (if i < 238 then (if i < 234 then (if i < 232 then b 231 else (if i < 233 then b 232 else b 233)) else (if i < 236 then (if i < 235 then b 234 else b 235) else (if i < 237 then b 236 else b 237))) else (if i < 241 then (if i < 239 then b 238 else (if i < 240 then b 239 else b 240)) else (if i < 243 then (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b)) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b)))))) else (if i < 258 then (if i < 251 then (if i < 248 then (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))) else (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b)))) else (if i < 254 then (if i < 252 then decide (1 ≤ count251 b) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b))) else (if i < 256 then (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b)) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))))) else (if i < 265 then (if i < 261 then (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 263 then (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b)) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))) else (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 270 then (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))))))) else (if i < 299 then (if i < 285 then (if i < 278 then (if i < 275 then (if i < 273 then decide (2 ≤ count271 b) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b))) else (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)))) else (if i < 281 then (if i < 279 then decide (2 ≤ count277 b) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b))) else (if i < 283 then (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))))) else (if i < 292 then (if i < 288 then (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))) else (if i < 290 then (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)))) else (if i < 295 then (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))) else (if i < 297 then (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b)) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))))) else (if i < 313 then (if i < 306 then (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))) else (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))))) else (if i < 320 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))) else (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 325 then (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b)) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)))))))) else (if i < 381 then (if i < 354 then (if i < 340 then (if i < 333 then (if i < 330 then (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b))) else (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)))) else (if i < 336 then (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 338 then (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))))) else (if i < 347 then (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))) else (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))))) else (if i < 367 then (if i < 360 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b)))) else (if i < 363 then (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))) else (if i < 365 then (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b)) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))))) else (if i < 374 then (if i < 370 then (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))) else (if i < 372 then (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)))) else (if i < 377 then (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b))) else (if i < 379 then (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))))))) else (if i < 408 then (if i < 394 then (if i < 387 then (if i < 384 then (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b))) else (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)))) else (if i < 390 then (if i < 388 then decide (1 ≤ count387 b) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b))) else (if i < 392 then (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b)) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))))) else (if i < 401 then (if i < 397 then (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))) else (if i < 399 then (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b)) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)))) else (if i < 404 then (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 406 then (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b)) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b)))))) else (if i < 422 then (if i < 415 then (if i < 411 then (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))) else (if i < 413 then (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 420 then (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))))) else (if i < 429 then (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 427 then (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)))) else (if i < 432 then (if i < 430 then decide (1 ≤ count429 b) else (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b))) else (if i < 434 then (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b)) else (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b)))))))))) else (if i < 654 then (if i < 545 then (if i < 490 then (if i < 463 then (if i < 449 then (if i < 442 then (if i < 439 then (if i < 437 then decide (2 ≤ count435 b) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b))) else (if i < 440 then decide (1 ≤ count439 b) else (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)))) else (if i < 445 then (if i < 443 then decide (2 ≤ count441 b) else (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b))) else (if i < 447 then (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b)) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b))))) else (if i < 456 then (if i < 452 then (if i < 450 then decide (1 ≤ count449 b) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b))) else (if i < 454 then (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b)) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b)))) else (if i < 459 then (if i < 457 then decide (2 ≤ count455 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b))) else (if i < 461 then (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)))))) else (if i < 476 then (if i < 469 then (if i < 466 then (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b))) else (if i < 467 then decide (2 ≤ count465 b) else (if i < 468 then decide (1 ≤ count467 b) else decide (2 ≤ count467 b)))) else (if i < 472 then (if i < 470 then decide (1 ≤ count469 b) else (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b))) else (if i < 474 then (if i < 473 then decide (2 ≤ count471 b) else decide (1 ≤ count473 b)) else (if i < 475 then decide (2 ≤ count473 b) else decide (1 ≤ count475 b))))) else (if i < 483 then (if i < 479 then (if i < 477 then decide (2 ≤ count475 b) else (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b))) else (if i < 481 then (if i < 480 then decide (1 ≤ count479 b) else decide (2 ≤ count479 b)) else (if i < 482 then decide (3 ≤ count479 b) else decide (1 ≤ count482 b)))) else (if i < 486 then (if i < 484 then decide (2 ≤ count482 b) else (if i < 485 then decide (1 ≤ count484 b) else decide (2 ≤ count484 b))) else (if i < 488 then (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b)) else (if i < 489 then decide (3 ≤ count486 b) else decide (4 ≤ count486 b))))))) else (if i < 517 then (if i < 503 then (if i < 496 then (if i < 493 then (if i < 491 then decide (1 ≤ count490 b) else (if i < 492 then decide (2 ≤ count490 b) else decide (3 ≤ count490 b))) else (if i < 494 then decide (4 ≤ count490 b) else (if i < 495 then decide (5 ≤ count490 b) else decide (6 ≤ count490 b)))) else (if i < 499 then (if i < 497 then decide (7 ≤ count490 b) else (if i < 498 then decide (1 ≤ count497 b) else decide (2 ≤ count497 b))) else (if i < 501 then (if i < 500 then decide (1 ≤ count499 b) else decide (2 ≤ count499 b)) else (if i < 502 then decide (1 ≤ count501 b) else decide (2 ≤ count501 b))))) else (if i < 510 then (if i < 506 then (if i < 504 then decide (3 ≤ count501 b) else (if i < 505 then decide (4 ≤ count501 b) else decide (1 ≤ count505 b))) else (if i < 508 then (if i < 507 then decide (2 ≤ count505 b) else decide (1 ≤ count507 b)) else (if i < 509 then decide (2 ≤ count507 b) else decide (1 ≤ count509 b)))) else (if i < 513 then (if i < 511 then decide (2 ≤ count509 b) else (if i < 512 then decide (3 ≤ count509 b) else decide (4 ≤ count509 b))) else (if i < 515 then (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b)) else (if i < 516 then decide (3 ≤ count513 b) else decide (4 ≤ count513 b)))))) else (if i < 531 then (if i < 524 then (if i < 520 then (if i < 518 then decide (5 ≤ count513 b) else (if i < 519 then decide (6 ≤ count513 b) else decide (7 ≤ count513 b))) else (if i < 522 then (if i < 521 then decide (8 ≤ count513 b) else decide (1 ≤ count521 b)) else (if i < 523 then decide (2 ≤ count521 b) else decide (3 ≤ count521 b)))) else (if i < 527 then (if i < 525 then decide (4 ≤ count521 b) else (if i < 526 then decide (5 ≤ count521 b) else decide (6 ≤ count521 b))) else (if i < 529 then (if i < 528 then decide (7 ≤ count521 b) else decide (8 ≤ count521 b)) else (if i < 530 then decide (9 ≤ count521 b) else decide (10 ≤ count521 b))))) else (if i < 538 then (if i < 534 then (if i < 532 then decide (11 ≤ count521 b) else (if i < 533 then decide (12 ≤ count521 b) else decide (13 ≤ count521 b))) else (if i < 536 then (if i < 535 then decide (14 ≤ count521 b) else decide (15 ≤ count521 b)) else (if i < 537 then decide (1 ≤ count536 b) else decide (2 ≤ count536 b)))) else (if i < 541 then (if i < 539 then decide (1 ≤ count538 b) else (if i < 540 then decide (2 ≤ count538 b) else decide (3 ≤ count538 b))) else (if i < 543 then (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b)) else (if i < 544 then decide (1 ≤ count543 b) else decide (2 ≤ count543 b)))))))) else (if i < 599 then (if i < 572 then (if i < 558 then (if i < 551 then (if i < 548 then (if i < 546 then decide (1 ≤ count545 b) else (if i < 547 then decide (2 ≤ count545 b) else decide (3 ≤ count545 b))) else (if i < 549 then decide (4 ≤ count545 b) else (if i < 550 then decide (1 ≤ count549 b) else decide (2 ≤ count549 b)))) else (if i < 554 then (if i < 552 then decide (3 ≤ count549 b) else (if i < 553 then decide (4 ≤ count549 b) else decide (5 ≤ count549 b))) else (if i < 556 then (if i < 555 then decide (6 ≤ count549 b) else decide (7 ≤ count549 b)) else (if i < 557 then decide (1 ≤ count556 b) else decide (2 ≤ count556 b))))) else (if i < 565 then (if i < 561 then (if i < 559 then decide (1 ≤ count558 b) else (if i < 560 then decide (2 ≤ count558 b) else decide (1 ≤ count560 b))) else (if i < 563 then (if i < 562 then decide (2 ≤ count560 b) else decide (3 ≤ count560 b)) else (if i < 564 then decide (4 ≤ count560 b) else decide (1 ≤ count564 b)))) else (if i < 568 then (if i < 566 then decide (2 ≤ count564 b) else (if i < 567 then decide (1 ≤ count566 b) else decide (2 ≤ count566 b))) else (if i < 570 then (if i < 569 then decide (1 ≤ count568 b) else decide (2 ≤ count568 b)) else (if i < 571 then decide (3 ≤ count568 b) else decide (4 ≤ count568 b)))))) else (if i < 585 then (if i < 578 then (if i < 575 then (if i < 573 then decide (1 ≤ count572 b) else (if i < 574 then decide (2 ≤ count572 b) else decide (3 ≤ count572 b))) else (if i < 576 then decide (4 ≤ count572 b) else (if i < 577 then decide (5 ≤ count572 b) else decide (6 ≤ count572 b)))) else (if i < 581 then (if i < 579 then decide (7 ≤ count572 b) else (if i < 580 then decide (8 ≤ count572 b) else decide (1 ≤ count580 b))) else (if i < 583 then (if i < 582 then decide (2 ≤ count580 b) else decide (3 ≤ count580 b)) else (if i < 584 then decide (4 ≤ count580 b) else decide (5 ≤ count580 b))))) else (if i < 592 then (if i < 588 then (if i < 586 then decide (6 ≤ count580 b) else (if i < 587 then decide (7 ≤ count580 b) else decide (8 ≤ count580 b))) else (if i < 590 then (if i < 589 then decide (9 ≤ count580 b) else decide (10 ≤ count580 b)) else (if i < 591 then decide (11 ≤ count580 b) else decide (12 ≤ count580 b)))) else (if i < 595 then (if i < 593 then decide (13 ≤ count580 b) else (if i < 594 then decide (14 ≤ count580 b) else decide (15 ≤ count580 b))) else (if i < 597 then (if i < 596 then decide (1 ≤ count595 b) else decide (2 ≤ count595 b)) else (if i < 598 then decide (3 ≤ count595 b) else decide (4 ≤ count595 b))))))) else (if i < 626 then (if i < 612 then (if i < 605 then (if i < 602 then (if i < 600 then decide (5 ≤ count595 b) else (if i < 601 then decide (6 ≤ count595 b) else decide (7 ≤ count595 b))) else (if i < 603 then decide (8 ≤ count595 b) else (if i < 604 then decide (9 ≤ count595 b) else decide (10 ≤ count595 b)))) else (if i < 608 then (if i < 606 then decide (11 ≤ count595 b) else (if i < 607 then decide (12 ≤ count595 b) else decide (13 ≤ count595 b))) else (if i < 610 then (if i < 609 then decide (14 ≤ count595 b) else decide (15 ≤ count595 b)) else (if i < 611 then decide (16 ≤ count595 b) else decide (17 ≤ count595 b))))) else (if i < 619 then (if i < 615 then (if i < 613 then decide (18 ≤ count595 b) else (if i < 614 then decide (19 ≤ count595 b) else decide (20 ≤ count595 b))) else (if i < 617 then (if i < 616 then decide (21 ≤ count595 b) else decide (22 ≤ count595 b)) else (if i < 618 then decide (23 ≤ count595 b) else decide (24 ≤ count595 b)))) else (if i < 622 then (if i < 620 then decide (25 ≤ count595 b) else (if i < 621 then decide (26 ≤ count595 b) else decide (27 ≤ count595 b))) else (if i < 624 then (if i < 623 then decide (28 ≤ count595 b) else decide (29 ≤ count595 b)) else (if i < 625 then decide (30 ≤ count595 b) else decide (1 ≤ count625 b)))))) else (if i < 640 then (if i < 633 then (if i < 629 then (if i < 627 then decide (2 ≤ count625 b) else (if i < 628 then decide (1 ≤ count627 b) else decide (2 ≤ count627 b))) else (if i < 631 then (if i < 630 then decide (3 ≤ count627 b) else decide (1 ≤ count630 b)) else (if i < 632 then decide (2 ≤ count630 b) else decide (1 ≤ count632 b)))) else (if i < 636 then (if i < 634 then decide (2 ≤ count632 b) else (if i < 635 then decide (1 ≤ count634 b) else decide (2 ≤ count634 b))) else (if i < 638 then (if i < 637 then decide (3 ≤ count634 b) else decide (4 ≤ count634 b)) else (if i < 639 then decide (1 ≤ count638 b) else decide (2 ≤ count638 b))))) else (if i < 647 then (if i < 643 then (if i < 641 then decide (3 ≤ count638 b) else (if i < 642 then decide (4 ≤ count638 b) else decide (5 ≤ count638 b))) else (if i < 645 then (if i < 644 then decide (6 ≤ count638 b) else decide (7 ≤ count638 b)) else (if i < 646 then decide (1 ≤ count645 b) else decide (2 ≤ count645 b)))) else (if i < 650 then (if i < 648 then decide (1 ≤ count647 b) else (if i < 649 then decide (2 ≤ count647 b) else decide (1 ≤ count649 b))) else (if i < 652 then (if i < 651 then decide (2 ≤ count649 b) else decide (3 ≤ count649 b)) else (if i < 653 then decide (4 ≤ count649 b) else decide (1 ≤ count653 b))))))))) else (if i < 763 then (if i < 708 then (if i < 681 then (if i < 667 then (if i < 660 then (if i < 657 then (if i < 655 then decide (2 ≤ count653 b) else (if i < 656 then decide (1 ≤ count655 b) else decide (2 ≤ count655 b))) else (if i < 658 then decide (1 ≤ count657 b) else (if i < 659 then decide (2 ≤ count657 b) else decide (3 ≤ count657 b)))) else (if i < 663 then (if i < 661 then decide (4 ≤ count657 b) else (if i < 662 then decide (1 ≤ count661 b) else decide (2 ≤ count661 b))) else (if i < 665 then (if i < 664 then decide (3 ≤ count661 b) else decide (4 ≤ count661 b)) else (if i < 666 then decide (5 ≤ count661 b) else decide (6 ≤ count661 b))))) else (if i < 674 then (if i < 670 then (if i < 668 then decide (7 ≤ count661 b) else (if i < 669 then decide (8 ≤ count661 b) else decide (1 ≤ count669 b))) else (if i < 672 then (if i < 671 then decide (2 ≤ count669 b) else decide (3 ≤ count669 b)) else (if i < 673 then decide (4 ≤ count669 b) else decide (5 ≤ count669 b)))) else (if i < 677 then (if i < 675 then decide (6 ≤ count669 b) else (if i < 676 then decide (7 ≤ count669 b) else decide (8 ≤ count669 b))) else (if i < 679 then (if i < 678 then decide (9 ≤ count669 b) else decide (10 ≤ count669 b)) else (if i < 680 then decide (11 ≤ count669 b) else decide (12 ≤ count669 b)))))) else (if i < 694 then (if i < 687 then (if i < 684 then (if i < 682 then decide (13 ≤ count669 b) else (if i < 683 then decide (14 ≤ count669 b) else decide (15 ≤ count669 b))) else (if i < 685 then decide (1 ≤ count684 b) else (if i < 686 then decide (2 ≤ count684 b) else decide (1 ≤ count686 b)))) else (if i < 690 then (if i < 688 then decide (2 ≤ count686 b) else (if i < 689 then decide (1 ≤ count688 b) else decide (2 ≤ count688 b))) else (if i < 692 then (if i < 691 then decide (3 ≤ count688 b) else decide (4 ≤ count688 b)) else (if i < 693 then decide (1 ≤ count692 b) else decide (2 ≤ count692 b))))) else (if i < 701 then (if i < 697 then (if i < 695 then decide (1 ≤ count694 b) else (if i < 696 then decide (2 ≤ count694 b) else decide (1 ≤ count696 b))) else (if i < 699 then (if i < 698 then decide (2 ≤ count696 b) else decide (3 ≤ count696 b)) else (if i < 700 then decide (4 ≤ count696 b) else decide (1 ≤ count700 b)))) else (if i < 704 then (if i < 702 then decide (2 ≤ count700 b) else (if i < 703 then decide (3 ≤ count700 b) else decide (4 ≤ count700 b))) else (if i < 706 then (if i < 705 then decide (5 ≤ count700 b) else decide (6 ≤ count700 b)) else (if i < 707 then decide (7 ≤ count700 b) else decide (8 ≤ count700 b))))))) else (if i < 735 then (if i < 721 then (if i < 714 then (if i < 711 then (if i < 709 then decide (1 ≤ count708 b) else (if i < 710 then decide (2 ≤ count708 b) else decide (1 ≤ count710 b))) else (if i < 712 then decide (2 ≤ count710 b) else (if i < 713 then decide (1 ≤ count712 b) else decide (2 ≤ count712 b)))) else (if i < 717 then (if i < 715 then decide (3 ≤ count712 b) else (if i < 716 then decide (4 ≤ count712 b) else decide (1 ≤ count716 b))) else (if i < 719 then (if i < 718 then decide (2 ≤ count716 b) else decide (1 ≤ count718 b)) else (if i < 720 then decide (2 ≤ count718 b) else decide (1 ≤ count720 b))))) else (if i < 728 then (if i < 724 then (if i < 722 then decide (2 ≤ count720 b) else (if i < 723 then decide (3 ≤ count720 b) else decide (4 ≤ count720 b))) else (if i < 726 then (if i < 725 then decide (1 ≤ count724 b) else decide (2 ≤ count724 b)) else (if i < 727 then decide (3 ≤ count724 b) else decide (4 ≤ count724 b)))) else (if i < 731 then (if i < 729 then decide (5 ≤ count724 b) else (if i < 730 then decide (6 ≤ count724 b) else decide (7 ≤ count724 b))) else (if i < 733 then (if i < 732 then decide (8 ≤ count724 b) else decide (1 ≤ count732 b)) else (if i < 734 then decide (2 ≤ count732 b) else decide (3 ≤ count732 b)))))) else (if i < 749 then (if i < 742 then (if i < 738 then (if i < 736 then decide (4 ≤ count732 b) else (if i < 737 then decide (5 ≤ count732 b) else decide (6 ≤ count732 b))) else (if i < 740 then (if i < 739 then decide (7 ≤ count732 b) else decide (8 ≤ count732 b)) else (if i < 741 then decide (9 ≤ count732 b) else decide (10 ≤ count732 b)))) else (if i < 745 then (if i < 743 then decide (11 ≤ count732 b) else (if i < 744 then decide (12 ≤ count732 b) else decide (13 ≤ count732 b))) else (if i < 747 then (if i < 746 then decide (14 ≤ count732 b) else decide (15 ≤ count732 b)) else (if i < 748 then decide (16 ≤ count732 b) else decide (1 ≤ count748 b))))) else (if i < 756 then (if i < 752 then (if i < 750 then decide (2 ≤ count748 b) else (if i < 751 then decide (3 ≤ count748 b) else decide (4 ≤ count748 b))) else (if i < 754 then (if i < 753 then decide (5 ≤ count748 b) else decide (6 ≤ count748 b)) else (if i < 755 then decide (7 ≤ count748 b) else decide (8 ≤ count748 b)))) else (if i < 759 then (if i < 757 then decide (9 ≤ count748 b) else (if i < 758 then decide (10 ≤ count748 b) else decide (11 ≤ count748 b))) else (if i < 761 then (if i < 760 then decide (12 ≤ count748 b) else decide (13 ≤ count748 b)) else (if i < 762 then decide (14 ≤ count748 b) else decide (15 ≤ count748 b)))))))) else (if i < 817 then (if i < 790 then (if i < 776 then (if i < 769 then (if i < 766 then (if i < 764 then decide (16 ≤ count748 b) else (if i < 765 then decide (17 ≤ count748 b) else decide (18 ≤ count748 b))) else (if i < 767 then decide (19 ≤ count748 b) else (if i < 768 then decide (20 ≤ count748 b) else decide (21 ≤ count748 b)))) else (if i < 772 then (if i < 770 then decide (22 ≤ count748 b) else (if i < 771 then decide (23 ≤ count748 b) else decide (24 ≤ count748 b))) else (if i < 774 then (if i < 773 then decide (25 ≤ count748 b) else decide (26 ≤ count748 b)) else (if i < 775 then decide (27 ≤ count748 b) else decide (28 ≤ count748 b))))) else (if i < 783 then (if i < 779 then (if i < 777 then decide (29 ≤ count748 b) else (if i < 778 then decide (30 ≤ count748 b) else decide (31 ≤ count748 b))) else (if i < 781 then (if i < 780 then decide (1 ≤ count779 b) else decide (2 ≤ count779 b)) else (if i < 782 then decide (3 ≤ count779 b) else decide (4 ≤ count779 b)))) else (if i < 786 then (if i < 784 then decide (5 ≤ count779 b) else (if i < 785 then decide (6 ≤ count779 b) else decide (7 ≤ count779 b))) else (if i < 788 then (if i < 787 then decide (8 ≤ count779 b) else decide (9 ≤ count779 b)) else (if i < 789 then decide (10 ≤ count779 b) else decide (11 ≤ count779 b)))))) else (if i < 803 then (if i < 796 then (if i < 793 then (if i < 791 then decide (12 ≤ count779 b) else (if i < 792 then decide (13 ≤ count779 b) else decide (14 ≤ count779 b))) else (if i < 794 then decide (15 ≤ count779 b) else (if i < 795 then decide (16 ≤ count779 b) else decide (17 ≤ count779 b)))) else (if i < 799 then (if i < 797 then decide (18 ≤ count779 b) else (if i < 798 then decide (19 ≤ count779 b) else decide (20 ≤ count779 b))) else (if i < 801 then (if i < 800 then decide (21 ≤ count779 b) else decide (22 ≤ count779 b)) else (if i < 802 then decide (23 ≤ count779 b) else decide (24 ≤ count779 b))))) else (if i < 810 then (if i < 806 then (if i < 804 then decide (25 ≤ count779 b) else (if i < 805 then decide (26 ≤ count779 b) else decide (27 ≤ count779 b))) else (if i < 808 then (if i < 807 then decide (28 ≤ count779 b) else decide (29 ≤ count779 b)) else (if i < 809 then decide (30 ≤ count779 b) else decide (31 ≤ count779 b)))) else (if i < 813 then (if i < 811 then decide (32 ≤ count779 b) else (if i < 812 then decide (33 ≤ count779 b) else decide (34 ≤ count779 b))) else (if i < 815 then (if i < 814 then decide (35 ≤ count779 b) else decide (36 ≤ count779 b)) else (if i < 816 then decide (37 ≤ count779 b) else decide (38 ≤ count779 b))))))) else (if i < 844 then (if i < 830 then (if i < 823 then (if i < 820 then (if i < 818 then decide (39 ≤ count779 b) else (if i < 819 then decide (40 ≤ count779 b) else decide (41 ≤ count779 b))) else (if i < 821 then decide (42 ≤ count779 b) else (if i < 822 then decide (1 ≤ count821 b) else decide (2 ≤ count821 b)))) else (if i < 826 then (if i < 824 then decide (1 ≤ count823 b) else (if i < 825 then decide (2 ≤ count823 b) else decide (3 ≤ count823 b))) else (if i < 828 then (if i < 827 then decide (1 ≤ count826 b) else decide (2 ≤ count826 b)) else (if i < 829 then decide (1 ≤ count828 b) else decide (2 ≤ count828 b))))) else (if i < 837 then (if i < 833 then (if i < 831 then decide (1 ≤ count830 b) else (if i < 832 then decide (2 ≤ count830 b) else decide (3 ≤ count830 b))) else (if i < 835 then (if i < 834 then decide (4 ≤ count830 b) else decide (1 ≤ count834 b)) else (if i < 836 then decide (2 ≤ count834 b) else decide (3 ≤ count834 b)))) else (if i < 840 then (if i < 838 then decide (4 ≤ count834 b) else (if i < 839 then decide (5 ≤ count834 b) else decide (6 ≤ count834 b))) else (if i < 842 then (if i < 841 then decide (7 ≤ count834 b) else decide (1 ≤ count841 b)) else (if i < 843 then decide (2 ≤ count841 b) else decide (1 ≤ count843 b)))))) else (if i < 858 then (if i < 851 then (if i < 847 then (if i < 845 then decide (2 ≤ count843 b) else (if i < 846 then decide (1 ≤ count845 b) else decide (2 ≤ count845 b))) else (if i < 849 then (if i < 848 then decide (3 ≤ count845 b) else decide (4 ≤ count845 b)) else (if i < 850 then decide (1 ≤ count849 b) else decide (2 ≤ count849 b)))) else (if i < 854 then (if i < 852 then decide (1 ≤ count851 b) else (if i < 853 then decide (2 ≤ count851 b) else decide (1 ≤ count853 b))) else (if i < 856 then (if i < 855 then decide (2 ≤ count853 b) else decide (3 ≤ count853 b)) else (if i < 857 then decide (4 ≤ count853 b) else decide (1 ≤ count857 b))))) else (if i < 865 then (if i < 861 then (if i < 859 then decide (2 ≤ count857 b) else (if i < 860 then decide (3 ≤ count857 b) else decide (4 ≤ count857 b))) else (if i < 863 then (if i < 862 then decide (5 ≤ count857 b) else decide (6 ≤ count857 b)) else (if i < 864 then decide (7 ≤ count857 b) else decide (8 ≤ count857 b)))) else (if i < 868 then (if i < 866 then decide (1 ≤ count865 b) else (if i < 867 then decide (2 ≤ count865 b) else decide (3 ≤ count865 b))) else (if i < 870 then (if i < 869 then decide (4 ≤ count865 b) else decide (5 ≤ count865 b)) else (if i < 871 then decide (6 ≤ count865 b) else decide (7 ≤ count865 b))))))))))) else (if i < 1308 then (if i < 1090 then (if i < 981 then (if i < 926 then (if i < 899 then (if i < 885 then (if i < 878 then (if i < 875 then (if i < 873 then decide (8 ≤ count865 b) else (if i < 874 then decide (9 ≤ count865 b) else decide (10 ≤ count865 b))) else (if i < 876 then decide (11 ≤ count865 b) else (if i < 877 then decide (12 ≤ count865 b) else decide (13 ≤ count865 b)))) else (if i < 881 then (if i < 879 then decide (14 ≤ count865 b) else (if i < 880 then decide (15 ≤ count865 b) else decide (1 ≤ count880 b))) else (if i < 883 then (if i < 882 then decide (2 ≤ count880 b) else decide (1 ≤ count882 b)) else (if i < 884 then decide (2 ≤ count882 b) else decide (3 ≤ count882 b))))) else (if i < 892 then (if i < 888 then (if i < 886 then decide (1 ≤ count885 b) else (if i < 887 then decide (2 ≤ count885 b) else decide (1 ≤ count887 b))) else (if i < 890 then (if i < 889 then decide (2 ≤ count887 b) else decide (1 ≤ count889 b)) else (if i < 891 then decide (2 ≤ count889 b) else decide (3 ≤ count889 b)))) else (if i < 895 then (if i < 893 then decide (4 ≤ count889 b) else (if i < 894 then decide (1 ≤ count893 b) else decide (2 ≤ count893 b))) else (if i < 897 then (if i < 896 then decide (3 ≤ count893 b) else decide (4 ≤ count893 b)) else (if i < 898 then decide (5 ≤ count893 b) else decide (6 ≤ count893 b)))))) else (if i < 912 then (if i < 905 then (if i < 902 then (if i < 900 then decide (7 ≤ count893 b) else (if i < 901 then decide (1 ≤ count900 b) else decide (2 ≤ count900 b))) else (if i < 903 then decide (1 ≤ count902 b) else (if i < 904 then decide (2 ≤ count902 b) else decide (1 ≤ count904 b)))) else (if i < 908 then (if i < 906 then decide (2 ≤ count904 b) else (if i < 907 then decide (3 ≤ count904 b) else decide (4 ≤ count904 b))) else (if i < 910 then (if i < 909 then decide (1 ≤ count908 b) else decide (2 ≤ count908 b)) else (if i < 911 then decide (1 ≤ count910 b) else decide (2 ≤ count910 b))))) else (if i < 919 then (if i < 915 then (if i < 913 then decide (1 ≤ count912 b) else (if i < 914 then decide (2 ≤ count912 b) else decide (3 ≤ count912 b))) else (if i < 917 then (if i < 916 then decide (4 ≤ count912 b) else decide (1 ≤ count916 b)) else (if i < 918 then decide (2 ≤ count916 b) else decide (3 ≤ count916 b)))) else (if i < 922 then (if i < 920 then decide (4 ≤ count916 b) else (if i < 921 then decide (5 ≤ count916 b) else decide (6 ≤ count916 b))) else (if i < 924 then (if i < 923 then decide (7 ≤ count916 b) else decide (8 ≤ count916 b)) else (if i < 925 then decide (1 ≤ count924 b) else decide (2 ≤ count924 b))))))) else (if i < 953 then (if i < 939 then (if i < 932 then (if i < 929 then (if i < 927 then decide (3 ≤ count924 b) else (if i < 928 then decide (4 ≤ count924 b) else decide (5 ≤ count924 b))) else (if i < 930 then decide (6 ≤ count924 b) else (if i < 931 then decide (7 ≤ count924 b) else decide (8 ≤ count924 b)))) else (if i < 935 then (if i < 933 then decide (9 ≤ count924 b) else (if i < 934 then decide (10 ≤ count924 b) else decide (11 ≤ count924 b))) else (if i < 937 then (if i < 936 then decide (12 ≤ count924 b) else decide (13 ≤ count924 b)) else (if i < 938 then decide (14 ≤ count924 b) else decide (15 ≤ count924 b))))) else (if i < 946 then (if i < 942 then (if i < 940 then decide (1 ≤ count939 b) else (if i < 941 then decide (2 ≤ count939 b) else decide (3 ≤ count939 b))) else (if i < 944 then (if i < 943 then decide (4 ≤ count939 b) else decide (5 ≤ count939 b)) else (if i < 945 then decide (6 ≤ count939 b) else decide (7 ≤ count939 b)))) else (if i < 949 then (if i < 947 then decide (8 ≤ count939 b) else (if i < 948 then decide (9 ≤ count939 b) else decide (10 ≤ count939 b))) else (if i < 951 then (if i < 950 then decide (11 ≤ count939 b) else decide (12 ≤ count939 b)) else (if i < 952 then decide (13 ≤ count939 b) else decide (14 ≤ count939 b)))))) else (if i < 967 then (if i < 960 then (if i < 956 then (if i < 954 then decide (15 ≤ count939 b) else (if i < 955 then decide (16 ≤ count939 b) else decide (17 ≤ count939 b))) else (if i < 958 then (if i < 957 then decide (18 ≤ count939 b) else decide (19 ≤ count939 b)) else (if i < 959 then decide (20 ≤ count939 b) else decide (21 ≤ count939 b)))) else (if i < 963 then (if i < 961 then decide (1 ≤ count960 b) else (if i < 962 then decide (2 ≤ count960 b) else decide (1 ≤ count962 b))) else (if i < 965 then (if i < 964 then decide (2 ≤ count962 b) else decide (3 ≤ count962 b)) else (if i < 966 then decide (1 ≤ count965 b) else decide (2 ≤ count965 b))))) else (if i < 974 then (if i < 970 then (if i < 968 then decide (1 ≤ count967 b) else (if i < 969 then decide (2 ≤ count967 b) else decide (1 ≤ count969 b))) else (if i < 972 then (if i < 971 then decide (2 ≤ count969 b) else decide (3 ≤ count969 b)) else (if i < 973 then decide (4 ≤ count969 b) else decide (1 ≤ count973 b)))) else (if i < 977 then (if i < 975 then decide (2 ≤ count973 b) else (if i < 976 then decide (3 ≤ count973 b) else decide (4 ≤ count973 b))) else (if i < 979 then (if i < 978 then decide (5 ≤ count973 b) else decide (6 ≤ count973 b)) else (if i < 980 then decide (7 ≤ count973 b) else decide (1 ≤ count980 b)))))))) else (if i < 1035 then (if i < 1008 then (if i < 994 then (if i < 987 then (if i < 984 then (if i < 982 then decide (2 ≤ count980 b) else (if i < 983 then decide (1 ≤ count982 b) else decide (2 ≤ count982 b))) else (if i < 985 then decide (1 ≤ count984 b) else (if i < 986 then decide (2 ≤ count984 b) else decide (3 ≤ count984 b)))) else (if i < 990 then (if i < 988 then decide (4 ≤ count984 b) else (if i < 989 then decide (1 ≤ count988 b) else decide (2 ≤ count988 b))) else (if i < 992 then (if i < 991 then decide (1 ≤ count990 b) else decide (2 ≤ count990 b)) else (if i < 993 then decide (1 ≤ count992 b) else decide (2 ≤ count992 b))))) else (if i < 1001 then (if i < 997 then (if i < 995 then decide (3 ≤ count992 b) else (if i < 996 then decide (4 ≤ count992 b) else decide (1 ≤ count996 b))) else (if i < 999 then (if i < 998 then decide (2 ≤ count996 b) else decide (3 ≤ count996 b)) else (if i < 1000 then decide (4 ≤ count996 b) else decide (5 ≤ count996 b)))) else (if i < 1004 then (if i < 1002 then decide (6 ≤ count996 b) else (if i < 1003 then decide (7 ≤ count996 b) else decide (8 ≤ count996 b))) else (if i < 1006 then (if i < 1005 then decide (1 ≤ count1004 b) else decide (2 ≤ count1004 b)) else (if i < 1007 then decide (3 ≤ count1004 b) else decide (4 ≤ count1004 b)))))) else (if i < 1021 then (if i < 1014 then (if i < 1011 then (if i < 1009 then decide (5 ≤ count1004 b) else (if i < 1010 then decide (6 ≤ count1004 b) else decide (7 ≤ count1004 b))) else (if i < 1012 then decide (8 ≤ count1004 b) else (if i < 1013 then decide (9 ≤ count1004 b) else decide (10 ≤ count1004 b)))) else (if i < 1017 then (if i < 1015 then decide (11 ≤ count1004 b) else (if i < 1016 then decide (12 ≤ count1004 b) else decide (13 ≤ count1004 b))) else (if i < 1019 then (if i < 1018 then decide (14 ≤ count1004 b) else decide (15 ≤ count1004 b)) else (if i < 1020 then decide (1 ≤ count1019 b) else decide (2 ≤ count1019 b))))) else (if i < 1028 then (if i < 1024 then (if i < 1022 then decide (1 ≤ count1021 b) else (if i < 1023 then decide (2 ≤ count1021 b) else decide (1 ≤ count1023 b))) else (if i < 1026 then (if i < 1025 then decide (2 ≤ count1023 b) else decide (3 ≤ count1023 b)) else (if i < 1027 then decide (4 ≤ count1023 b) else decide (1 ≤ count1027 b)))) else (if i < 1031 then (if i < 1029 then decide (2 ≤ count1027 b) else (if i < 1030 then decide (1 ≤ count1029 b) else decide (2 ≤ count1029 b))) else (if i < 1033 then (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b)) else (if i < 1034 then decide (3 ≤ count1031 b) else decide (4 ≤ count1031 b))))))) else (if i < 1062 then (if i < 1048 then (if i < 1041 then (if i < 1038 then (if i < 1036 then decide (1 ≤ count1035 b) else (if i < 1037 then decide (2 ≤ count1035 b) else decide (3 ≤ count1035 b))) else (if i < 1039 then decide (4 ≤ count1035 b) else (if i < 1040 then decide (5 ≤ count1035 b) else decide (6 ≤ count1035 b)))) else (if i < 1044 then (if i < 1042 then decide (7 ≤ count1035 b) else (if i < 1043 then decide (8 ≤ count1035 b) else decide (1 ≤ count1043 b))) else (if i < 1046 then (if i < 1045 then decide (2 ≤ count1043 b) else decide (1 ≤ count1045 b)) else (if i < 1047 then decide (2 ≤ count1045 b) else decide (1 ≤ count1047 b))))) else (if i < 1055 then (if i < 1051 then (if i < 1049 then decide (2 ≤ count1047 b) else (if i < 1050 then decide (3 ≤ count1047 b) else decide (4 ≤ count1047 b))) else (if i < 1053 then (if i < 1052 then decide (1 ≤ count1051 b) else decide (2 ≤ count1051 b)) else (if i < 1054 then decide (1 ≤ count1053 b) else decide (2 ≤ count1053 b)))) else (if i < 1058 then (if i < 1056 then decide (1 ≤ count1055 b) else (if i < 1057 then decide (2 ≤ count1055 b) else decide (3 ≤ count1055 b))) else (if i < 1060 then (if i < 1059 then decide (4 ≤ count1055 b) else decide (1 ≤ count1059 b)) else (if i < 1061 then decide (2 ≤ count1059 b) else decide (3 ≤ count1059 b)))))) else (if i < 1076 then (if i < 1069 then (if i < 1065 then (if i < 1063 then decide (4 ≤ count1059 b) else (if i < 1064 then decide (5 ≤ count1059 b) else decide (6 ≤ count1059 b))) else (if i < 1067 then (if i < 1066 then decide (7 ≤ count1059 b) else decide (8 ≤ count1059 b)) else (if i < 1068 then decide (1 ≤ count1067 b) else decide (2 ≤ count1067 b)))) else (if i < 1072 then (if i < 1070 then decide (3 ≤ count1067 b) else (if i < 1071 then decide (4 ≤ count1067 b) else decide (5 ≤ count1067 b))) else (if i < 1074 then (if i < 1073 then decide (6 ≤ count1067 b) else decide (7 ≤ count1067 b)) else (if i < 1075 then decide (8 ≤ count1067 b) else decide (9 ≤ count1067 b))))) else (if i < 1083 then (if i < 1079 then (if i < 1077 then decide (10 ≤ count1067 b) else (if i < 1078 then decide (11 ≤ count1067 b) else decide (12 ≤ count1067 b))) else (if i < 1081 then (if i < 1080 then decide (13 ≤ count1067 b) else decide (14 ≤ count1067 b)) else (if i < 1082 then decide (15 ≤ count1067 b) else decide (16 ≤ count1067 b)))) else (if i < 1086 then (if i < 1084 then decide (1 ≤ count1083 b) else (if i < 1085 then decide (2 ≤ count1083 b) else decide (3 ≤ count1083 b))) else (if i < 1088 then (if i < 1087 then decide (4 ≤ count1083 b) else decide (5 ≤ count1083 b)) else (if i < 1089 then decide (6 ≤ count1083 b) else decide (7 ≤ count1083 b))))))))) else (if i < 1199 then (if i < 1144 then (if i < 1117 then (if i < 1103 then (if i < 1096 then (if i < 1093 then (if i < 1091 then decide (8 ≤ count1083 b) else (if i < 1092 then decide (9 ≤ count1083 b) else decide (10 ≤ count1083 b))) else (if i < 1094 then decide (11 ≤ count1083 b) else (if i < 1095 then decide (12 ≤ count1083 b) else decide (13 ≤ count1083 b)))) else (if i < 1099 then (if i < 1097 then decide (14 ≤ count1083 b) else (if i < 1098 then decide (15 ≤ count1083 b) else decide (16 ≤ count1083 b))) else (if i < 1101 then (if i < 1100 then decide (17 ≤ count1083 b) else decide (18 ≤ count1083 b)) else (if i < 1102 then decide (19 ≤ count1083 b) else decide (20 ≤ count1083 b))))) else (if i < 1110 then (if i < 1106 then (if i < 1104 then decide (21 ≤ count1083 b) else (if i < 1105 then decide (1 ≤ count1104 b) else decide (2 ≤ count1104 b))) else (if i < 1108 then (if i < 1107 then decide (3 ≤ count1104 b) else decide (4 ≤ count1104 b)) else (if i < 1109 then decide (5 ≤ count1104 b) else decide (6 ≤ count1104 b)))) else (if i < 1113 then (if i < 1111 then decide (7 ≤ count1104 b) else (if i < 1112 then decide (8 ≤ count1104 b) else decide (9 ≤ count1104 b))) else (if i < 1115 then (if i < 1114 then decide (10 ≤ count1104 b) else decide (11 ≤ count1104 b)) else (if i < 1116 then decide (12 ≤ count1104 b) else decide (13 ≤ count1104 b)))))) else (if i < 1130 then (if i < 1123 then (if i < 1120 then (if i < 1118 then decide (14 ≤ count1104 b) else (if i < 1119 then decide (15 ≤ count1104 b) else decide (16 ≤ count1104 b))) else (if i < 1121 then decide (17 ≤ count1104 b) else (if i < 1122 then decide (18 ≤ count1104 b) else decide (19 ≤ count1104 b)))) else (if i < 1126 then (if i < 1124 then decide (20 ≤ count1104 b) else (if i < 1125 then decide (21 ≤ count1104 b) else decide (1 ≤ count1125 b))) else (if i < 1128 then (if i < 1127 then decide (2 ≤ count1125 b) else decide (1 ≤ count1127 b)) else (if i < 1129 then decide (2 ≤ count1127 b) else decide (3 ≤ count1127 b))))) else (if i < 1137 then (if i < 1133 then (if i < 1131 then decide (1 ≤ count1130 b) else (if i < 1132 then decide (2 ≤ count1130 b) else decide (1 ≤ count1132 b))) else (if i < 1135 then (if i < 1134 then decide (2 ≤ count1132 b) else decide (1 ≤ count1134 b)) else (if i < 1136 then decide (2 ≤ count1134 b) else decide (3 ≤ count1134 b)))) else (if i < 1140 then (if i < 1138 then decide (4 ≤ count1134 b) else (if i < 1139 then decide (1 ≤ count1138 b) else decide (2 ≤ count1138 b))) else (if i < 1142 then (if i < 1141 then decide (3 ≤ count1138 b) else decide (4 ≤ count1138 b)) else (if i < 1143 then decide (5 ≤ count1138 b) else decide (6 ≤ count1138 b))))))) else (if i < 1171 then (if i < 1157 then (if i < 1150 then (if i < 1147 then (if i < 1145 then decide (7 ≤ count1138 b) else (if i < 1146 then decide (1 ≤ count1145 b) else decide (2 ≤ count1145 b))) else (if i < 1148 then decide (1 ≤ count1147 b) else (if i < 1149 then decide (2 ≤ count1147 b) else decide (3 ≤ count1147 b)))) else (if i < 1153 then (if i < 1151 then decide (1 ≤ count1150 b) else (if i < 1152 then decide (2 ≤ count1150 b) else decide (1 ≤ count1152 b))) else (if i < 1155 then (if i < 1154 then decide (2 ≤ count1152 b) else decide (1 ≤ count1154 b)) else (if i < 1156 then decide (2 ≤ count1154 b) else decide (3 ≤ count1154 b))))) else (if i < 1164 then (if i < 1160 then (if i < 1158 then decide (4 ≤ count1154 b) else (if i < 1159 then decide (1 ≤ count1158 b) else decide (2 ≤ count1158 b))) else (if i < 1162 then (if i < 1161 then decide (3 ≤ count1158 b) else decide (4 ≤ count1158 b)) else (if i < 1163 then decide (5 ≤ count1158 b) else decide (6 ≤ count1158 b)))) else (if i < 1167 then (if i < 1165 then decide (7 ≤ count1158 b) else (if i < 1166 then decide (1 ≤ count1165 b) else decide (2 ≤ count1165 b))) else (if i < 1169 then (if i < 1168 then decide (3 ≤ count1165 b) else decide (4 ≤ count1165 b)) else (if i < 1170 then decide (5 ≤ count1165 b) else decide (6 ≤ count1165 b)))))) else (if i < 1185 then (if i < 1178 then (if i < 1174 then (if i < 1172 then decide (7 ≤ count1165 b) else (if i < 1173 then decide (8 ≤ count1165 b) else decide (9 ≤ count1165 b))) else (if i < 1176 then (if i < 1175 then decide (10 ≤ count1165 b) else decide (11 ≤ count1165 b)) else (if i < 1177 then decide (12 ≤ count1165 b) else decide (13 ≤ count1165 b)))) else (if i < 1181 then (if i < 1179 then decide (14 ≤ count1165 b) else (if i < 1180 then decide (1 ≤ count1179 b) else decide (2 ≤ count1179 b))) else (if i < 1183 then (if i < 1182 then decide (1 ≤ count1181 b) else decide (2 ≤ count1181 b)) else (if i < 1184 then decide (3 ≤ count1181 b) else decide (1 ≤ count1184 b))))) else (if i < 1192 then (if i < 1188 then (if i < 1186 then decide (2 ≤ count1184 b) else (if i < 1187 then decide (1 ≤ count1186 b) else decide (2 ≤ count1186 b))) else (if i < 1190 then (if i < 1189 then decide (1 ≤ count1188 b) else decide (2 ≤ count1188 b)) else (if i < 1191 then decide (3 ≤ count1188 b) else decide (4 ≤ count1188 b)))) else (if i < 1195 then (if i < 1193 then decide (1 ≤ count1192 b) else (if i < 1194 then decide (2 ≤ count1192 b) else decide (3 ≤ count1192 b))) else (if i < 1197 then (if i < 1196 then decide (4 ≤ count1192 b) else decide (5 ≤ count1192 b)) else (if i < 1198 then decide (6 ≤ count1192 b) else decide (7 ≤ count1192 b)))))))) else (if i < 1253 then (if i < 1226 then (if i < 1212 then (if i < 1205 then (if i < 1202 then (if i < 1200 then decide (1 ≤ count1199 b) else (if i < 1201 then decide (2 ≤ count1199 b) else decide (1 ≤ count1201 b))) else (if i < 1203 then decide (2 ≤ count1201 b) else (if i < 1204 then decide (1 ≤ count1203 b) else decide (2 ≤ count1203 b)))) else (if i < 1208 then (if i < 1206 then decide (3 ≤ count1203 b) else (if i < 1207 then decide (4 ≤ count1203 b) else decide (1 ≤ count1207 b))) else (if i < 1210 then (if i < 1209 then decide (2 ≤ count1207 b) else decide (1 ≤ count1209 b)) else (if i < 1211 then decide (2 ≤ count1209 b) else decide (1 ≤ count1211 b))))) else (if i < 1219 then (if i < 1215 then (if i < 1213 then decide (2 ≤ count1211 b) else (if i < 1214 then decide (3 ≤ count1211 b) else decide (4 ≤ count1211 b))) else (if i < 1217 then (if i < 1216 then decide (1 ≤ count1215 b) else decide (2 ≤ count1215 b)) else (if i < 1218 then decide (3 ≤ count1215 b) else decide (4 ≤ count1215 b)))) else (if i < 1222 then (if i < 1220 then decide (5 ≤ count1215 b) else (if i < 1221 then decide (6 ≤ count1215 b) else decide (7 ≤ count1215 b))) else (if i < 1224 then (if i < 1223 then decide (8 ≤ count1215 b) else decide (1 ≤ count1223 b)) else (if i < 1225 then decide (2 ≤ count1223 b) else decide (3 ≤ count1223 b)))))) else (if i < 1239 then (if i < 1232 then (if i < 1229 then (if i < 1227 then decide (4 ≤ count1223 b) else (if i < 1228 then decide (5 ≤ count1223 b) else decide (6 ≤ count1223 b))) else (if i < 1230 then decide (7 ≤ count1223 b) else (if i < 1231 then decide (8 ≤ count1223 b) else decide (9 ≤ count1223 b)))) else (if i < 1235 then (if i < 1233 then decide (10 ≤ count1223 b) else (if i < 1234 then decide (11 ≤ count1223 b) else decide (12 ≤ count1223 b))) else (if i < 1237 then (if i < 1236 then decide (13 ≤ count1223 b) else decide (14 ≤ count1223 b)) else (if i < 1238 then decide (15 ≤ count1223 b) else decide (1 ≤ count1238 b))))) else (if i < 1246 then (if i < 1242 then (if i < 1240 then decide (2 ≤ count1238 b) else (if i < 1241 then decide (3 ≤ count1238 b) else decide (4 ≤ count1238 b))) else (if i < 1244 then (if i < 1243 then decide (5 ≤ count1238 b) else decide (6 ≤ count1238 b)) else (if i < 1245 then decide (7 ≤ count1238 b) else decide (8 ≤ count1238 b)))) else (if i < 1249 then (if i < 1247 then decide (9 ≤ count1238 b) else (if i < 1248 then decide (10 ≤ count1238 b) else decide (11 ≤ count1238 b))) else (if i < 1251 then (if i < 1250 then decide (12 ≤ count1238 b) else decide (13 ≤ count1238 b)) else (if i < 1252 then decide (14 ≤ count1238 b) else decide (15 ≤ count1238 b))))))) else (if i < 1280 then (if i < 1266 then (if i < 1259 then (if i < 1256 then (if i < 1254 then decide (16 ≤ count1238 b) else (if i < 1255 then decide (17 ≤ count1238 b) else decide (18 ≤ count1238 b))) else (if i < 1257 then decide (19 ≤ count1238 b) else (if i < 1258 then decide (20 ≤ count1238 b) else decide (21 ≤ count1238 b)))) else (if i < 1262 then (if i < 1260 then decide (22 ≤ count1238 b) else (if i < 1261 then decide (23 ≤ count1238 b) else decide (24 ≤ count1238 b))) else (if i < 1264 then (if i < 1263 then decide (25 ≤ count1238 b) else decide (26 ≤ count1238 b)) else (if i < 1265 then decide (27 ≤ count1238 b) else decide (28 ≤ count1238 b))))) else (if i < 1273 then (if i < 1269 then (if i < 1267 then decide (29 ≤ count1238 b) else (if i < 1268 then decide (1 ≤ count1267 b) else decide (2 ≤ count1267 b))) else (if i < 1271 then (if i < 1270 then decide (1 ≤ count1269 b) else decide (2 ≤ count1269 b)) else (if i < 1272 then decide (3 ≤ count1269 b) else decide (1 ≤ count1272 b)))) else (if i < 1276 then (if i < 1274 then decide (2 ≤ count1272 b) else (if i < 1275 then decide (1 ≤ count1274 b) else decide (2 ≤ count1274 b))) else (if i < 1278 then (if i < 1277 then decide (1 ≤ count1276 b) else decide (2 ≤ count1276 b)) else (if i < 1279 then decide (3 ≤ count1276 b) else decide (4 ≤ count1276 b)))))) else (if i < 1294 then (if i < 1287 then (if i < 1283 then (if i < 1281 then decide (1 ≤ count1280 b) else (if i < 1282 then decide (2 ≤ count1280 b) else decide (3 ≤ count1280 b))) else (if i < 1285 then (if i < 1284 then decide (4 ≤ count1280 b) else decide (5 ≤ count1280 b)) else (if i < 1286 then decide (6 ≤ count1280 b) else decide (7 ≤ count1280 b)))) else (if i < 1290 then (if i < 1288 then decide (1 ≤ count1287 b) else (if i < 1289 then decide (2 ≤ count1287 b) else decide (1 ≤ count1289 b))) else (if i < 1292 then (if i < 1291 then decide (2 ≤ count1289 b) else decide (1 ≤ count1291 b)) else (if i < 1293 then decide (2 ≤ count1291 b) else decide (3 ≤ count1291 b))))) else (if i < 1301 then (if i < 1297 then (if i < 1295 then decide (4 ≤ count1291 b) else (if i < 1296 then decide (1 ≤ count1295 b) else decide (2 ≤ count1295 b))) else (if i < 1299 then (if i < 1298 then decide (1 ≤ count1297 b) else decide (2 ≤ count1297 b)) else (if i < 1300 then decide (1 ≤ count1299 b) else decide (2 ≤ count1299 b)))) else (if i < 1304 then (if i < 1302 then decide (3 ≤ count1299 b) else (if i < 1303 then decide (4 ≤ count1299 b) else decide (1 ≤ count1303 b))) else (if i < 1306 then (if i < 1305 then decide (2 ≤ count1303 b) else decide (3 ≤ count1303 b)) else (if i < 1307 then decide (4 ≤ count1303 b) else decide (5 ≤ count1303 b)))))))))) else (if i < 1526 then (if i < 1417 then (if i < 1362 then (if i < 1335 then (if i < 1321 then (if i < 1314 then (if i < 1311 then (if i < 1309 then decide (6 ≤ count1303 b) else (if i < 1310 then decide (7 ≤ count1303 b) else decide (8 ≤ count1303 b))) else (if i < 1312 then decide (1 ≤ count1311 b) else (if i < 1313 then decide (2 ≤ count1311 b) else decide (3 ≤ count1311 b)))) else (if i < 1317 then (if i < 1315 then decide (4 ≤ count1311 b) else (if i < 1316 then decide (5 ≤ count1311 b) else decide (6 ≤ count1311 b))) else (if i < 1319 then (if i < 1318 then decide (7 ≤ count1311 b) else decide (8 ≤ count1311 b)) else (if i < 1320 then decide (9 ≤ count1311 b) else decide (10 ≤ count1311 b))))) else (if i < 1328 then (if i < 1324 then (if i < 1322 then decide (11 ≤ count1311 b) else (if i < 1323 then decide (12 ≤ count1311 b) else decide (13 ≤ count1311 b))) else (if i < 1326 then (if i < 1325 then decide (14 ≤ count1311 b) else decide (15 ≤ count1311 b)) else (if i < 1327 then decide (1 ≤ count1326 b) else decide (2 ≤ count1326 b)))) else (if i < 1331 then (if i < 1329 then decide (1 ≤ count1328 b) else (if i < 1330 then decide (2 ≤ count1328 b) else decide (3 ≤ count1328 b))) else (if i < 1333 then (if i < 1332 then decide (1 ≤ count1331 b) else decide (2 ≤ count1331 b)) else (if i < 1334 then decide (1 ≤ count1333 b) else decide (2 ≤ count1333 b)))))) else (if i < 1348 then (if i < 1341 then (if i < 1338 then (if i < 1336 then decide (1 ≤ count1335 b) else (if i < 1337 then decide (2 ≤ count1335 b) else decide (3 ≤ count1335 b))) else (if i < 1339 then decide (4 ≤ count1335 b) else (if i < 1340 then decide (1 ≤ count1339 b) else decide (2 ≤ count1339 b)))) else (if i < 1344 then (if i < 1342 then decide (3 ≤ count1339 b) else (if i < 1343 then decide (4 ≤ count1339 b) else decide (5 ≤ count1339 b))) else (if i < 1346 then (if i < 1345 then decide (6 ≤ count1339 b) else decide (7 ≤ count1339 b)) else (if i < 1347 then decide (1 ≤ count1346 b) else decide (2 ≤ count1346 b))))) else (if i < 1355 then (if i < 1351 then (if i < 1349 then decide (1 ≤ count1348 b) else (if i < 1350 then decide (2 ≤ count1348 b) else decide (1 ≤ count1350 b))) else (if i < 1353 then (if i < 1352 then decide (2 ≤ count1350 b) else decide (3 ≤ count1350 b)) else (if i < 1354 then decide (4 ≤ count1350 b) else decide (1 ≤ count1354 b)))) else (if i < 1358 then (if i < 1356 then decide (2 ≤ count1354 b) else (if i < 1357 then decide (1 ≤ count1356 b) else decide (2 ≤ count1356 b))) else (if i < 1360 then (if i < 1359 then decide (1 ≤ count1358 b) else decide (2 ≤ count1358 b)) else (if i < 1361 then decide (3 ≤ count1358 b) else decide (4 ≤ count1358 b))))))) else (if i < 1389 then (if i < 1375 then (if i < 1368 then (if i < 1365 then (if i < 1363 then decide (1 ≤ count1362 b) else (if i < 1364 then decide (2 ≤ count1362 b) else decide (3 ≤ count1362 b))) else (if i < 1366 then decide (4 ≤ count1362 b) else (if i < 1367 then decide (5 ≤ count1362 b) else decide (6 ≤ count1362 b)))) else (if i < 1371 then (if i < 1369 then decide (7 ≤ count1362 b) else (if i < 1370 then decide (8 ≤ count1362 b) else decide (1 ≤ count1370 b))) else (if i < 1373 then (if i < 1372 then decide (2 ≤ count1370 b) else decide (3 ≤ count1370 b)) else (if i < 1374 then decide (4 ≤ count1370 b) else decide (5 ≤ count1370 b))))) else (if i < 1382 then (if i < 1378 then (if i < 1376 then decide (6 ≤ count1370 b) else (if i < 1377 then decide (7 ≤ count1370 b) else decide (8 ≤ count1370 b))) else (if i < 1380 then (if i < 1379 then decide (9 ≤ count1370 b) else decide (10 ≤ count1370 b)) else (if i < 1381 then decide (11 ≤ count1370 b) else decide (12 ≤ count1370 b)))) else (if i < 1385 then (if i < 1383 then decide (13 ≤ count1370 b) else (if i < 1384 then decide (14 ≤ count1370 b) else decide (15 ≤ count1370 b))) else (if i < 1387 then (if i < 1386 then decide (1 ≤ count1385 b) else decide (2 ≤ count1385 b)) else (if i < 1388 then decide (3 ≤ count1385 b) else decide (4 ≤ count1385 b)))))) else (if i < 1403 then (if i < 1396 then (if i < 1392 then (if i < 1390 then decide (5 ≤ count1385 b) else (if i < 1391 then decide (6 ≤ count1385 b) else decide (7 ≤ count1385 b))) else (if i < 1394 then (if i < 1393 then decide (8 ≤ count1385 b) else decide (9 ≤ count1385 b)) else (if i < 1395 then decide (10 ≤ count1385 b) else decide (11 ≤ count1385 b)))) else (if i < 1399 then (if i < 1397 then decide (12 ≤ count1385 b) else (if i < 1398 then decide (13 ≤ count1385 b) else decide (14 ≤ count1385 b))) else (if i < 1401 then (if i < 1400 then decide (15 ≤ count1385 b) else decide (16 ≤ count1385 b)) else (if i < 1402 then decide (17 ≤ count1385 b) else decide (18 ≤ count1385 b))))) else (if i < 1410 then (if i < 1406 then (if i < 1404 then decide (19 ≤ count1385 b) else (if i < 1405 then decide (20 ≤ count1385 b) else decide (21 ≤ count1385 b))) else (if i < 1408 then (if i < 1407 then decide (22 ≤ count1385 b) else decide (23 ≤ count1385 b)) else (if i < 1409 then decide (24 ≤ count1385 b) else decide (25 ≤ count1385 b)))) else (if i < 1413 then (if i < 1411 then decide (26 ≤ count1385 b) else (if i < 1412 then decide (27 ≤ count1385 b) else decide (28 ≤ count1385 b))) else (if i < 1415 then (if i < 1414 then decide (29 ≤ count1385 b) else decide (30 ≤ count1385 b)) else (if i < 1416 then decide (1 ≤ count1415 b) else decide (2 ≤ count1415 b)))))))) else (if i < 1471 then (if i < 1444 then (if i < 1430 then (if i < 1423 then (if i < 1420 then (if i < 1418 then decide (3 ≤ count1415 b) else (if i < 1419 then decide (4 ≤ count1415 b) else decide (5 ≤ count1415 b))) else (if i < 1421 then decide (6 ≤ count1415 b) else (if i < 1422 then decide (7 ≤ count1415 b) else decide (8 ≤ count1415 b)))) else (if i < 1426 then (if i < 1424 then decide (9 ≤ count1415 b) else (if i < 1425 then decide (10 ≤ count1415 b) else decide (11 ≤ count1415 b))) else (if i < 1428 then (if i < 1427 then decide (12 ≤ count1415 b) else decide (13 ≤ count1415 b)) else (if i < 1429 then decide (14 ≤ count1415 b) else decide (15 ≤ count1415 b))))) else (if i < 1437 then (if i < 1433 then (if i < 1431 then decide (16 ≤ count1415 b) else (if i < 1432 then decide (17 ≤ count1415 b) else decide (18 ≤ count1415 b))) else (if i < 1435 then (if i < 1434 then decide (19 ≤ count1415 b) else decide (20 ≤ count1415 b)) else (if i < 1436 then decide (21 ≤ count1415 b) else decide (22 ≤ count1415 b)))) else (if i < 1440 then (if i < 1438 then decide (23 ≤ count1415 b) else (if i < 1439 then decide (24 ≤ count1415 b) else decide (25 ≤ count1415 b))) else (if i < 1442 then (if i < 1441 then decide (26 ≤ count1415 b) else decide (27 ≤ count1415 b)) else (if i < 1443 then decide (28 ≤ count1415 b) else decide (29 ≤ count1415 b)))))) else (if i < 1457 then (if i < 1450 then (if i < 1447 then (if i < 1445 then decide (30 ≤ count1415 b) else (if i < 1446 then decide (31 ≤ count1415 b) else decide (32 ≤ count1415 b))) else (if i < 1448 then decide (33 ≤ count1415 b) else (if i < 1449 then decide (34 ≤ count1415 b) else decide (35 ≤ count1415 b)))) else (if i < 1453 then (if i < 1451 then decide (36 ≤ count1415 b) else (if i < 1452 then decide (37 ≤ count1415 b) else decide (38 ≤ count1415 b))) else (if i < 1455 then (if i < 1454 then decide (39 ≤ count1415 b) else decide (40 ≤ count1415 b)) else (if i < 1456 then decide (41 ≤ count1415 b) else decide (42 ≤ count1415 b))))) else (if i < 1464 then (if i < 1460 then (if i < 1458 then decide (1 ≤ count1457 b) else (if i < 1459 then decide (2 ≤ count1457 b) else decide (1 ≤ count1459 b))) else (if i < 1462 then (if i < 1461 then decide (2 ≤ count1459 b) else decide (3 ≤ count1459 b)) else (if i < 1463 then decide (1 ≤ count1462 b) else decide (2 ≤ count1462 b)))) else (if i < 1467 then (if i < 1465 then decide (1 ≤ count1464 b) else (if i < 1466 then decide (2 ≤ count1464 b) else decide (1 ≤ count1466 b))) else (if i < 1469 then (if i < 1468 then decide (2 ≤ count1466 b) else decide (3 ≤ count1466 b)) else (if i < 1470 then decide (4 ≤ count1466 b) else decide (1 ≤ count1470 b))))))) else (if i < 1498 then (if i < 1484 then (if i < 1477 then (if i < 1474 then (if i < 1472 then decide (2 ≤ count1470 b) else (if i < 1473 then decide (3 ≤ count1470 b) else decide (4 ≤ count1470 b))) else (if i < 1475 then decide (5 ≤ count1470 b) else (if i < 1476 then decide (6 ≤ count1470 b) else decide (7 ≤ count1470 b)))) else (if i < 1480 then (if i < 1478 then decide (1 ≤ count1477 b) else (if i < 1479 then decide (2 ≤ count1477 b) else decide (1 ≤ count1479 b))) else (if i < 1482 then (if i < 1481 then decide (2 ≤ count1479 b) else decide (3 ≤ count1479 b)) else (if i < 1483 then decide (1 ≤ count1482 b) else decide (2 ≤ count1482 b))))) else (if i < 1491 then (if i < 1487 then (if i < 1485 then decide (1 ≤ count1484 b) else (if i < 1486 then decide (2 ≤ count1484 b) else decide (1 ≤ count1486 b))) else (if i < 1489 then (if i < 1488 then decide (2 ≤ count1486 b) else decide (3 ≤ count1486 b)) else (if i < 1490 then decide (4 ≤ count1486 b) else decide (1 ≤ count1490 b)))) else (if i < 1494 then (if i < 1492 then decide (2 ≤ count1490 b) else (if i < 1493 then decide (3 ≤ count1490 b) else decide (4 ≤ count1490 b))) else (if i < 1496 then (if i < 1495 then decide (5 ≤ count1490 b) else decide (6 ≤ count1490 b)) else (if i < 1497 then decide (7 ≤ count1490 b) else decide (1 ≤ count1497 b)))))) else (if i < 1512 then (if i < 1505 then (if i < 1501 then (if i < 1499 then decide (2 ≤ count1497 b) else (if i < 1500 then decide (3 ≤ count1497 b) else decide (4 ≤ count1497 b))) else (if i < 1503 then (if i < 1502 then decide (5 ≤ count1497 b) else decide (6 ≤ count1497 b)) else (if i < 1504 then decide (7 ≤ count1497 b) else decide (8 ≤ count1497 b)))) else (if i < 1508 then (if i < 1506 then decide (9 ≤ count1497 b) else (if i < 1507 then decide (10 ≤ count1497 b) else decide (11 ≤ count1497 b))) else (if i < 1510 then (if i < 1509 then decide (12 ≤ count1497 b) else decide (13 ≤ count1497 b)) else (if i < 1511 then decide (14 ≤ count1497 b) else decide (1 ≤ count1511 b))))) else (if i < 1519 then (if i < 1515 then (if i < 1513 then decide (2 ≤ count1511 b) else (if i < 1514 then decide (1 ≤ count1513 b) else decide (2 ≤ count1513 b))) else (if i < 1517 then (if i < 1516 then decide (3 ≤ count1513 b) else decide (1 ≤ count1516 b)) else (if i < 1518 then decide (2 ≤ count1516 b) else decide (1 ≤ count1518 b)))) else (if i < 1522 then (if i < 1520 then decide (2 ≤ count1518 b) else (if i < 1521 then decide (1 ≤ count1520 b) else decide (2 ≤ count1520 b))) else (if i < 1524 then (if i < 1523 then decide (3 ≤ count1520 b) else decide (4 ≤ count1520 b)) else (if i < 1525 then decide (1 ≤ count1524 b) else decide (2 ≤ count1524 b))))))))) else (if i < 1635 then (if i < 1580 then (if i < 1553 then (if i < 1539 then (if i < 1532 then (if i < 1529 then (if i < 1527 then decide (3 ≤ count1524 b) else (if i < 1528 then decide (4 ≤ count1524 b) else decide (5 ≤ count1524 b))) else (if i < 1530 then decide (6 ≤ count1524 b) else (if i < 1531 then decide (7 ≤ count1524 b) else decide (1 ≤ count1531 b)))) else (if i < 1535 then (if i < 1533 then decide (2 ≤ count1531 b) else (if i < 1534 then decide (1 ≤ count1533 b) else decide (2 ≤ count1533 b))) else (if i < 1537 then (if i < 1536 then decide (1 ≤ count1535 b) else decide (2 ≤ count1535 b)) else (if i < 1538 then decide (3 ≤ count1535 b) else decide (4 ≤ count1535 b))))) else (if i < 1546 then (if i < 1542 then (if i < 1540 then decide (1 ≤ count1539 b) else (if i < 1541 then decide (2 ≤ count1539 b) else decide (1 ≤ count1541 b))) else (if i < 1544 then (if i < 1543 then decide (2 ≤ count1541 b) else decide (1 ≤ count1543 b)) else (if i < 1545 then decide (2 ≤ count1543 b) else decide (3 ≤ count1543 b)))) else (if i < 1549 then (if i < 1547 then decide (4 ≤ count1543 b) else (if i < 1548 then decide (1 ≤ count1547 b) else decide (2 ≤ count1547 b))) else (if i < 1551 then (if i < 1550 then decide (3 ≤ count1547 b) else decide (4 ≤ count1547 b)) else (if i < 1552 then decide (5 ≤ count1547 b) else decide (6 ≤ count1547 b)))))) else (if i < 1566 then (if i < 1559 then (if i < 1556 then (if i < 1554 then decide (7 ≤ count1547 b) else (if i < 1555 then decide (8 ≤ count1547 b) else decide (1 ≤ count1555 b))) else (if i < 1557 then decide (2 ≤ count1555 b) else (if i < 1558 then decide (3 ≤ count1555 b) else decide (4 ≤ count1555 b)))) else (if i < 1562 then (if i < 1560 then decide (5 ≤ count1555 b) else (if i < 1561 then decide (6 ≤ count1555 b) else decide (7 ≤ count1555 b))) else (if i < 1564 then (if i < 1563 then decide (8 ≤ count1555 b) else decide (9 ≤ count1555 b)) else (if i < 1565 then decide (10 ≤ count1555 b) else decide (11 ≤ count1555 b))))) else (if i < 1573 then (if i < 1569 then (if i < 1567 then decide (12 ≤ count1555 b) else (if i < 1568 then decide (13 ≤ count1555 b) else decide (14 ≤ count1555 b))) else (if i < 1571 then (if i < 1570 then decide (15 ≤ count1555 b) else decide (1 ≤ count1570 b)) else (if i < 1572 then decide (2 ≤ count1570 b) else decide (3 ≤ count1570 b)))) else (if i < 1576 then (if i < 1574 then decide (4 ≤ count1570 b) else (if i < 1575 then decide (5 ≤ count1570 b) else decide (6 ≤ count1570 b))) else (if i < 1578 then (if i < 1577 then decide (7 ≤ count1570 b) else decide (8 ≤ count1570 b)) else (if i < 1579 then decide (9 ≤ count1570 b) else decide (10 ≤ count1570 b))))))) else (if i < 1607 then (if i < 1593 then (if i < 1586 then (if i < 1583 then (if i < 1581 then decide (11 ≤ count1570 b) else (if i < 1582 then decide (12 ≤ count1570 b) else decide (13 ≤ count1570 b))) else (if i < 1584 then decide (14 ≤ count1570 b) else (if i < 1585 then decide (15 ≤ count1570 b) else decide (16 ≤ count1570 b)))) else (if i < 1589 then (if i < 1587 then decide (17 ≤ count1570 b) else (if i < 1588 then decide (18 ≤ count1570 b) else decide (19 ≤ count1570 b))) else (if i < 1591 then (if i < 1590 then decide (1 ≤ count1589 b) else decide (2 ≤ count1589 b)) else (if i < 1592 then decide (1 ≤ count1591 b) else decide (2 ≤ count1591 b))))) else (if i < 1600 then (if i < 1596 then (if i < 1594 then decide (3 ≤ count1591 b) else (if i < 1595 then decide (1 ≤ count1594 b) else decide (2 ≤ count1594 b))) else (if i < 1598 then (if i < 1597 then decide (1 ≤ count1596 b) else decide (2 ≤ count1596 b)) else (if i < 1599 then decide (1 ≤ count1598 b) else decide (2 ≤ count1598 b)))) else (if i < 1603 then (if i < 1601 then decide (3 ≤ count1598 b) else (if i < 1602 then decide (4 ≤ count1598 b) else decide (1 ≤ count1602 b))) else (if i < 1605 then (if i < 1604 then decide (2 ≤ count1602 b) else decide (3 ≤ count1602 b)) else (if i < 1606 then decide (4 ≤ count1602 b) else decide (5 ≤ count1602 b)))))) else (if i < 1621 then (if i < 1614 then (if i < 1610 then (if i < 1608 then decide (6 ≤ count1602 b) else (if i < 1609 then decide (7 ≤ count1602 b) else decide (1 ≤ count1609 b))) else (if i < 1612 then (if i < 1611 then decide (2 ≤ count1609 b) else decide (1 ≤ count1611 b)) else (if i < 1613 then decide (2 ≤ count1611 b) else decide (1 ≤ count1613 b)))) else (if i < 1617 then (if i < 1615 then decide (2 ≤ count1613 b) else (if i < 1616 then decide (3 ≤ count1613 b) else decide (4 ≤ count1613 b))) else (if i < 1619 then (if i < 1618 then decide (1 ≤ count1617 b) else decide (2 ≤ count1617 b)) else (if i < 1620 then decide (1 ≤ count1619 b) else decide (2 ≤ count1619 b))))) else (if i < 1628 then (if i < 1624 then (if i < 1622 then decide (1 ≤ count1621 b) else (if i < 1623 then decide (2 ≤ count1621 b) else decide (3 ≤ count1621 b))) else (if i < 1626 then (if i < 1625 then decide (4 ≤ count1621 b) else decide (1 ≤ count1625 b)) else (if i < 1627 then decide (2 ≤ count1625 b) else decide (3 ≤ count1625 b)))) else (if i < 1631 then (if i < 1629 then decide (4 ≤ count1625 b) else (if i < 1630 then decide (5 ≤ count1625 b) else decide (6 ≤ count1625 b))) else (if i < 1633 then (if i < 1632 then decide (7 ≤ count1625 b) else decide (8 ≤ count1625 b)) else (if i < 1634 then decide (1 ≤ count1633 b) else decide (2 ≤ count1633 b)))))))) else (if i < 1690 then (if i < 1662 then (if i < 1648 then (if i < 1641 then (if i < 1638 then (if i < 1636 then decide (3 ≤ count1633 b) else (if i < 1637 then decide (4 ≤ count1633 b) else decide (5 ≤ count1633 b))) else (if i < 1639 then decide (6 ≤ count1633 b) else (if i < 1640 then decide (7 ≤ count1633 b) else decide (8 ≤ count1633 b)))) else (if i < 1644 then (if i < 1642 then decide (9 ≤ count1633 b) else (if i < 1643 then decide (10 ≤ count1633 b) else decide (11 ≤ count1633 b))) else (if i < 1646 then (if i < 1645 then decide (12 ≤ count1633 b) else decide (13 ≤ count1633 b)) else (if i < 1647 then decide (14 ≤ count1633 b) else decide (15 ≤ count1633 b))))) else (if i < 1655 then (if i < 1651 then (if i < 1649 then decide (1 ≤ count1648 b) else (if i < 1650 then decide (2 ≤ count1648 b) else decide (1 ≤ count1650 b))) else (if i < 1653 then (if i < 1652 then decide (2 ≤ count1650 b) else decide (3 ≤ count1650 b)) else (if i < 1654 then decide (1 ≤ count1653 b) else decide (2 ≤ count1653 b)))) else (if i < 1658 then (if i < 1656 then decide (1 ≤ count1655 b) else (if i < 1657 then decide (2 ≤ count1655 b) else decide (1 ≤ count1657 b))) else (if i < 1660 then (if i < 1659 then decide (2 ≤ count1657 b) else decide (3 ≤ count1657 b)) else (if i < 1661 then decide (4 ≤ count1657 b) else decide (1 ≤ count1661 b)))))) else (if i < 1676 then (if i < 1669 then (if i < 1665 then (if i < 1663 then decide (2 ≤ count1661 b) else (if i < 1664 then decide (3 ≤ count1661 b) else decide (4 ≤ count1661 b))) else (if i < 1667 then (if i < 1666 then decide (5 ≤ count1661 b) else decide (6 ≤ count1661 b)) else (if i < 1668 then decide (7 ≤ count1661 b) else decide (1 ≤ count1668 b)))) else (if i < 1672 then (if i < 1670 then decide (2 ≤ count1668 b) else (if i < 1671 then decide (1 ≤ count1670 b) else decide (2 ≤ count1670 b))) else (if i < 1674 then (if i < 1673 then decide (1 ≤ count1672 b) else decide (2 ≤ count1672 b)) else (if i < 1675 then decide (3 ≤ count1672 b) else decide (4 ≤ count1672 b))))) else (if i < 1683 then (if i < 1679 then (if i < 1677 then decide (1 ≤ count1676 b) else (if i < 1678 then decide (2 ≤ count1676 b) else decide (1 ≤ count1678 b))) else (if i < 1681 then (if i < 1680 then decide (2 ≤ count1678 b) else decide (1 ≤ count1680 b)) else (if i < 1682 then decide (2 ≤ count1680 b) else decide (3 ≤ count1680 b)))) else (if i < 1686 then (if i < 1684 then decide (4 ≤ count1680 b) else (if i < 1685 then decide (1 ≤ count1684 b) else decide (2 ≤ count1684 b))) else (if i < 1688 then (if i < 1687 then decide (3 ≤ count1684 b) else decide (4 ≤ count1684 b)) else (if i < 1689 then decide (5 ≤ count1684 b) else decide (6 ≤ count1684 b))))))) else (if i < 1717 then (if i < 1703 then (if i < 1696 then (if i < 1693 then (if i < 1691 then decide (7 ≤ count1684 b) else (if i < 1692 then decide (8 ≤ count1684 b) else decide (1 ≤ count1692 b))) else (if i < 1694 then decide (2 ≤ count1692 b) else (if i < 1695 then decide (3 ≤ count1692 b) else decide (4 ≤ count1692 b)))) else (if i < 1699 then (if i < 1697 then decide (5 ≤ count1692 b) else (if i < 1698 then decide (6 ≤ count1692 b) else decide (7 ≤ count1692 b))) else (if i < 1701 then (if i < 1700 then decide (8 ≤ count1692 b) else decide (9 ≤ count1692 b)) else (if i < 1702 then decide (10 ≤ count1692 b) else decide (11 ≤ count1692 b))))) else (if i < 1710 then (if i < 1706 then (if i < 1704 then decide (12 ≤ count1692 b) else (if i < 1705 then decide (13 ≤ count1692 b) else decide (14 ≤ count1692 b))) else (if i < 1708 then (if i < 1707 then decide (15 ≤ count1692 b) else decide (1 ≤ count1707 b)) else (if i < 1709 then decide (2 ≤ count1707 b) else decide (3 ≤ count1707 b)))) else (if i < 1713 then (if i < 1711 then decide (4 ≤ count1707 b) else (if i < 1712 then decide (5 ≤ count1707 b) else decide (6 ≤ count1707 b))) else (if i < 1715 then (if i < 1714 then decide (7 ≤ count1707 b) else decide (8 ≤ count1707 b)) else (if i < 1716 then decide (9 ≤ count1707 b) else decide (10 ≤ count1707 b)))))) else (if i < 1731 then (if i < 1724 then (if i < 1720 then (if i < 1718 then decide (11 ≤ count1707 b) else (if i < 1719 then decide (12 ≤ count1707 b) else decide (13 ≤ count1707 b))) else (if i < 1722 then (if i < 1721 then decide (14 ≤ count1707 b) else decide (15 ≤ count1707 b)) else (if i < 1723 then decide (16 ≤ count1707 b) else decide (17 ≤ count1707 b)))) else (if i < 1727 then (if i < 1725 then decide (18 ≤ count1707 b) else (if i < 1726 then decide (19 ≤ count1707 b) else decide (1 ≤ count1726 b))) else (if i < 1729 then (if i < 1728 then decide (2 ≤ count1726 b) else decide (3 ≤ count1726 b)) else (if i < 1730 then decide (4 ≤ count1726 b) else decide (5 ≤ count1726 b))))) else (if i < 1738 then (if i < 1734 then (if i < 1732 then decide (6 ≤ count1726 b) else (if i < 1733 then decide (7 ≤ count1726 b) else decide (8 ≤ count1726 b))) else (if i < 1736 then (if i < 1735 then decide (9 ≤ count1726 b) else decide (10 ≤ count1726 b)) else (if i < 1737 then decide (11 ≤ count1726 b) else decide (12 ≤ count1726 b)))) else (if i < 1741 then (if i < 1739 then decide (13 ≤ count1726 b) else (if i < 1740 then decide (14 ≤ count1726 b) else decide (15 ≤ count1726 b))) else (if i < 1743 then (if i < 1742 then decide (16 ≤ count1726 b) else decide (17 ≤ count1726 b)) else (if i < 1744 then decide (18 ≤ count1726 b) else decide (19 ≤ count1726 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (9 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (17 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (19 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (25 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (33 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (35 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (39 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (41 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (96 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (98 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (102 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (103 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (104 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (105 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (110 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (113 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (114 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (115 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (117 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (121 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (124 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (125 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (126 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (160 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (162 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (166 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (167 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (168 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (169 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (170 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (174 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (175 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (177 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (178 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (179 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (181 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (185 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (188 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (189 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (225 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (227 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (228 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (229 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (230 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (234 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (235 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (236 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (237 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (240 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (244 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (246 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (247 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (248 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (249 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (250 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (251 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (255 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (353 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (355 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (357 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (358 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (361 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (363 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (364 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (365 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (368 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (372 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (373 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (374 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (375 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (376 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (378 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (379 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (383 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (417 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (419 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (421 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (422 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (423 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (424 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (425 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (427 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (428 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (429 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (431 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (432 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (434 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (436 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (437 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (438 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (440 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (442 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (443 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (447 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (480 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (481 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (482 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (483 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (485 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (486 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (488 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (490 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (492 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (493 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (494 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (495 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (497 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (498 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (499 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (501 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (502 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (503 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (505 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (508 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (509 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (510 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (511 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (9 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (33 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (35 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (39 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (96 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (98 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (104 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (113 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (114 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (117 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (124 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (126 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (174 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (225 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (353 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (358 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (364 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (365 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (372 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (378 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (379 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (422 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (438 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (442 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (490 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (494 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (501 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (505 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (510 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (2 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (2 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value476 (q : Snake 81) : valuation q 476 = decide (2 ≤ count475 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (1 ≤ count1457 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (2 ≤ count1457 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (1 ≤ count1459 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (2 ≤ count1459 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (3 ≤ count1459 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (1 ≤ count1462 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (2 ≤ count1462 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (1 ≤ count1464 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (2 ≤ count1464 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (1 ≤ count1466 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (2 ≤ count1466 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (3 ≤ count1466 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (2 ≤ count1470 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (3 ≤ count1470 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (4 ≤ count1470 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (1 ≤ count1477 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (2 ≤ count1477 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (1 ≤ count1479 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (2 ≤ count1479 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (1 ≤ count1482 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (2 ≤ count1482 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (1 ≤ count1484 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (1 ≤ count1486 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (2 ≤ count1486 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (3 ≤ count1486 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (1 ≤ count1490 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (2 ≤ count1490 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (3 ≤ count1490 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (4 ≤ count1490 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (3 ≤ count1497 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (4 ≤ count1497 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (5 ≤ count1497 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (6 ≤ count1497 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (1 ≤ count1511 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (2 ≤ count1511 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (1 ≤ count1513 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (2 ≤ count1513 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (1 ≤ count1516 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (2 ≤ count1516 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (1 ≤ count1518 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (2 ≤ count1518 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (1 ≤ count1520 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (2 ≤ count1520 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (3 ≤ count1520 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (1 ≤ count1524 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (2 ≤ count1524 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (3 ≤ count1524 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (4 ≤ count1524 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (1 ≤ count1531 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (2 ≤ count1531 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (1 ≤ count1533 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (2 ≤ count1533 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (1 ≤ count1535 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (2 ≤ count1535 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (3 ≤ count1535 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (1 ≤ count1539 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (2 ≤ count1539 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (1 ≤ count1541 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (2 ≤ count1541 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (1 ≤ count1543 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (2 ≤ count1543 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (3 ≤ count1543 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (1 ≤ count1547 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (2 ≤ count1547 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (3 ≤ count1547 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (4 ≤ count1547 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (2 ≤ count1555 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (3 ≤ count1555 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (4 ≤ count1555 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (5 ≤ count1555 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (6 ≤ count1555 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (6 ≤ count1570 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (7 ≤ count1570 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (8 ≤ count1570 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (9 ≤ count1570 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (10 ≤ count1570 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (11 ≤ count1570 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (1 ≤ count1589 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (2 ≤ count1589 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (1 ≤ count1591 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (2 ≤ count1591 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (3 ≤ count1591 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (1 ≤ count1594 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (2 ≤ count1594 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (1 ≤ count1596 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (1 ≤ count1598 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (2 ≤ count1598 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (3 ≤ count1598 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (1 ≤ count1602 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (2 ≤ count1602 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (3 ≤ count1602 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (4 ≤ count1602 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (5 ≤ count1602 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (1 ≤ count1609 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (2 ≤ count1609 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (1 ≤ count1611 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (2 ≤ count1611 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (1 ≤ count1613 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (2 ≤ count1613 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (3 ≤ count1613 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (1 ≤ count1617 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (2 ≤ count1617 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (1 ≤ count1619 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (2 ≤ count1619 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (1 ≤ count1621 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (2 ≤ count1621 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (3 ≤ count1621 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (4 ≤ count1621 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (1 ≤ count1625 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (2 ≤ count1625 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (3 ≤ count1625 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (4 ≤ count1625 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (2 ≤ count1633 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (3 ≤ count1633 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (4 ≤ count1633 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (5 ≤ count1633 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (6 ≤ count1633 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (7 ≤ count1633 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (8 ≤ count1633 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (1 ≤ count1648 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (2 ≤ count1648 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (1 ≤ count1650 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (2 ≤ count1650 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (3 ≤ count1650 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (1 ≤ count1653 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (2 ≤ count1653 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (1 ≤ count1655 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (2 ≤ count1655 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (1 ≤ count1657 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (2 ≤ count1657 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (3 ≤ count1657 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (4 ≤ count1657 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (1 ≤ count1661 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (2 ≤ count1661 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (3 ≤ count1661 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (4 ≤ count1661 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (1 ≤ count1668 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (2 ≤ count1668 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (1 ≤ count1670 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (2 ≤ count1670 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (1 ≤ count1672 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (2 ≤ count1672 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (3 ≤ count1672 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (4 ≤ count1672 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (1 ≤ count1676 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (2 ≤ count1676 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (1 ≤ count1678 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (2 ≤ count1678 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (1 ≤ count1680 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (2 ≤ count1680 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (3 ≤ count1680 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (4 ≤ count1680 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (1 ≤ count1684 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (2 ≤ count1684 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (3 ≤ count1684 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (4 ≤ count1684 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (5 ≤ count1684 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (6 ≤ count1684 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (7 ≤ count1684 (baseVal q)) := rfl
theorem value1694 (q : Snake 81) : valuation q 1694 = decide (3 ≤ count1692 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (4 ≤ count1692 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (5 ≤ count1692 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (6 ≤ count1692 (baseVal q)) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (7 ≤ count1692 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (8 ≤ count1692 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (9 ≤ count1692 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (10 ≤ count1692 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (8 ≤ count1707 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (9 ≤ count1707 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (10 ≤ count1707 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (11 ≤ count1707 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (12 ≤ count1707 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (13 ≤ count1707 (baseVal q)) := rfl
theorem value1744 (q : Snake 81) : valuation q 1744 = decide (19 ≤ count1726 (baseVal q)) := rfl
theorem meaningNeg120 (b : Nat → Bool) : literal (valuationOf b) (-120) = decide (1 ≤ countLit b [-120]) := by
  change literal b (-120) = decide (1 ≤ countLit b [-120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-120) <;> decide
theorem meaningNeg117 (b : Nat → Bool) : literal (valuationOf b) (-117) = decide (1 ≤ countLit b [-117]) := by
  change literal b (-117) = decide (1 ≤ countLit b [-117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-117) <;> decide
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
theorem meaningNeg104 (b : Nat → Bool) : literal (valuationOf b) (-104) = decide (1 ≤ countLit b [-104]) := by
  change literal b (-104) = decide (1 ≤ countLit b [-104])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-104) <;> decide
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
theorem meaningNeg96 (b : Nat → Bool) : literal (valuationOf b) (-96) = decide (1 ≤ countLit b [-96]) := by
  change literal b (-96) = decide (1 ≤ countLit b [-96])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-96) <;> decide
theorem meaningNeg94 (b : Nat → Bool) : literal (valuationOf b) (-94) = decide (1 ≤ countLit b [-94]) := by
  change literal b (-94) = decide (1 ≤ countLit b [-94])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-94) <;> decide
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
theorem meaningNeg88 (b : Nat → Bool) : literal (valuationOf b) (-88) = decide (1 ≤ countLit b [-88]) := by
  change literal b (-88) = decide (1 ≤ countLit b [-88])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-88) <;> decide
theorem meaningNeg86 (b : Nat → Bool) : literal (valuationOf b) (-86) = decide (1 ≤ countLit b [-86]) := by
  change literal b (-86) = decide (1 ≤ countLit b [-86])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-86) <;> decide
theorem meaningNeg84 (b : Nat → Bool) : literal (valuationOf b) (-84) = decide (1 ≤ countLit b [-84]) := by
  change literal b (-84) = decide (1 ≤ countLit b [-84])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-84) <;> decide
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
theorem meaningNeg79 (b : Nat → Bool) : literal (valuationOf b) (-79) = decide (1 ≤ countLit b [-79]) := by
  change literal b (-79) = decide (1 ≤ countLit b [-79])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-79) <;> decide
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
theorem meaningNeg59 (b : Nat → Bool) : literal (valuationOf b) (-59) = decide (1 ≤ countLit b [-59]) := by
  change literal b (-59) = decide (1 ≤ countLit b [-59])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-59) <;> decide
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
theorem meaningNeg53 (b : Nat → Bool) : literal (valuationOf b) (-53) = decide (1 ≤ countLit b [-53]) := by
  change literal b (-53) = decide (1 ≤ countLit b [-53])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-53) <;> decide
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
theorem meaningNeg47 (b : Nat → Bool) : literal (valuationOf b) (-47) = decide (1 ≤ countLit b [-47]) := by
  change literal b (-47) = decide (1 ≤ countLit b [-47])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-47) <;> decide
theorem meaningNeg46 (b : Nat → Bool) : literal (valuationOf b) (-46) = decide (1 ≤ countLit b [-46]) := by
  change literal b (-46) = decide (1 ≤ countLit b [-46])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-46) <;> decide
theorem meaningNeg44 (b : Nat → Bool) : literal (valuationOf b) (-44) = decide (1 ≤ countLit b [-44]) := by
  change literal b (-44) = decide (1 ≤ countLit b [-44])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-44) <;> decide
theorem meaningNeg40 (b : Nat → Bool) : literal (valuationOf b) (-40) = decide (1 ≤ countLit b [-40]) := by
  change literal b (-40) = decide (1 ≤ countLit b [-40])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-40) <;> decide
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
theorem meaningNeg37 (b : Nat → Bool) : literal (valuationOf b) (-37) = decide (1 ≤ countLit b [-37]) := by
  change literal b (-37) = decide (1 ≤ countLit b [-37])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-37) <;> decide
theorem meaningNeg33 (b : Nat → Bool) : literal (valuationOf b) (-33) = decide (1 ≤ countLit b [-33]) := by
  change literal b (-33) = decide (1 ≤ countLit b [-33])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-33) <;> decide
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
theorem meaningNeg27 (b : Nat → Bool) : literal (valuationOf b) (-27) = decide (1 ≤ countLit b [-27]) := by
  change literal b (-27) = decide (1 ≤ countLit b [-27])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-27) <;> decide
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
theorem meaningNeg16 (b : Nat → Bool) : literal (valuationOf b) (-16) = decide (1 ≤ countLit b [-16]) := by
  change literal b (-16) = decide (1 ≤ countLit b [-16])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-16) <;> decide
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
theorem meaningNeg11 (b : Nat → Bool) : literal (valuationOf b) (-11) = decide (1 ≤ countLit b [-11]) := by
  change literal b (-11) = decide (1 ≤ countLit b [-11])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-11) <;> decide
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
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
theorem meaning122 (b : Nat → Bool) : literal (valuationOf b) (122) = decide (1 ≤ countLit b [122]) := by
  change literal b (122) = decide (1 ≤ countLit b [122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (122) <;> decide
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
theorem meaning127 (b : Nat → Bool) : literal (valuationOf b) (127) = decide (1 ≤ countLit b [127]) := by
  change literal b (127) = decide (1 ≤ countLit b [127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (127) <;> decide
theorem meaning130 (b : Nat → Bool) : literal (valuationOf b) (130) = decide (1 ≤ countLit b [130]) := by
  change literal b (130) = decide (1 ≤ countLit b [130])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (130) <;> decide
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
theorem meaning146 (b : Nat → Bool) : literal (valuationOf b) (146) = decide (1 ≤ countLit b [146]) := by
  change literal b (146) = decide (1 ≤ countLit b [146])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (146) <;> decide
theorem meaning155 (b : Nat → Bool) : literal (valuationOf b) (155) = decide (1 ≤ countLit b [155]) := by
  change literal b (155) = decide (1 ≤ countLit b [155])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (155) <;> decide
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
theorem meaning188 (b : Nat → Bool) : literal (valuationOf b) (188) = decide (1 ≤ countLit b [188]) := by
  change literal b (188) = decide (1 ≤ countLit b [188])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (188) <;> decide
theorem meaning189 (b : Nat → Bool) : literal (valuationOf b) (189) = decide (1 ≤ countLit b [189]) := by
  change literal b (189) = decide (1 ≤ countLit b [189])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (189) <;> decide
theorem meaning195 (b : Nat → Bool) : literal (valuationOf b) (195) = decide (1 ≤ countLit b [195]) := by
  change literal b (195) = decide (1 ≤ countLit b [195])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (195) <;> decide
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) (215) = decide (1 ≤ countLit b [215]) := by
  change literal b (215) = decide (1 ≤ countLit b [215])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (215) <;> decide
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) (217) = decide (1 ≤ countLit b [217]) := by
  change literal b (217) = decide (1 ≤ countLit b [217])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (217) <;> decide
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) (218) = decide (1 ≤ countLit b [218]) := by
  change literal b (218) = decide (1 ≤ countLit b [218])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (218) <;> decide
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) (225) = decide (1 ≤ countLit b [225]) := by
  change literal b (225) = decide (1 ≤ countLit b [225])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (225) <;> decide
theorem meaning226 (b : Nat → Bool) : literal (valuationOf b) (226) = decide (1 ≤ countLit b [226]) := by
  change literal b (226) = decide (1 ≤ countLit b [226])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (226) <;> decide
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) (239) = decide (1 ≤ countLit b [239]) := by
  change literal b (239) = decide (1 ≤ countLit b [239])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (239) <;> decide
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) 244 = decide (2 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) 252 = decide (2 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning356 (b : Nat → Bool) : literal (valuationOf b) 356 = decide (2 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning476 (b : Nat → Bool) : literal (valuationOf b) 476 = decide (2 ≤ count475 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (1 ≤ count1457 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (2 ≤ count1457 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (1 ≤ count1459 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (2 ≤ count1459 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (3 ≤ count1459 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (1 ≤ count1462 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (2 ≤ count1462 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (1 ≤ count1464 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (2 ≤ count1464 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (1 ≤ count1466 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (2 ≤ count1466 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (3 ≤ count1466 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (2 ≤ count1470 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (3 ≤ count1470 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (4 ≤ count1470 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (1 ≤ count1477 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (2 ≤ count1477 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (1 ≤ count1479 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (2 ≤ count1479 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (1 ≤ count1482 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (2 ≤ count1482 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (1 ≤ count1484 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (1 ≤ count1486 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (2 ≤ count1486 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (3 ≤ count1486 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (1 ≤ count1490 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (2 ≤ count1490 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (3 ≤ count1490 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (4 ≤ count1490 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (3 ≤ count1497 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (4 ≤ count1497 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (5 ≤ count1497 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (6 ≤ count1497 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (1 ≤ count1511 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (2 ≤ count1511 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (1 ≤ count1513 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (2 ≤ count1513 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (1 ≤ count1516 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (2 ≤ count1516 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (1 ≤ count1518 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (2 ≤ count1518 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (1 ≤ count1520 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (2 ≤ count1520 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (3 ≤ count1520 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (1 ≤ count1524 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (2 ≤ count1524 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (3 ≤ count1524 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (4 ≤ count1524 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (1 ≤ count1531 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (2 ≤ count1531 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (1 ≤ count1533 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (2 ≤ count1533 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (1 ≤ count1535 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (2 ≤ count1535 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (3 ≤ count1535 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (1 ≤ count1539 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (2 ≤ count1539 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (1 ≤ count1541 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (2 ≤ count1541 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (1 ≤ count1543 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (2 ≤ count1543 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (3 ≤ count1543 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (1 ≤ count1547 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (2 ≤ count1547 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (3 ≤ count1547 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (4 ≤ count1547 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (2 ≤ count1555 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (3 ≤ count1555 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (4 ≤ count1555 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (5 ≤ count1555 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (6 ≤ count1555 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (6 ≤ count1570 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (7 ≤ count1570 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (8 ≤ count1570 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (9 ≤ count1570 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (10 ≤ count1570 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (11 ≤ count1570 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (1 ≤ count1589 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (2 ≤ count1589 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (1 ≤ count1591 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (2 ≤ count1591 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (3 ≤ count1591 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (1 ≤ count1594 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (2 ≤ count1594 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (1 ≤ count1596 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (1 ≤ count1598 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (2 ≤ count1598 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (3 ≤ count1598 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (1 ≤ count1602 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (2 ≤ count1602 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (3 ≤ count1602 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (4 ≤ count1602 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (5 ≤ count1602 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (1 ≤ count1609 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (2 ≤ count1609 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (1 ≤ count1611 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (2 ≤ count1611 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (1 ≤ count1613 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (2 ≤ count1613 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (3 ≤ count1613 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (1 ≤ count1617 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (2 ≤ count1617 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (1 ≤ count1619 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (2 ≤ count1619 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (1 ≤ count1621 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (2 ≤ count1621 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (3 ≤ count1621 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (4 ≤ count1621 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (1 ≤ count1625 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (2 ≤ count1625 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (3 ≤ count1625 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (4 ≤ count1625 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (2 ≤ count1633 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (3 ≤ count1633 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (4 ≤ count1633 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (5 ≤ count1633 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (6 ≤ count1633 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (7 ≤ count1633 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (8 ≤ count1633 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (1 ≤ count1648 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (2 ≤ count1648 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (1 ≤ count1650 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (2 ≤ count1650 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (3 ≤ count1650 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (1 ≤ count1653 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (2 ≤ count1653 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (1 ≤ count1655 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (2 ≤ count1655 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (1 ≤ count1657 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (2 ≤ count1657 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (3 ≤ count1657 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (4 ≤ count1657 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (1 ≤ count1661 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (2 ≤ count1661 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (3 ≤ count1661 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (4 ≤ count1661 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (1 ≤ count1668 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (2 ≤ count1668 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (1 ≤ count1670 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (2 ≤ count1670 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (1 ≤ count1672 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (2 ≤ count1672 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (3 ≤ count1672 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (4 ≤ count1672 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (1 ≤ count1676 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (2 ≤ count1676 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (1 ≤ count1678 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (2 ≤ count1678 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (1 ≤ count1680 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (2 ≤ count1680 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (3 ≤ count1680 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (4 ≤ count1680 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (1 ≤ count1684 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (2 ≤ count1684 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (3 ≤ count1684 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (4 ≤ count1684 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (5 ≤ count1684 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (6 ≤ count1684 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (7 ≤ count1684 b) := rfl
theorem meaning1694 (b : Nat → Bool) : literal (valuationOf b) 1694 = decide (3 ≤ count1692 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (4 ≤ count1692 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (5 ≤ count1692 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (6 ≤ count1692 b) := rfl
theorem meaning1698 (b : Nat → Bool) : literal (valuationOf b) 1698 = decide (7 ≤ count1692 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (8 ≤ count1692 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (9 ≤ count1692 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (10 ≤ count1692 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (8 ≤ count1707 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (9 ≤ count1707 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (10 ≤ count1707 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (11 ≤ count1707 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (12 ≤ count1707 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (13 ≤ count1707 b) := rfl
theorem meaning1744 (b : Nat → Bool) : literal (valuationOf b) 1744 = decide (19 ≤ count1726 b) := rfl
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
end Snake9.Regrowth.E112152
