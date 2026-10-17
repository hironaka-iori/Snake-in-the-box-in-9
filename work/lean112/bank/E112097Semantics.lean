import E112097Data
namespace Snake9.Regrowth.E112097
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 123 then (if i < 61 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (8 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (12 : Vertex)) else decide (InPath q (33 : Vertex))) else (if i < 6 then decide (InPath q (35 : Vertex)) else decide (InPath q (39 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (40 : Vertex)) else decide (InPath q (48 : Vertex))) else (if i < 10 then decide (InPath q (50 : Vertex)) else decide (InPath q (51 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (52 : Vertex)) else decide (InPath q (56 : Vertex))) else (if i < 14 then decide (InPath q (160 : Vertex)) else decide (InPath q (162 : Vertex)))))) else (if i < 22 then (if i < 18 then (if i < 16 then decide (InPath q (164 : Vertex)) else (if i < 17 then decide (InPath q (167 : Vertex)) else decide (InPath q (168 : Vertex)))) else (if i < 20 then (if i < 19 then decide (InPath q (170 : Vertex)) else decide (InPath q (171 : Vertex))) else (if i < 21 then decide (InPath q (172 : Vertex)) else decide (InPath q (177 : Vertex))))) else (if i < 26 then (if i < 24 then (if i < 23 then decide (InPath q (180 : Vertex)) else decide (InPath q (181 : Vertex))) else (if i < 25 then decide (InPath q (182 : Vertex)) else decide (InPath q (183 : Vertex)))) else (if i < 28 then (if i < 27 then decide (InPath q (185 : Vertex)) else decide (InPath q (186 : Vertex))) else (if i < 29 then decide (InPath q (187 : Vertex)) else decide (InPath q (225 : Vertex))))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then decide (InPath q (227 : Vertex)) else (if i < 32 then decide (InPath q (229 : Vertex)) else decide (InPath q (230 : Vertex)))) else (if i < 35 then (if i < 34 then decide (InPath q (231 : Vertex)) else decide (InPath q (232 : Vertex))) else (if i < 36 then decide (InPath q (233 : Vertex)) else decide (InPath q (238 : Vertex))))) else (if i < 41 then (if i < 39 then (if i < 38 then decide (InPath q (239 : Vertex)) else decide (InPath q (240 : Vertex))) else (if i < 40 then decide (InPath q (242 : Vertex)) else decide (InPath q (243 : Vertex)))) else (if i < 43 then (if i < 42 then decide (InPath q (244 : Vertex)) else decide (InPath q (248 : Vertex))) else (if i < 44 then decide (InPath q (250 : Vertex)) else decide (InPath q (252 : Vertex)))))) else (if i < 53 then (if i < 49 then (if i < 47 then (if i < 46 then decide (InPath q (253 : Vertex)) else decide (InPath q (255 : Vertex))) else (if i < 48 then decide (InPath q (288 : Vertex)) else decide (InPath q (290 : Vertex)))) else (if i < 51 then (if i < 50 then decide (InPath q (292 : Vertex)) else decide (InPath q (294 : Vertex))) else (if i < 52 then decide (InPath q (295 : Vertex)) else decide (InPath q (296 : Vertex))))) else (if i < 57 then (if i < 55 then (if i < 54 then decide (InPath q (297 : Vertex)) else decide (InPath q (298 : Vertex))) else (if i < 56 then decide (InPath q (300 : Vertex)) else decide (InPath q (302 : Vertex)))) else (if i < 59 then (if i < 58 then decide (InPath q (305 : Vertex)) else decide (InPath q (307 : Vertex))) else (if i < 60 then decide (InPath q (308 : Vertex)) else decide (InPath q (309 : Vertex)))))))) else (if i < 92 then (if i < 76 then (if i < 68 then (if i < 64 then (if i < 62 then decide (InPath q (311 : Vertex)) else (if i < 63 then decide (InPath q (313 : Vertex)) else decide (InPath q (314 : Vertex)))) else (if i < 66 then (if i < 65 then decide (InPath q (315 : Vertex)) else decide (InPath q (353 : Vertex))) else (if i < 67 then decide (InPath q (355 : Vertex)) else decide (InPath q (357 : Vertex))))) else (if i < 72 then (if i < 70 then (if i < 69 then decide (InPath q (358 : Vertex)) else decide (InPath q (359 : Vertex))) else (if i < 71 then decide (InPath q (360 : Vertex)) else decide (InPath q (361 : Vertex)))) else (if i < 74 then (if i < 73 then decide (InPath q (366 : Vertex)) else decide (InPath q (367 : Vertex))) else (if i < 75 then decide (InPath q (368 : Vertex)) else decide (InPath q (370 : Vertex)))))) else (if i < 84 then (if i < 80 then (if i < 78 then (if i < 77 then decide (InPath q (371 : Vertex)) else decide (InPath q (372 : Vertex))) else (if i < 79 then decide (InPath q (376 : Vertex)) else decide (InPath q (380 : Vertex)))) else (if i < 82 then (if i < 81 then decide (InPath q (381 : Vertex)) else decide (InPath q (383 : Vertex))) else (if i < 83 then decide (InPath q (417 : Vertex)) else decide (InPath q (419 : Vertex))))) else (if i < 88 then (if i < 86 then (if i < 85 then decide (InPath q (421 : Vertex)) else decide (InPath q (422 : Vertex))) else (if i < 87 then decide (InPath q (424 : Vertex)) else decide (InPath q (427 : Vertex)))) else (if i < 90 then (if i < 89 then decide (InPath q (428 : Vertex)) else decide (InPath q (430 : Vertex))) else (if i < 91 then decide (InPath q (431 : Vertex)) else decide (InPath q (432 : Vertex))))))) else (if i < 107 then (if i < 99 then (if i < 95 then (if i < 93 then decide (InPath q (433 : Vertex)) else (if i < 94 then decide (InPath q (434 : Vertex)) else decide (InPath q (435 : Vertex)))) else (if i < 97 then (if i < 96 then decide (InPath q (438 : Vertex)) else decide (InPath q (440 : Vertex))) else (if i < 98 then decide (InPath q (444 : Vertex)) else decide (InPath q (445 : Vertex))))) else (if i < 103 then (if i < 101 then (if i < 100 then decide (InPath q (446 : Vertex)) else decide (InPath q (447 : Vertex))) else (if i < 102 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex)))) else (if i < 105 then (if i < 104 then decide (InPath q (482 : Vertex)) else decide (InPath q (484 : Vertex))) else (if i < 106 then decide (InPath q (485 : Vertex)) else decide (InPath q (486 : Vertex)))))) else (if i < 115 then (if i < 111 then (if i < 109 then (if i < 108 then decide (InPath q (488 : Vertex)) else decide (InPath q (489 : Vertex))) else (if i < 110 then decide (InPath q (490 : Vertex)) else decide (InPath q (491 : Vertex)))) else (if i < 113 then (if i < 112 then decide (InPath q (492 : Vertex)) else decide (InPath q (494 : Vertex))) else (if i < 114 then decide (InPath q (495 : Vertex)) else decide (InPath q (497 : Vertex))))) else (if i < 119 then (if i < 117 then (if i < 116 then decide (InPath q (500 : Vertex)) else decide (InPath q (501 : Vertex))) else (if i < 118 then decide (InPath q (502 : Vertex)) else decide (InPath q (503 : Vertex)))) else (if i < 121 then (if i < 120 then decide (InPath q (505 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 122 then decide (InPath q (507 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 185 then (if i < 154 then (if i < 138 then (if i < 130 then (if i < 126 then (if i < 124 then decide (InPath q (511 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (8 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (12 : Vertex)) else decide (BallClauseLogic.Endpoint q (33 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (35 : Vertex)) else decide (BallClauseLogic.Endpoint q (39 : Vertex))))) else (if i < 134 then (if i < 132 then (if i < 131 then decide (BallClauseLogic.Endpoint q (40 : Vertex)) else decide (BallClauseLogic.Endpoint q (48 : Vertex))) else (if i < 133 then decide (BallClauseLogic.Endpoint q (50 : Vertex)) else decide (BallClauseLogic.Endpoint q (51 : Vertex)))) else (if i < 136 then (if i < 135 then decide (BallClauseLogic.Endpoint q (52 : Vertex)) else decide (BallClauseLogic.Endpoint q (56 : Vertex))) else (if i < 137 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (162 : Vertex)))))) else (if i < 146 then (if i < 142 then (if i < 140 then (if i < 139 then decide (BallClauseLogic.Endpoint q (164 : Vertex)) else decide (BallClauseLogic.Endpoint q (167 : Vertex))) else (if i < 141 then decide (BallClauseLogic.Endpoint q (168 : Vertex)) else decide (BallClauseLogic.Endpoint q (170 : Vertex)))) else (if i < 144 then (if i < 143 then decide (BallClauseLogic.Endpoint q (171 : Vertex)) else decide (BallClauseLogic.Endpoint q (172 : Vertex))) else (if i < 145 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (180 : Vertex))))) else (if i < 150 then (if i < 148 then (if i < 147 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))) else (if i < 149 then decide (BallClauseLogic.Endpoint q (183 : Vertex)) else decide (BallClauseLogic.Endpoint q (185 : Vertex)))) else (if i < 152 then (if i < 151 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (187 : Vertex))) else (if i < 153 then decide (BallClauseLogic.Endpoint q (225 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex))))))) else (if i < 169 then (if i < 161 then (if i < 157 then (if i < 155 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else (if i < 156 then decide (BallClauseLogic.Endpoint q (230 : Vertex)) else decide (BallClauseLogic.Endpoint q (231 : Vertex)))) else (if i < 159 then (if i < 158 then decide (BallClauseLogic.Endpoint q (232 : Vertex)) else decide (BallClauseLogic.Endpoint q (233 : Vertex))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else decide (BallClauseLogic.Endpoint q (239 : Vertex))))) else (if i < 165 then (if i < 163 then (if i < 162 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (242 : Vertex))) else (if i < 164 then decide (BallClauseLogic.Endpoint q (243 : Vertex)) else decide (BallClauseLogic.Endpoint q (244 : Vertex)))) else (if i < 167 then (if i < 166 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else decide (BallClauseLogic.Endpoint q (250 : Vertex))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (252 : Vertex)) else decide (BallClauseLogic.Endpoint q (253 : Vertex)))))) else (if i < 177 then (if i < 173 then (if i < 171 then (if i < 170 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else decide (BallClauseLogic.Endpoint q (288 : Vertex))) else (if i < 172 then decide (BallClauseLogic.Endpoint q (290 : Vertex)) else decide (BallClauseLogic.Endpoint q (292 : Vertex)))) else (if i < 175 then (if i < 174 then decide (BallClauseLogic.Endpoint q (294 : Vertex)) else decide (BallClauseLogic.Endpoint q (295 : Vertex))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else decide (BallClauseLogic.Endpoint q (297 : Vertex))))) else (if i < 181 then (if i < 179 then (if i < 178 then decide (BallClauseLogic.Endpoint q (298 : Vertex)) else decide (BallClauseLogic.Endpoint q (300 : Vertex))) else (if i < 180 then decide (BallClauseLogic.Endpoint q (302 : Vertex)) else decide (BallClauseLogic.Endpoint q (305 : Vertex)))) else (if i < 183 then (if i < 182 then decide (BallClauseLogic.Endpoint q (307 : Vertex)) else decide (BallClauseLogic.Endpoint q (308 : Vertex))) else (if i < 184 then decide (BallClauseLogic.Endpoint q (309 : Vertex)) else decide (BallClauseLogic.Endpoint q (311 : Vertex)))))))) else (if i < 216 then (if i < 200 then (if i < 192 then (if i < 188 then (if i < 186 then decide (BallClauseLogic.Endpoint q (313 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (314 : Vertex)) else decide (BallClauseLogic.Endpoint q (315 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (353 : Vertex)) else decide (BallClauseLogic.Endpoint q (355 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (358 : Vertex))))) else (if i < 196 then (if i < 194 then (if i < 193 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (360 : Vertex))) else (if i < 195 then decide (BallClauseLogic.Endpoint q (361 : Vertex)) else decide (BallClauseLogic.Endpoint q (366 : Vertex)))) else (if i < 198 then (if i < 197 then decide (BallClauseLogic.Endpoint q (367 : Vertex)) else decide (BallClauseLogic.Endpoint q (368 : Vertex))) else (if i < 199 then decide (BallClauseLogic.Endpoint q (370 : Vertex)) else decide (BallClauseLogic.Endpoint q (371 : Vertex)))))) else (if i < 208 then (if i < 204 then (if i < 202 then (if i < 201 then decide (BallClauseLogic.Endpoint q (372 : Vertex)) else decide (BallClauseLogic.Endpoint q (376 : Vertex))) else (if i < 203 then decide (BallClauseLogic.Endpoint q (380 : Vertex)) else decide (BallClauseLogic.Endpoint q (381 : Vertex)))) else (if i < 206 then (if i < 205 then decide (BallClauseLogic.Endpoint q (383 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex))) else (if i < 207 then decide (BallClauseLogic.Endpoint q (419 : Vertex)) else decide (BallClauseLogic.Endpoint q (421 : Vertex))))) else (if i < 212 then (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (422 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (427 : Vertex)) else decide (BallClauseLogic.Endpoint q (428 : Vertex)))) else (if i < 214 then (if i < 213 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (431 : Vertex))) else (if i < 215 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else decide (BallClauseLogic.Endpoint q (433 : Vertex))))))) else (if i < 231 then (if i < 223 then (if i < 219 then (if i < 217 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else (if i < 218 then decide (BallClauseLogic.Endpoint q (435 : Vertex)) else decide (BallClauseLogic.Endpoint q (438 : Vertex)))) else (if i < 221 then (if i < 220 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (444 : Vertex))) else (if i < 222 then decide (BallClauseLogic.Endpoint q (445 : Vertex)) else decide (BallClauseLogic.Endpoint q (446 : Vertex))))) else (if i < 227 then (if i < 225 then (if i < 224 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else decide (BallClauseLogic.Endpoint q (480 : Vertex))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (482 : Vertex)))) else (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (484 : Vertex)) else decide (BallClauseLogic.Endpoint q (485 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))))) else (if i < 239 then (if i < 235 then (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (490 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (492 : Vertex)))) else (if i < 237 then (if i < 236 then decide (BallClauseLogic.Endpoint q (494 : Vertex)) else decide (BallClauseLogic.Endpoint q (495 : Vertex))) else (if i < 238 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (500 : Vertex))))) else (if i < 243 then (if i < 241 then (if i < 240 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex))) else (if i < 242 then decide (BallClauseLogic.Endpoint q (503 : Vertex)) else decide (BallClauseLogic.Endpoint q (505 : Vertex)))) else (if i < 245 then (if i < 244 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (507 : Vertex))) else (if i < 246 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count247 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count249 (b : Nat → Bool) : Nat := countLit b [124, 125, 126]
def count251 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count253 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count283 (b : Nat → Bool) : Nat := countLit b [142, 144, 145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 144, 145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count291 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154]
def count299 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150, 151, 152, 153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [155, 156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count313 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165, 166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count343 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count349 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count351 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count367 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count375 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192]
def count379 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200]
def count395 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count397 (b : Nat → Bool) : Nat := countLit b [201, 202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count403 (b : Nat → Bool) : Nat := countLit b [204, 205, 206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204, 205, 206, 207]
def count407 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count411 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count417 (b : Nat → Bool) : Nat := countLit b [212, 213, 214, 215]
def count419 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211, 212, 213, 214, 215]
def count421 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
def count423 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]
def count425 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [216, 217, 218]
def count429 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [219, 220, 221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219, 220, 221, 222]
def count437 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count441 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226]
def count443 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count447 (b : Nat → Bool) : Nat := countLit b [227, 228, 229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230]
def count453 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [235, 236, 237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234, 235, 236, 237, 238]
def count467 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count471 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count475 (b : Nat → Bool) : Nat := countLit b [245, 246]
def count477 (b : Nat → Bool) : Nat := countLit b [243, 244, 245, 246]
def count479 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242, 243, 244, 245, 246]
def count481 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]
def count483 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]
def count485 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]
def count487 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246]
def count489 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count491 (b : Nat → Bool) : Nat := countLit b [1, 3, 4]
def count494 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count496 (b : Nat → Bool) : Nat := countLit b [8, 10]
def count498 (b : Nat → Bool) : Nat := countLit b [6, 7, 8, 10]
def count502 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 8, 10]
def count509 (b : Nat → Bool) : Nat := countLit b [13, 18]
def count511 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count513 (b : Nat → Bool) : Nat := countLit b [13, 18, 20, 21]
def count517 (b : Nat → Bool) : Nat := countLit b [22, 25]
def count519 (b : Nat → Bool) : Nat := countLit b [28, 29]
def count521 (b : Nat → Bool) : Nat := countLit b [22, 25, 28, 29]
def count525 (b : Nat → Bool) : Nat := countLit b [13, 18, 20, 21, 22, 25, 28, 29]
def count533 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 8, 10, 13, 18, 20, 21, 22, 25, 28, 29]
def count548 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count550 (b : Nat → Bool) : Nat := countLit b [33, 34, 36]
def count553 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count555 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count557 (b : Nat → Bool) : Nat := countLit b [38, 40, 43, 44]
def count561 (b : Nat → Bool) : Nat := countLit b [33, 34, 36, 38, 40, 43, 44]
def count568 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count570 (b : Nat → Bool) : Nat := countLit b [50, 53]
def count572 (b : Nat → Bool) : Nat := countLit b [46, 47, 50, 53]
def count576 (b : Nat → Bool) : Nat := countLit b [54, 55]
def count578 (b : Nat → Bool) : Nat := countLit b [57, 59]
def count580 (b : Nat → Bool) : Nat := countLit b [54, 55, 57, 59]
def count584 (b : Nat → Bool) : Nat := countLit b [46, 47, 50, 53, 54, 55, 57, 59]
def count592 (b : Nat → Bool) : Nat := countLit b [33, 34, 36, 38, 40, 43, 44, 46, 47, 50, 53, 54, 55, 57, 59]
def count607 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 8, 10, 13, 18, 20, 21, 22, 25, 28, 29, 33, 34, 36, 38, 40, 43, 44, 46, 47, 50, 53, 54, 55, 57, 59]
def count637 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count639 (b : Nat → Bool) : Nat := countLit b [61, 64, 65]
def count642 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count644 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count646 (b : Nat → Bool) : Nat := countLit b [69, 70, 72, 74]
def count650 (b : Nat → Bool) : Nat := countLit b [61, 64, 65, 69, 70, 72, 74]
def count657 (b : Nat → Bool) : Nat := countLit b [76, 79]
def count659 (b : Nat → Bool) : Nat := countLit b [81, 82]
def count661 (b : Nat → Bool) : Nat := countLit b [76, 79, 81, 82]
def count665 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count667 (b : Nat → Bool) : Nat := countLit b [89, 91]
def count669 (b : Nat → Bool) : Nat := countLit b [86, 87, 89, 91]
def count673 (b : Nat → Bool) : Nat := countLit b [76, 79, 81, 82, 86, 87, 89, 91]
def count681 (b : Nat → Bool) : Nat := countLit b [61, 64, 65, 69, 70, 72, 74, 76, 79, 81, 82, 86, 87, 89, 91]
def count696 (b : Nat → Bool) : Nat := countLit b [94, 95]
def count698 (b : Nat → Bool) : Nat := countLit b [97, 100]
def count700 (b : Nat → Bool) : Nat := countLit b [94, 95, 97, 100]
def count704 (b : Nat → Bool) : Nat := countLit b [101, 105]
def count706 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count708 (b : Nat → Bool) : Nat := countLit b [101, 105, 106, 108]
def count712 (b : Nat → Bool) : Nat := countLit b [94, 95, 97, 100, 101, 105, 106, 108]
def count720 (b : Nat → Bool) : Nat := countLit b [109, 111]
def count722 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count724 (b : Nat → Bool) : Nat := countLit b [109, 111, 113, 114]
def count728 (b : Nat → Bool) : Nat := countLit b [115, 118]
def count730 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count732 (b : Nat → Bool) : Nat := countLit b [115, 118, 121, 122]
def count736 (b : Nat → Bool) : Nat := countLit b [109, 111, 113, 114, 115, 118, 121, 122]
def count744 (b : Nat → Bool) : Nat := countLit b [94, 95, 97, 100, 101, 105, 106, 108, 109, 111, 113, 114, 115, 118, 121, 122]
def count760 (b : Nat → Bool) : Nat := countLit b [61, 64, 65, 69, 70, 72, 74, 76, 79, 81, 82, 86, 87, 89, 91, 94, 95, 97, 100, 101, 105, 106, 108, 109, 111, 113, 114, 115, 118, 121, 122]
def count791 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 8, 10, 13, 18, 20, 21, 22, 25, 28, 29, 33, 34, 36, 38, 40, 43, 44, 46, 47, 50, 53, 54, 55, 57, 59, 61, 64, 65, 69, 70, 72, 74, 76, 79, 81, 82, 86, 87, 89, 91, 94, 95, 97, 100, 101, 105, 106, 108, 109, 111, 113, 114, 115, 118, 121, 122]
def count833 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count835 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4]
def count838 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count840 (b : Nat → Bool) : Nat := countLit b [-8, -10]
def count842 (b : Nat → Bool) : Nat := countLit b [-6, -7, -8, -10]
def count846 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -8, -10]
def count853 (b : Nat → Bool) : Nat := countLit b [-13, -18]
def count855 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count857 (b : Nat → Bool) : Nat := countLit b [-13, -18, -20, -21]
def count861 (b : Nat → Bool) : Nat := countLit b [-22, -25]
def count863 (b : Nat → Bool) : Nat := countLit b [-28, -29]
def count865 (b : Nat → Bool) : Nat := countLit b [-22, -25, -28, -29]
def count869 (b : Nat → Bool) : Nat := countLit b [-13, -18, -20, -21, -22, -25, -28, -29]
def count877 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]
def count892 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count894 (b : Nat → Bool) : Nat := countLit b [-33, -34, -36]
def count897 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count899 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count901 (b : Nat → Bool) : Nat := countLit b [-38, -40, -43, -44]
def count905 (b : Nat → Bool) : Nat := countLit b [-33, -34, -36, -38, -40, -43, -44]
def count912 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count914 (b : Nat → Bool) : Nat := countLit b [-50, -53]
def count916 (b : Nat → Bool) : Nat := countLit b [-46, -47, -50, -53]
def count920 (b : Nat → Bool) : Nat := countLit b [-54, -55]
def count922 (b : Nat → Bool) : Nat := countLit b [-57, -59]
def count924 (b : Nat → Bool) : Nat := countLit b [-54, -55, -57, -59]
def count928 (b : Nat → Bool) : Nat := countLit b [-46, -47, -50, -53, -54, -55, -57, -59]
def count936 (b : Nat → Bool) : Nat := countLit b [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]
def count951 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]
def count972 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count974 (b : Nat → Bool) : Nat := countLit b [-61, -64, -65]
def count977 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count979 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count981 (b : Nat → Bool) : Nat := countLit b [-69, -70, -72, -74]
def count985 (b : Nat → Bool) : Nat := countLit b [-61, -64, -65, -69, -70, -72, -74]
def count992 (b : Nat → Bool) : Nat := countLit b [-76, -79]
def count994 (b : Nat → Bool) : Nat := countLit b [-81, -82]
def count996 (b : Nat → Bool) : Nat := countLit b [-76, -79, -81, -82]
def count1000 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count1002 (b : Nat → Bool) : Nat := countLit b [-89, -91]
def count1004 (b : Nat → Bool) : Nat := countLit b [-86, -87, -89, -91]
def count1008 (b : Nat → Bool) : Nat := countLit b [-76, -79, -81, -82, -86, -87, -89, -91]
def count1016 (b : Nat → Bool) : Nat := countLit b [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91]
def count1031 (b : Nat → Bool) : Nat := countLit b [-94, -95]
def count1033 (b : Nat → Bool) : Nat := countLit b [-97, -100]
def count1035 (b : Nat → Bool) : Nat := countLit b [-94, -95, -97, -100]
def count1039 (b : Nat → Bool) : Nat := countLit b [-101, -105]
def count1041 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count1043 (b : Nat → Bool) : Nat := countLit b [-101, -105, -106, -108]
def count1047 (b : Nat → Bool) : Nat := countLit b [-94, -95, -97, -100, -101, -105, -106, -108]
def count1055 (b : Nat → Bool) : Nat := countLit b [-109, -111]
def count1057 (b : Nat → Bool) : Nat := countLit b [-113, -114]
def count1059 (b : Nat → Bool) : Nat := countLit b [-109, -111, -113, -114]
def count1063 (b : Nat → Bool) : Nat := countLit b [-115, -118]
def count1065 (b : Nat → Bool) : Nat := countLit b [-121, -122]
def count1067 (b : Nat → Bool) : Nat := countLit b [-115, -118, -121, -122]
def count1071 (b : Nat → Bool) : Nat := countLit b [-109, -111, -113, -114, -115, -118, -121, -122]
def count1079 (b : Nat → Bool) : Nat := countLit b [-94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]
def count1095 (b : Nat → Bool) : Nat := countLit b [-61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]
def count1116 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29, -33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59, -61, -64, -65, -69, -70, -72, -74, -76, -79, -81, -82, -86, -87, -89, -91, -94, -95, -97, -100, -101, -105, -106, -108, -109, -111, -113, -114, -115, -118, -121, -122]
def count1137 (b : Nat → Bool) : Nat := countLit b [5, 9]
def count1139 (b : Nat → Bool) : Nat := countLit b [2, 5, 9]
def count1142 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count1144 (b : Nat → Bool) : Nat := countLit b [14, 15]
def count1146 (b : Nat → Bool) : Nat := countLit b [11, 12, 14, 15]
def count1150 (b : Nat → Bool) : Nat := countLit b [2, 5, 9, 11, 12, 14, 15]
def count1157 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count1159 (b : Nat → Bool) : Nat := countLit b [19, 23]
def count1161 (b : Nat → Bool) : Nat := countLit b [16, 17, 19, 23]
def count1165 (b : Nat → Bool) : Nat := countLit b [24, 26]
def count1167 (b : Nat → Bool) : Nat := countLit b [27, 30]
def count1169 (b : Nat → Bool) : Nat := countLit b [24, 26, 27, 30]
def count1173 (b : Nat → Bool) : Nat := countLit b [16, 17, 19, 23, 24, 26, 27, 30]
def count1181 (b : Nat → Bool) : Nat := countLit b [2, 5, 9, 11, 12, 14, 15, 16, 17, 19, 23, 24, 26, 27, 30]
def count1196 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count1198 (b : Nat → Bool) : Nat := countLit b [35, 37]
def count1200 (b : Nat → Bool) : Nat := countLit b [31, 32, 35, 37]
def count1204 (b : Nat → Bool) : Nat := countLit b [39, 41]
def count1206 (b : Nat → Bool) : Nat := countLit b [42, 45]
def count1208 (b : Nat → Bool) : Nat := countLit b [39, 41, 42, 45]
def count1212 (b : Nat → Bool) : Nat := countLit b [31, 32, 35, 37, 39, 41, 42, 45]
def count1220 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count1222 (b : Nat → Bool) : Nat := countLit b [51, 52]
def count1224 (b : Nat → Bool) : Nat := countLit b [48, 49, 51, 52]
def count1228 (b : Nat → Bool) : Nat := countLit b [56, 58]
def count1230 (b : Nat → Bool) : Nat := countLit b [60, 62]
def count1232 (b : Nat → Bool) : Nat := countLit b [56, 58, 60, 62]
def count1236 (b : Nat → Bool) : Nat := countLit b [48, 49, 51, 52, 56, 58, 60, 62]
def count1244 (b : Nat → Bool) : Nat := countLit b [31, 32, 35, 37, 39, 41, 42, 45, 48, 49, 51, 52, 56, 58, 60, 62]
def count1260 (b : Nat → Bool) : Nat := countLit b [2, 5, 9, 11, 12, 14, 15, 16, 17, 19, 23, 24, 26, 27, 30, 31, 32, 35, 37, 39, 41, 42, 45, 48, 49, 51, 52, 56, 58, 60, 62]
def count1291 (b : Nat → Bool) : Nat := countLit b [66, 67]
def count1293 (b : Nat → Bool) : Nat := countLit b [63, 66, 67]
def count1296 (b : Nat → Bool) : Nat := countLit b [68, 71]
def count1298 (b : Nat → Bool) : Nat := countLit b [73, 75]
def count1300 (b : Nat → Bool) : Nat := countLit b [68, 71, 73, 75]
def count1304 (b : Nat → Bool) : Nat := countLit b [63, 66, 67, 68, 71, 73, 75]
def count1311 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count1313 (b : Nat → Bool) : Nat := countLit b [80, 83]
def count1315 (b : Nat → Bool) : Nat := countLit b [77, 78, 80, 83]
def count1319 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count1321 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count1323 (b : Nat → Bool) : Nat := countLit b [84, 85, 88, 90]
def count1327 (b : Nat → Bool) : Nat := countLit b [77, 78, 80, 83, 84, 85, 88, 90]
def count1335 (b : Nat → Bool) : Nat := countLit b [63, 66, 67, 68, 71, 73, 75, 77, 78, 80, 83, 84, 85, 88, 90]
def count1350 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count1352 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count1354 (b : Nat → Bool) : Nat := countLit b [92, 93, 96, 98]
def count1358 (b : Nat → Bool) : Nat := countLit b [99, 102]
def count1360 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count1362 (b : Nat → Bool) : Nat := countLit b [99, 102, 103, 104]
def count1366 (b : Nat → Bool) : Nat := countLit b [92, 93, 96, 98, 99, 102, 103, 104]
def count1374 (b : Nat → Bool) : Nat := countLit b [107, 110]
def count1376 (b : Nat → Bool) : Nat := countLit b [112, 116]
def count1378 (b : Nat → Bool) : Nat := countLit b [107, 110, 112, 116]
def count1382 (b : Nat → Bool) : Nat := countLit b [117, 119]
def count1384 (b : Nat → Bool) : Nat := countLit b [120, 123]
def count1386 (b : Nat → Bool) : Nat := countLit b [117, 119, 120, 123]
def count1390 (b : Nat → Bool) : Nat := countLit b [107, 110, 112, 116, 117, 119, 120, 123]
def count1398 (b : Nat → Bool) : Nat := countLit b [92, 93, 96, 98, 99, 102, 103, 104, 107, 110, 112, 116, 117, 119, 120, 123]
def count1414 (b : Nat → Bool) : Nat := countLit b [63, 66, 67, 68, 71, 73, 75, 77, 78, 80, 83, 84, 85, 88, 90, 92, 93, 96, 98, 99, 102, 103, 104, 107, 110, 112, 116, 117, 119, 120, 123]
def count1445 (b : Nat → Bool) : Nat := countLit b [2, 5, 9, 11, 12, 14, 15, 16, 17, 19, 23, 24, 26, 27, 30, 31, 32, 35, 37, 39, 41, 42, 45, 48, 49, 51, 52, 56, 58, 60, 62, 63, 66, 67, 68, 71, 73, 75, 77, 78, 80, 83, 84, 85, 88, 90, 92, 93, 96, 98, 99, 102, 103, 104, 107, 110, 112, 116, 117, 119, 120, 123]
def count1487 (b : Nat → Bool) : Nat := countLit b [-5, -9]
def count1489 (b : Nat → Bool) : Nat := countLit b [-2, -5, -9]
def count1492 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count1494 (b : Nat → Bool) : Nat := countLit b [-14, -15]
def count1496 (b : Nat → Bool) : Nat := countLit b [-11, -12, -14, -15]
def count1500 (b : Nat → Bool) : Nat := countLit b [-2, -5, -9, -11, -12, -14, -15]
def count1507 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count1509 (b : Nat → Bool) : Nat := countLit b [-19, -23]
def count1511 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19, -23]
def count1515 (b : Nat → Bool) : Nat := countLit b [-24, -26]
def count1517 (b : Nat → Bool) : Nat := countLit b [-27, -30]
def count1519 (b : Nat → Bool) : Nat := countLit b [-24, -26, -27, -30]
def count1523 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19, -23, -24, -26, -27, -30]
def count1531 (b : Nat → Bool) : Nat := countLit b [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30]
def count1546 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count1548 (b : Nat → Bool) : Nat := countLit b [-35, -37]
def count1550 (b : Nat → Bool) : Nat := countLit b [-31, -32, -35, -37]
def count1554 (b : Nat → Bool) : Nat := countLit b [-39, -41]
def count1556 (b : Nat → Bool) : Nat := countLit b [-42, -45]
def count1558 (b : Nat → Bool) : Nat := countLit b [-39, -41, -42, -45]
def count1562 (b : Nat → Bool) : Nat := countLit b [-31, -32, -35, -37, -39, -41, -42, -45]
def count1570 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count1572 (b : Nat → Bool) : Nat := countLit b [-51, -52]
def count1574 (b : Nat → Bool) : Nat := countLit b [-48, -49, -51, -52]
def count1578 (b : Nat → Bool) : Nat := countLit b [-56, -58]
def count1580 (b : Nat → Bool) : Nat := countLit b [-60, -62]
def count1582 (b : Nat → Bool) : Nat := countLit b [-56, -58, -60, -62]
def count1586 (b : Nat → Bool) : Nat := countLit b [-48, -49, -51, -52, -56, -58, -60, -62]
def count1594 (b : Nat → Bool) : Nat := countLit b [-31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62]
def count1610 (b : Nat → Bool) : Nat := countLit b [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30, -31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62]
def count1632 (b : Nat → Bool) : Nat := countLit b [-66, -67]
def count1634 (b : Nat → Bool) : Nat := countLit b [-63, -66, -67]
def count1637 (b : Nat → Bool) : Nat := countLit b [-68, -71]
def count1639 (b : Nat → Bool) : Nat := countLit b [-73, -75]
def count1641 (b : Nat → Bool) : Nat := countLit b [-68, -71, -73, -75]
def count1645 (b : Nat → Bool) : Nat := countLit b [-63, -66, -67, -68, -71, -73, -75]
def count1652 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count1654 (b : Nat → Bool) : Nat := countLit b [-80, -83]
def count1656 (b : Nat → Bool) : Nat := countLit b [-77, -78, -80, -83]
def count1660 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count1662 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count1664 (b : Nat → Bool) : Nat := countLit b [-84, -85, -88, -90]
def count1668 (b : Nat → Bool) : Nat := countLit b [-77, -78, -80, -83, -84, -85, -88, -90]
def count1676 (b : Nat → Bool) : Nat := countLit b [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90]
def count1691 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1693 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count1695 (b : Nat → Bool) : Nat := countLit b [-92, -93, -96, -98]
def count1699 (b : Nat → Bool) : Nat := countLit b [-99, -102]
def count1701 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1703 (b : Nat → Bool) : Nat := countLit b [-99, -102, -103, -104]
def count1707 (b : Nat → Bool) : Nat := countLit b [-92, -93, -96, -98, -99, -102, -103, -104]
def count1715 (b : Nat → Bool) : Nat := countLit b [-107, -110]
def count1717 (b : Nat → Bool) : Nat := countLit b [-112, -116]
def count1719 (b : Nat → Bool) : Nat := countLit b [-107, -110, -112, -116]
def count1723 (b : Nat → Bool) : Nat := countLit b [-117, -119]
def count1725 (b : Nat → Bool) : Nat := countLit b [-120, -123]
def count1727 (b : Nat → Bool) : Nat := countLit b [-117, -119, -120, -123]
def count1731 (b : Nat → Bool) : Nat := countLit b [-107, -110, -112, -116, -117, -119, -120, -123]
def count1739 (b : Nat → Bool) : Nat := countLit b [-92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]
def count1755 (b : Nat → Bool) : Nat := countLit b [-63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90, -92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]
def count1777 (b : Nat → Bool) : Nat := countLit b [-2, -5, -9, -11, -12, -14, -15, -16, -17, -19, -23, -24, -26, -27, -30, -31, -32, -35, -37, -39, -41, -42, -45, -48, -49, -51, -52, -56, -58, -60, -62, -63, -66, -67, -68, -71, -73, -75, -77, -78, -80, -83, -84, -85, -88, -90, -92, -93, -96, -98, -99, -102, -103, -104, -107, -110, -112, -116, -117, -119, -120, -123]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 899 then (if i < 449 then (if i < 224 then (if i < 112 then (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 24 then (if i < 22 then b 21 else (if i < 23 then b 22 else b 23)) else (if i < 26 then (if i < 25 then b 24 else b 25) else (if i < 27 then b 26 else b 27))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 33 then (if i < 32 then b 31 else b 32) else (if i < 34 then b 33 else b 34))) else (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 40 then (if i < 39 then b 38 else b 39) else (if i < 41 then b 40 else b 41)))) else (if i < 49 then (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else b 48))) else (if i < 52 then (if i < 50 then b 49 else (if i < 51 then b 50 else b 51)) else (if i < 54 then (if i < 53 then b 52 else b 53) else (if i < 55 then b 54 else b 55)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then b 56 else (if i < 58 then b 57 else b 58)) else (if i < 61 then (if i < 60 then b 59 else b 60) else (if i < 62 then b 61 else b 62))) else (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 68 then (if i < 67 then b 66 else b 67) else (if i < 69 then b 68 else b 69)))) else (if i < 77 then (if i < 73 then (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)) else (if i < 75 then (if i < 74 then b 73 else b 74) else (if i < 76 then b 75 else b 76))) else (if i < 80 then (if i < 78 then b 77 else (if i < 79 then b 78 else b 79)) else (if i < 82 then (if i < 81 then b 80 else b 81) else (if i < 83 then b 82 else b 83))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90))) else (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else b 97)))) else (if i < 105 then (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else b 104))) else (if i < 108 then (if i < 106 then b 105 else (if i < 107 then b 106 else b 107)) else (if i < 110 then (if i < 109 then b 108 else b 109) else (if i < 111 then b 110 else b 111))))))) else (if i < 168 then (if i < 140 then (if i < 126 then (if i < 119 then (if i < 115 then (if i < 113 then b 112 else (if i < 114 then b 113 else b 114)) else (if i < 117 then (if i < 116 then b 115 else b 116) else (if i < 118 then b 117 else b 118))) else (if i < 122 then (if i < 120 then b 119 else (if i < 121 then b 120 else b 121)) else (if i < 124 then (if i < 123 then b 122 else b 123) else (if i < 125 then b 124 else b 125)))) else (if i < 133 then (if i < 129 then (if i < 127 then b 126 else (if i < 128 then b 127 else b 128)) else (if i < 131 then (if i < 130 then b 129 else b 130) else (if i < 132 then b 131 else b 132))) else (if i < 136 then (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)) else (if i < 138 then (if i < 137 then b 136 else b 137) else (if i < 139 then b 138 else b 139))))) else (if i < 154 then (if i < 147 then (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 145 then (if i < 144 then b 143 else b 144) else (if i < 146 then b 145 else b 146))) else (if i < 150 then (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)) else (if i < 152 then (if i < 151 then b 150 else b 151) else (if i < 153 then b 152 else b 153)))) else (if i < 161 then (if i < 157 then (if i < 155 then b 154 else (if i < 156 then b 155 else b 156)) else (if i < 159 then (if i < 158 then b 157 else b 158) else (if i < 160 then b 159 else b 160))) else (if i < 164 then (if i < 162 then b 161 else (if i < 163 then b 162 else b 163)) else (if i < 166 then (if i < 165 then b 164 else b 165) else (if i < 167 then b 166 else b 167)))))) else (if i < 196 then (if i < 182 then (if i < 175 then (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 173 then (if i < 172 then b 171 else b 172) else (if i < 174 then b 173 else b 174))) else (if i < 178 then (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)) else (if i < 180 then (if i < 179 then b 178 else b 179) else (if i < 181 then b 180 else b 181)))) else (if i < 189 then (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 187 then (if i < 186 then b 185 else b 186) else (if i < 188 then b 187 else b 188))) else (if i < 192 then (if i < 190 then b 189 else (if i < 191 then b 190 else b 191)) else (if i < 194 then (if i < 193 then b 192 else b 193) else (if i < 195 then b 194 else b 195))))) else (if i < 210 then (if i < 203 then (if i < 199 then (if i < 197 then b 196 else (if i < 198 then b 197 else b 198)) else (if i < 201 then (if i < 200 then b 199 else b 200) else (if i < 202 then b 201 else b 202))) else (if i < 206 then (if i < 204 then b 203 else (if i < 205 then b 204 else b 205)) else (if i < 208 then (if i < 207 then b 206 else b 207) else (if i < 209 then b 208 else b 209)))) else (if i < 217 then (if i < 213 then (if i < 211 then b 210 else (if i < 212 then b 211 else b 212)) else (if i < 215 then (if i < 214 then b 213 else b 214) else (if i < 216 then b 215 else b 216))) else (if i < 220 then (if i < 218 then b 217 else (if i < 219 then b 218 else b 219)) else (if i < 222 then (if i < 221 then b 220 else b 221) else (if i < 223 then b 222 else b 223)))))))) else (if i < 336 then (if i < 280 then (if i < 252 then (if i < 238 then (if i < 231 then (if i < 227 then (if i < 225 then b 224 else (if i < 226 then b 225 else b 226)) else (if i < 229 then (if i < 228 then b 227 else b 228) else (if i < 230 then b 229 else b 230))) else (if i < 234 then (if i < 232 then b 231 else (if i < 233 then b 232 else b 233)) else (if i < 236 then (if i < 235 then b 234 else b 235) else (if i < 237 then b 236 else b 237)))) else (if i < 245 then (if i < 241 then (if i < 239 then b 238 else (if i < 240 then b 239 else b 240)) else (if i < 243 then (if i < 242 then b 241 else b 242) else (if i < 244 then b 243 else b 244))) else (if i < 248 then (if i < 246 then b 245 else (if i < 247 then b 246 else decide (1 ≤ count247 b))) else (if i < 250 then (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b)) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)))))) else (if i < 266 then (if i < 259 then (if i < 255 then (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))) else (if i < 257 then (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b)) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)))) else (if i < 262 then (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))) else (if i < 264 then (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)) else (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b))))) else (if i < 273 then (if i < 269 then (if i < 267 then decide (2 ≤ count265 b) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b))) else (if i < 271 then (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)))) else (if i < 276 then (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 278 then (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))))))) else (if i < 308 then (if i < 294 then (if i < 287 then (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))) else (if i < 290 then (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))) else (if i < 292 then (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b))))) else (if i < 301 then (if i < 297 then (if i < 295 then decide (2 ≤ count293 b) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b))) else (if i < 299 then (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b)))) else (if i < 304 then (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))) else (if i < 306 then (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b)))))) else (if i < 322 then (if i < 315 then (if i < 311 then (if i < 309 then decide (2 ≤ count307 b) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b))) else (if i < 313 then (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b)))) else (if i < 318 then (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b))) else (if i < 320 then (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))))) else (if i < 329 then (if i < 325 then (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))) else (if i < 327 then (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)))) else (if i < 332 then (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))) else (if i < 334 then (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b)))))))) else (if i < 392 then (if i < 364 then (if i < 350 then (if i < 343 then (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))) else (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))))) else (if i < 357 then (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 355 then (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)))) else (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 362 then (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)))))) else (if i < 378 then (if i < 371 then (if i < 367 then (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))) else (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 376 then (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))))) else (if i < 385 then (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 383 then (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)))) else (if i < 388 then (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b))) else (if i < 390 then (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b)) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))))))) else (if i < 420 then (if i < 406 then (if i < 399 then (if i < 395 then (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b))) else (if i < 397 then (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b)))) else (if i < 402 then (if i < 400 then decide (1 ≤ count399 b) else (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b))) else (if i < 404 then (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))))) else (if i < 413 then (if i < 409 then (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 411 then (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)))) else (if i < 416 then (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b))) else (if i < 418 then (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)))))) else (if i < 434 then (if i < 427 then (if i < 423 then (if i < 421 then decide (2 ≤ count419 b) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b))) else (if i < 425 then (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b)) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)))) else (if i < 430 then (if i < 428 then decide (1 ≤ count427 b) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 432 then (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))))) else (if i < 441 then (if i < 437 then (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b))) else (if i < 439 then (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b)) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b)))) else (if i < 445 then (if i < 443 then (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b)) else (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b))) else (if i < 447 then (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b)) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b)))))))))) else (if i < 674 then (if i < 561 then (if i < 505 then (if i < 477 then (if i < 463 then (if i < 456 then (if i < 452 then (if i < 450 then decide (1 ≤ count449 b) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b))) else (if i < 454 then (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b)) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b)))) else (if i < 459 then (if i < 457 then decide (2 ≤ count455 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b))) else (if i < 461 then (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b))))) else (if i < 470 then (if i < 466 then (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b))) else (if i < 468 then (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b)) else (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b)))) else (if i < 473 then (if i < 471 then decide (2 ≤ count469 b) else (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b))) else (if i < 475 then (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)) else (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b)))))) else (if i < 491 then (if i < 484 then (if i < 480 then (if i < 478 then decide (1 ≤ count477 b) else (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b))) else (if i < 482 then (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b)) else (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b)))) else (if i < 487 then (if i < 485 then decide (2 ≤ count483 b) else (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b))) else (if i < 489 then (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b)) else (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b))))) else (if i < 498 then (if i < 494 then (if i < 492 then decide (1 ≤ count491 b) else (if i < 493 then decide (2 ≤ count491 b) else decide (3 ≤ count491 b))) else (if i < 496 then (if i < 495 then decide (1 ≤ count494 b) else decide (2 ≤ count494 b)) else (if i < 497 then decide (1 ≤ count496 b) else decide (2 ≤ count496 b)))) else (if i < 501 then (if i < 499 then decide (1 ≤ count498 b) else (if i < 500 then decide (2 ≤ count498 b) else decide (3 ≤ count498 b))) else (if i < 503 then (if i < 502 then decide (4 ≤ count498 b) else decide (1 ≤ count502 b)) else (if i < 504 then decide (2 ≤ count502 b) else decide (3 ≤ count502 b))))))) else (if i < 533 then (if i < 519 then (if i < 512 then (if i < 508 then (if i < 506 then decide (4 ≤ count502 b) else (if i < 507 then decide (5 ≤ count502 b) else decide (6 ≤ count502 b))) else (if i < 510 then (if i < 509 then decide (7 ≤ count502 b) else decide (1 ≤ count509 b)) else (if i < 511 then decide (2 ≤ count509 b) else decide (1 ≤ count511 b)))) else (if i < 515 then (if i < 513 then decide (2 ≤ count511 b) else (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b))) else (if i < 517 then (if i < 516 then decide (3 ≤ count513 b) else decide (4 ≤ count513 b)) else (if i < 518 then decide (1 ≤ count517 b) else decide (2 ≤ count517 b))))) else (if i < 526 then (if i < 522 then (if i < 520 then decide (1 ≤ count519 b) else (if i < 521 then decide (2 ≤ count519 b) else decide (1 ≤ count521 b))) else (if i < 524 then (if i < 523 then decide (2 ≤ count521 b) else decide (3 ≤ count521 b)) else (if i < 525 then decide (4 ≤ count521 b) else decide (1 ≤ count525 b)))) else (if i < 529 then (if i < 527 then decide (2 ≤ count525 b) else (if i < 528 then decide (3 ≤ count525 b) else decide (4 ≤ count525 b))) else (if i < 531 then (if i < 530 then decide (5 ≤ count525 b) else decide (6 ≤ count525 b)) else (if i < 532 then decide (7 ≤ count525 b) else decide (8 ≤ count525 b)))))) else (if i < 547 then (if i < 540 then (if i < 536 then (if i < 534 then decide (1 ≤ count533 b) else (if i < 535 then decide (2 ≤ count533 b) else decide (3 ≤ count533 b))) else (if i < 538 then (if i < 537 then decide (4 ≤ count533 b) else decide (5 ≤ count533 b)) else (if i < 539 then decide (6 ≤ count533 b) else decide (7 ≤ count533 b)))) else (if i < 543 then (if i < 541 then decide (8 ≤ count533 b) else (if i < 542 then decide (9 ≤ count533 b) else decide (10 ≤ count533 b))) else (if i < 545 then (if i < 544 then decide (11 ≤ count533 b) else decide (12 ≤ count533 b)) else (if i < 546 then decide (13 ≤ count533 b) else decide (14 ≤ count533 b))))) else (if i < 554 then (if i < 550 then (if i < 548 then decide (15 ≤ count533 b) else (if i < 549 then decide (1 ≤ count548 b) else decide (2 ≤ count548 b))) else (if i < 552 then (if i < 551 then decide (1 ≤ count550 b) else decide (2 ≤ count550 b)) else (if i < 553 then decide (3 ≤ count550 b) else decide (1 ≤ count553 b)))) else (if i < 557 then (if i < 555 then decide (2 ≤ count553 b) else (if i < 556 then decide (1 ≤ count555 b) else decide (2 ≤ count555 b))) else (if i < 559 then (if i < 558 then decide (1 ≤ count557 b) else decide (2 ≤ count557 b)) else (if i < 560 then decide (3 ≤ count557 b) else decide (4 ≤ count557 b)))))))) else (if i < 617 then (if i < 589 then (if i < 575 then (if i < 568 then (if i < 564 then (if i < 562 then decide (1 ≤ count561 b) else (if i < 563 then decide (2 ≤ count561 b) else decide (3 ≤ count561 b))) else (if i < 566 then (if i < 565 then decide (4 ≤ count561 b) else decide (5 ≤ count561 b)) else (if i < 567 then decide (6 ≤ count561 b) else decide (7 ≤ count561 b)))) else (if i < 571 then (if i < 569 then decide (1 ≤ count568 b) else (if i < 570 then decide (2 ≤ count568 b) else decide (1 ≤ count570 b))) else (if i < 573 then (if i < 572 then decide (2 ≤ count570 b) else decide (1 ≤ count572 b)) else (if i < 574 then decide (2 ≤ count572 b) else decide (3 ≤ count572 b))))) else (if i < 582 then (if i < 578 then (if i < 576 then decide (4 ≤ count572 b) else (if i < 577 then decide (1 ≤ count576 b) else decide (2 ≤ count576 b))) else (if i < 580 then (if i < 579 then decide (1 ≤ count578 b) else decide (2 ≤ count578 b)) else (if i < 581 then decide (1 ≤ count580 b) else decide (2 ≤ count580 b)))) else (if i < 585 then (if i < 583 then decide (3 ≤ count580 b) else (if i < 584 then decide (4 ≤ count580 b) else decide (1 ≤ count584 b))) else (if i < 587 then (if i < 586 then decide (2 ≤ count584 b) else decide (3 ≤ count584 b)) else (if i < 588 then decide (4 ≤ count584 b) else decide (5 ≤ count584 b)))))) else (if i < 603 then (if i < 596 then (if i < 592 then (if i < 590 then decide (6 ≤ count584 b) else (if i < 591 then decide (7 ≤ count584 b) else decide (8 ≤ count584 b))) else (if i < 594 then (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b)) else (if i < 595 then decide (3 ≤ count592 b) else decide (4 ≤ count592 b)))) else (if i < 599 then (if i < 597 then decide (5 ≤ count592 b) else (if i < 598 then decide (6 ≤ count592 b) else decide (7 ≤ count592 b))) else (if i < 601 then (if i < 600 then decide (8 ≤ count592 b) else decide (9 ≤ count592 b)) else (if i < 602 then decide (10 ≤ count592 b) else decide (11 ≤ count592 b))))) else (if i < 610 then (if i < 606 then (if i < 604 then decide (12 ≤ count592 b) else (if i < 605 then decide (13 ≤ count592 b) else decide (14 ≤ count592 b))) else (if i < 608 then (if i < 607 then decide (15 ≤ count592 b) else decide (1 ≤ count607 b)) else (if i < 609 then decide (2 ≤ count607 b) else decide (3 ≤ count607 b)))) else (if i < 613 then (if i < 611 then decide (4 ≤ count607 b) else (if i < 612 then decide (5 ≤ count607 b) else decide (6 ≤ count607 b))) else (if i < 615 then (if i < 614 then decide (7 ≤ count607 b) else decide (8 ≤ count607 b)) else (if i < 616 then decide (9 ≤ count607 b) else decide (10 ≤ count607 b))))))) else (if i < 645 then (if i < 631 then (if i < 624 then (if i < 620 then (if i < 618 then decide (11 ≤ count607 b) else (if i < 619 then decide (12 ≤ count607 b) else decide (13 ≤ count607 b))) else (if i < 622 then (if i < 621 then decide (14 ≤ count607 b) else decide (15 ≤ count607 b)) else (if i < 623 then decide (16 ≤ count607 b) else decide (17 ≤ count607 b)))) else (if i < 627 then (if i < 625 then decide (18 ≤ count607 b) else (if i < 626 then decide (19 ≤ count607 b) else decide (20 ≤ count607 b))) else (if i < 629 then (if i < 628 then decide (21 ≤ count607 b) else decide (22 ≤ count607 b)) else (if i < 630 then decide (23 ≤ count607 b) else decide (24 ≤ count607 b))))) else (if i < 638 then (if i < 634 then (if i < 632 then decide (25 ≤ count607 b) else (if i < 633 then decide (26 ≤ count607 b) else decide (27 ≤ count607 b))) else (if i < 636 then (if i < 635 then decide (28 ≤ count607 b) else decide (29 ≤ count607 b)) else (if i < 637 then decide (30 ≤ count607 b) else decide (1 ≤ count637 b)))) else (if i < 641 then (if i < 639 then decide (2 ≤ count637 b) else (if i < 640 then decide (1 ≤ count639 b) else decide (2 ≤ count639 b))) else (if i < 643 then (if i < 642 then decide (3 ≤ count639 b) else decide (1 ≤ count642 b)) else (if i < 644 then decide (2 ≤ count642 b) else decide (1 ≤ count644 b)))))) else (if i < 659 then (if i < 652 then (if i < 648 then (if i < 646 then decide (2 ≤ count644 b) else (if i < 647 then decide (1 ≤ count646 b) else decide (2 ≤ count646 b))) else (if i < 650 then (if i < 649 then decide (3 ≤ count646 b) else decide (4 ≤ count646 b)) else (if i < 651 then decide (1 ≤ count650 b) else decide (2 ≤ count650 b)))) else (if i < 655 then (if i < 653 then decide (3 ≤ count650 b) else (if i < 654 then decide (4 ≤ count650 b) else decide (5 ≤ count650 b))) else (if i < 657 then (if i < 656 then decide (6 ≤ count650 b) else decide (7 ≤ count650 b)) else (if i < 658 then decide (1 ≤ count657 b) else decide (2 ≤ count657 b))))) else (if i < 666 then (if i < 662 then (if i < 660 then decide (1 ≤ count659 b) else (if i < 661 then decide (2 ≤ count659 b) else decide (1 ≤ count661 b))) else (if i < 664 then (if i < 663 then decide (2 ≤ count661 b) else decide (3 ≤ count661 b)) else (if i < 665 then decide (4 ≤ count661 b) else decide (1 ≤ count665 b)))) else (if i < 670 then (if i < 668 then (if i < 667 then decide (2 ≤ count665 b) else decide (1 ≤ count667 b)) else (if i < 669 then decide (2 ≤ count667 b) else decide (1 ≤ count669 b))) else (if i < 672 then (if i < 671 then decide (2 ≤ count669 b) else decide (3 ≤ count669 b)) else (if i < 673 then decide (4 ≤ count669 b) else decide (1 ≤ count673 b))))))))) else (if i < 786 then (if i < 730 then (if i < 702 then (if i < 688 then (if i < 681 then (if i < 677 then (if i < 675 then decide (2 ≤ count673 b) else (if i < 676 then decide (3 ≤ count673 b) else decide (4 ≤ count673 b))) else (if i < 679 then (if i < 678 then decide (5 ≤ count673 b) else decide (6 ≤ count673 b)) else (if i < 680 then decide (7 ≤ count673 b) else decide (8 ≤ count673 b)))) else (if i < 684 then (if i < 682 then decide (1 ≤ count681 b) else (if i < 683 then decide (2 ≤ count681 b) else decide (3 ≤ count681 b))) else (if i < 686 then (if i < 685 then decide (4 ≤ count681 b) else decide (5 ≤ count681 b)) else (if i < 687 then decide (6 ≤ count681 b) else decide (7 ≤ count681 b))))) else (if i < 695 then (if i < 691 then (if i < 689 then decide (8 ≤ count681 b) else (if i < 690 then decide (9 ≤ count681 b) else decide (10 ≤ count681 b))) else (if i < 693 then (if i < 692 then decide (11 ≤ count681 b) else decide (12 ≤ count681 b)) else (if i < 694 then decide (13 ≤ count681 b) else decide (14 ≤ count681 b)))) else (if i < 698 then (if i < 696 then decide (15 ≤ count681 b) else (if i < 697 then decide (1 ≤ count696 b) else decide (2 ≤ count696 b))) else (if i < 700 then (if i < 699 then decide (1 ≤ count698 b) else decide (2 ≤ count698 b)) else (if i < 701 then decide (1 ≤ count700 b) else decide (2 ≤ count700 b)))))) else (if i < 716 then (if i < 709 then (if i < 705 then (if i < 703 then decide (3 ≤ count700 b) else (if i < 704 then decide (4 ≤ count700 b) else decide (1 ≤ count704 b))) else (if i < 707 then (if i < 706 then decide (2 ≤ count704 b) else decide (1 ≤ count706 b)) else (if i < 708 then decide (2 ≤ count706 b) else decide (1 ≤ count708 b)))) else (if i < 712 then (if i < 710 then decide (2 ≤ count708 b) else (if i < 711 then decide (3 ≤ count708 b) else decide (4 ≤ count708 b))) else (if i < 714 then (if i < 713 then decide (1 ≤ count712 b) else decide (2 ≤ count712 b)) else (if i < 715 then decide (3 ≤ count712 b) else decide (4 ≤ count712 b))))) else (if i < 723 then (if i < 719 then (if i < 717 then decide (5 ≤ count712 b) else (if i < 718 then decide (6 ≤ count712 b) else decide (7 ≤ count712 b))) else (if i < 721 then (if i < 720 then decide (8 ≤ count712 b) else decide (1 ≤ count720 b)) else (if i < 722 then decide (2 ≤ count720 b) else decide (1 ≤ count722 b)))) else (if i < 726 then (if i < 724 then decide (2 ≤ count722 b) else (if i < 725 then decide (1 ≤ count724 b) else decide (2 ≤ count724 b))) else (if i < 728 then (if i < 727 then decide (3 ≤ count724 b) else decide (4 ≤ count724 b)) else (if i < 729 then decide (1 ≤ count728 b) else decide (2 ≤ count728 b))))))) else (if i < 758 then (if i < 744 then (if i < 737 then (if i < 733 then (if i < 731 then decide (1 ≤ count730 b) else (if i < 732 then decide (2 ≤ count730 b) else decide (1 ≤ count732 b))) else (if i < 735 then (if i < 734 then decide (2 ≤ count732 b) else decide (3 ≤ count732 b)) else (if i < 736 then decide (4 ≤ count732 b) else decide (1 ≤ count736 b)))) else (if i < 740 then (if i < 738 then decide (2 ≤ count736 b) else (if i < 739 then decide (3 ≤ count736 b) else decide (4 ≤ count736 b))) else (if i < 742 then (if i < 741 then decide (5 ≤ count736 b) else decide (6 ≤ count736 b)) else (if i < 743 then decide (7 ≤ count736 b) else decide (8 ≤ count736 b))))) else (if i < 751 then (if i < 747 then (if i < 745 then decide (1 ≤ count744 b) else (if i < 746 then decide (2 ≤ count744 b) else decide (3 ≤ count744 b))) else (if i < 749 then (if i < 748 then decide (4 ≤ count744 b) else decide (5 ≤ count744 b)) else (if i < 750 then decide (6 ≤ count744 b) else decide (7 ≤ count744 b)))) else (if i < 754 then (if i < 752 then decide (8 ≤ count744 b) else (if i < 753 then decide (9 ≤ count744 b) else decide (10 ≤ count744 b))) else (if i < 756 then (if i < 755 then decide (11 ≤ count744 b) else decide (12 ≤ count744 b)) else (if i < 757 then decide (13 ≤ count744 b) else decide (14 ≤ count744 b)))))) else (if i < 772 then (if i < 765 then (if i < 761 then (if i < 759 then decide (15 ≤ count744 b) else (if i < 760 then decide (16 ≤ count744 b) else decide (1 ≤ count760 b))) else (if i < 763 then (if i < 762 then decide (2 ≤ count760 b) else decide (3 ≤ count760 b)) else (if i < 764 then decide (4 ≤ count760 b) else decide (5 ≤ count760 b)))) else (if i < 768 then (if i < 766 then decide (6 ≤ count760 b) else (if i < 767 then decide (7 ≤ count760 b) else decide (8 ≤ count760 b))) else (if i < 770 then (if i < 769 then decide (9 ≤ count760 b) else decide (10 ≤ count760 b)) else (if i < 771 then decide (11 ≤ count760 b) else decide (12 ≤ count760 b))))) else (if i < 779 then (if i < 775 then (if i < 773 then decide (13 ≤ count760 b) else (if i < 774 then decide (14 ≤ count760 b) else decide (15 ≤ count760 b))) else (if i < 777 then (if i < 776 then decide (16 ≤ count760 b) else decide (17 ≤ count760 b)) else (if i < 778 then decide (18 ≤ count760 b) else decide (19 ≤ count760 b)))) else (if i < 782 then (if i < 780 then decide (20 ≤ count760 b) else (if i < 781 then decide (21 ≤ count760 b) else decide (22 ≤ count760 b))) else (if i < 784 then (if i < 783 then decide (23 ≤ count760 b) else decide (24 ≤ count760 b)) else (if i < 785 then decide (25 ≤ count760 b) else decide (26 ≤ count760 b)))))))) else (if i < 842 then (if i < 814 then (if i < 800 then (if i < 793 then (if i < 789 then (if i < 787 then decide (27 ≤ count760 b) else (if i < 788 then decide (28 ≤ count760 b) else decide (29 ≤ count760 b))) else (if i < 791 then (if i < 790 then decide (30 ≤ count760 b) else decide (31 ≤ count760 b)) else (if i < 792 then decide (1 ≤ count791 b) else decide (2 ≤ count791 b)))) else (if i < 796 then (if i < 794 then decide (3 ≤ count791 b) else (if i < 795 then decide (4 ≤ count791 b) else decide (5 ≤ count791 b))) else (if i < 798 then (if i < 797 then decide (6 ≤ count791 b) else decide (7 ≤ count791 b)) else (if i < 799 then decide (8 ≤ count791 b) else decide (9 ≤ count791 b))))) else (if i < 807 then (if i < 803 then (if i < 801 then decide (10 ≤ count791 b) else (if i < 802 then decide (11 ≤ count791 b) else decide (12 ≤ count791 b))) else (if i < 805 then (if i < 804 then decide (13 ≤ count791 b) else decide (14 ≤ count791 b)) else (if i < 806 then decide (15 ≤ count791 b) else decide (16 ≤ count791 b)))) else (if i < 810 then (if i < 808 then decide (17 ≤ count791 b) else (if i < 809 then decide (18 ≤ count791 b) else decide (19 ≤ count791 b))) else (if i < 812 then (if i < 811 then decide (20 ≤ count791 b) else decide (21 ≤ count791 b)) else (if i < 813 then decide (22 ≤ count791 b) else decide (23 ≤ count791 b)))))) else (if i < 828 then (if i < 821 then (if i < 817 then (if i < 815 then decide (24 ≤ count791 b) else (if i < 816 then decide (25 ≤ count791 b) else decide (26 ≤ count791 b))) else (if i < 819 then (if i < 818 then decide (27 ≤ count791 b) else decide (28 ≤ count791 b)) else (if i < 820 then decide (29 ≤ count791 b) else decide (30 ≤ count791 b)))) else (if i < 824 then (if i < 822 then decide (31 ≤ count791 b) else (if i < 823 then decide (32 ≤ count791 b) else decide (33 ≤ count791 b))) else (if i < 826 then (if i < 825 then decide (34 ≤ count791 b) else decide (35 ≤ count791 b)) else (if i < 827 then decide (36 ≤ count791 b) else decide (37 ≤ count791 b))))) else (if i < 835 then (if i < 831 then (if i < 829 then decide (38 ≤ count791 b) else (if i < 830 then decide (39 ≤ count791 b) else decide (40 ≤ count791 b))) else (if i < 833 then (if i < 832 then decide (41 ≤ count791 b) else decide (42 ≤ count791 b)) else (if i < 834 then decide (1 ≤ count833 b) else decide (2 ≤ count833 b)))) else (if i < 838 then (if i < 836 then decide (1 ≤ count835 b) else (if i < 837 then decide (2 ≤ count835 b) else decide (3 ≤ count835 b))) else (if i < 840 then (if i < 839 then decide (1 ≤ count838 b) else decide (2 ≤ count838 b)) else (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b))))))) else (if i < 870 then (if i < 856 then (if i < 849 then (if i < 845 then (if i < 843 then decide (1 ≤ count842 b) else (if i < 844 then decide (2 ≤ count842 b) else decide (3 ≤ count842 b))) else (if i < 847 then (if i < 846 then decide (4 ≤ count842 b) else decide (1 ≤ count846 b)) else (if i < 848 then decide (2 ≤ count846 b) else decide (3 ≤ count846 b)))) else (if i < 852 then (if i < 850 then decide (4 ≤ count846 b) else (if i < 851 then decide (5 ≤ count846 b) else decide (6 ≤ count846 b))) else (if i < 854 then (if i < 853 then decide (7 ≤ count846 b) else decide (1 ≤ count853 b)) else (if i < 855 then decide (2 ≤ count853 b) else decide (1 ≤ count855 b))))) else (if i < 863 then (if i < 859 then (if i < 857 then decide (2 ≤ count855 b) else (if i < 858 then decide (1 ≤ count857 b) else decide (2 ≤ count857 b))) else (if i < 861 then (if i < 860 then decide (3 ≤ count857 b) else decide (4 ≤ count857 b)) else (if i < 862 then decide (1 ≤ count861 b) else decide (2 ≤ count861 b)))) else (if i < 866 then (if i < 864 then decide (1 ≤ count863 b) else (if i < 865 then decide (2 ≤ count863 b) else decide (1 ≤ count865 b))) else (if i < 868 then (if i < 867 then decide (2 ≤ count865 b) else decide (3 ≤ count865 b)) else (if i < 869 then decide (4 ≤ count865 b) else decide (1 ≤ count869 b)))))) else (if i < 884 then (if i < 877 then (if i < 873 then (if i < 871 then decide (2 ≤ count869 b) else (if i < 872 then decide (3 ≤ count869 b) else decide (4 ≤ count869 b))) else (if i < 875 then (if i < 874 then decide (5 ≤ count869 b) else decide (6 ≤ count869 b)) else (if i < 876 then decide (7 ≤ count869 b) else decide (8 ≤ count869 b)))) else (if i < 880 then (if i < 878 then decide (1 ≤ count877 b) else (if i < 879 then decide (2 ≤ count877 b) else decide (3 ≤ count877 b))) else (if i < 882 then (if i < 881 then decide (4 ≤ count877 b) else decide (5 ≤ count877 b)) else (if i < 883 then decide (6 ≤ count877 b) else decide (7 ≤ count877 b))))) else (if i < 891 then (if i < 887 then (if i < 885 then decide (8 ≤ count877 b) else (if i < 886 then decide (9 ≤ count877 b) else decide (10 ≤ count877 b))) else (if i < 889 then (if i < 888 then decide (11 ≤ count877 b) else decide (12 ≤ count877 b)) else (if i < 890 then decide (13 ≤ count877 b) else decide (14 ≤ count877 b)))) else (if i < 895 then (if i < 893 then (if i < 892 then decide (15 ≤ count877 b) else decide (1 ≤ count892 b)) else (if i < 894 then decide (2 ≤ count892 b) else decide (1 ≤ count894 b))) else (if i < 897 then (if i < 896 then decide (2 ≤ count894 b) else decide (3 ≤ count894 b)) else (if i < 898 then decide (1 ≤ count897 b) else decide (2 ≤ count897 b))))))))))) else (if i < 1349 then (if i < 1124 then (if i < 1011 then (if i < 955 then (if i < 927 then (if i < 913 then (if i < 906 then (if i < 902 then (if i < 900 then decide (1 ≤ count899 b) else (if i < 901 then decide (2 ≤ count899 b) else decide (1 ≤ count901 b))) else (if i < 904 then (if i < 903 then decide (2 ≤ count901 b) else decide (3 ≤ count901 b)) else (if i < 905 then decide (4 ≤ count901 b) else decide (1 ≤ count905 b)))) else (if i < 909 then (if i < 907 then decide (2 ≤ count905 b) else (if i < 908 then decide (3 ≤ count905 b) else decide (4 ≤ count905 b))) else (if i < 911 then (if i < 910 then decide (5 ≤ count905 b) else decide (6 ≤ count905 b)) else (if i < 912 then decide (7 ≤ count905 b) else decide (1 ≤ count912 b))))) else (if i < 920 then (if i < 916 then (if i < 914 then decide (2 ≤ count912 b) else (if i < 915 then decide (1 ≤ count914 b) else decide (2 ≤ count914 b))) else (if i < 918 then (if i < 917 then decide (1 ≤ count916 b) else decide (2 ≤ count916 b)) else (if i < 919 then decide (3 ≤ count916 b) else decide (4 ≤ count916 b)))) else (if i < 923 then (if i < 921 then decide (1 ≤ count920 b) else (if i < 922 then decide (2 ≤ count920 b) else decide (1 ≤ count922 b))) else (if i < 925 then (if i < 924 then decide (2 ≤ count922 b) else decide (1 ≤ count924 b)) else (if i < 926 then decide (2 ≤ count924 b) else decide (3 ≤ count924 b)))))) else (if i < 941 then (if i < 934 then (if i < 930 then (if i < 928 then decide (4 ≤ count924 b) else (if i < 929 then decide (1 ≤ count928 b) else decide (2 ≤ count928 b))) else (if i < 932 then (if i < 931 then decide (3 ≤ count928 b) else decide (4 ≤ count928 b)) else (if i < 933 then decide (5 ≤ count928 b) else decide (6 ≤ count928 b)))) else (if i < 937 then (if i < 935 then decide (7 ≤ count928 b) else (if i < 936 then decide (8 ≤ count928 b) else decide (1 ≤ count936 b))) else (if i < 939 then (if i < 938 then decide (2 ≤ count936 b) else decide (3 ≤ count936 b)) else (if i < 940 then decide (4 ≤ count936 b) else decide (5 ≤ count936 b))))) else (if i < 948 then (if i < 944 then (if i < 942 then decide (6 ≤ count936 b) else (if i < 943 then decide (7 ≤ count936 b) else decide (8 ≤ count936 b))) else (if i < 946 then (if i < 945 then decide (9 ≤ count936 b) else decide (10 ≤ count936 b)) else (if i < 947 then decide (11 ≤ count936 b) else decide (12 ≤ count936 b)))) else (if i < 951 then (if i < 949 then decide (13 ≤ count936 b) else (if i < 950 then decide (14 ≤ count936 b) else decide (15 ≤ count936 b))) else (if i < 953 then (if i < 952 then decide (1 ≤ count951 b) else decide (2 ≤ count951 b)) else (if i < 954 then decide (3 ≤ count951 b) else decide (4 ≤ count951 b))))))) else (if i < 983 then (if i < 969 then (if i < 962 then (if i < 958 then (if i < 956 then decide (5 ≤ count951 b) else (if i < 957 then decide (6 ≤ count951 b) else decide (7 ≤ count951 b))) else (if i < 960 then (if i < 959 then decide (8 ≤ count951 b) else decide (9 ≤ count951 b)) else (if i < 961 then decide (10 ≤ count951 b) else decide (11 ≤ count951 b)))) else (if i < 965 then (if i < 963 then decide (12 ≤ count951 b) else (if i < 964 then decide (13 ≤ count951 b) else decide (14 ≤ count951 b))) else (if i < 967 then (if i < 966 then decide (15 ≤ count951 b) else decide (16 ≤ count951 b)) else (if i < 968 then decide (17 ≤ count951 b) else decide (18 ≤ count951 b))))) else (if i < 976 then (if i < 972 then (if i < 970 then decide (19 ≤ count951 b) else (if i < 971 then decide (20 ≤ count951 b) else decide (21 ≤ count951 b))) else (if i < 974 then (if i < 973 then decide (1 ≤ count972 b) else decide (2 ≤ count972 b)) else (if i < 975 then decide (1 ≤ count974 b) else decide (2 ≤ count974 b)))) else (if i < 979 then (if i < 977 then decide (3 ≤ count974 b) else (if i < 978 then decide (1 ≤ count977 b) else decide (2 ≤ count977 b))) else (if i < 981 then (if i < 980 then decide (1 ≤ count979 b) else decide (2 ≤ count979 b)) else (if i < 982 then decide (1 ≤ count981 b) else decide (2 ≤ count981 b)))))) else (if i < 997 then (if i < 990 then (if i < 986 then (if i < 984 then decide (3 ≤ count981 b) else (if i < 985 then decide (4 ≤ count981 b) else decide (1 ≤ count985 b))) else (if i < 988 then (if i < 987 then decide (2 ≤ count985 b) else decide (3 ≤ count985 b)) else (if i < 989 then decide (4 ≤ count985 b) else decide (5 ≤ count985 b)))) else (if i < 993 then (if i < 991 then decide (6 ≤ count985 b) else (if i < 992 then decide (7 ≤ count985 b) else decide (1 ≤ count992 b))) else (if i < 995 then (if i < 994 then decide (2 ≤ count992 b) else decide (1 ≤ count994 b)) else (if i < 996 then decide (2 ≤ count994 b) else decide (1 ≤ count996 b))))) else (if i < 1004 then (if i < 1000 then (if i < 998 then decide (2 ≤ count996 b) else (if i < 999 then decide (3 ≤ count996 b) else decide (4 ≤ count996 b))) else (if i < 1002 then (if i < 1001 then decide (1 ≤ count1000 b) else decide (2 ≤ count1000 b)) else (if i < 1003 then decide (1 ≤ count1002 b) else decide (2 ≤ count1002 b)))) else (if i < 1007 then (if i < 1005 then decide (1 ≤ count1004 b) else (if i < 1006 then decide (2 ≤ count1004 b) else decide (3 ≤ count1004 b))) else (if i < 1009 then (if i < 1008 then decide (4 ≤ count1004 b) else decide (1 ≤ count1008 b)) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (3 ≤ count1008 b)))))))) else (if i < 1067 then (if i < 1039 then (if i < 1025 then (if i < 1018 then (if i < 1014 then (if i < 1012 then decide (4 ≤ count1008 b) else (if i < 1013 then decide (5 ≤ count1008 b) else decide (6 ≤ count1008 b))) else (if i < 1016 then (if i < 1015 then decide (7 ≤ count1008 b) else decide (8 ≤ count1008 b)) else (if i < 1017 then decide (1 ≤ count1016 b) else decide (2 ≤ count1016 b)))) else (if i < 1021 then (if i < 1019 then decide (3 ≤ count1016 b) else (if i < 1020 then decide (4 ≤ count1016 b) else decide (5 ≤ count1016 b))) else (if i < 1023 then (if i < 1022 then decide (6 ≤ count1016 b) else decide (7 ≤ count1016 b)) else (if i < 1024 then decide (8 ≤ count1016 b) else decide (9 ≤ count1016 b))))) else (if i < 1032 then (if i < 1028 then (if i < 1026 then decide (10 ≤ count1016 b) else (if i < 1027 then decide (11 ≤ count1016 b) else decide (12 ≤ count1016 b))) else (if i < 1030 then (if i < 1029 then decide (13 ≤ count1016 b) else decide (14 ≤ count1016 b)) else (if i < 1031 then decide (15 ≤ count1016 b) else decide (1 ≤ count1031 b)))) else (if i < 1035 then (if i < 1033 then decide (2 ≤ count1031 b) else (if i < 1034 then decide (1 ≤ count1033 b) else decide (2 ≤ count1033 b))) else (if i < 1037 then (if i < 1036 then decide (1 ≤ count1035 b) else decide (2 ≤ count1035 b)) else (if i < 1038 then decide (3 ≤ count1035 b) else decide (4 ≤ count1035 b)))))) else (if i < 1053 then (if i < 1046 then (if i < 1042 then (if i < 1040 then decide (1 ≤ count1039 b) else (if i < 1041 then decide (2 ≤ count1039 b) else decide (1 ≤ count1041 b))) else (if i < 1044 then (if i < 1043 then decide (2 ≤ count1041 b) else decide (1 ≤ count1043 b)) else (if i < 1045 then decide (2 ≤ count1043 b) else decide (3 ≤ count1043 b)))) else (if i < 1049 then (if i < 1047 then decide (4 ≤ count1043 b) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b))) else (if i < 1051 then (if i < 1050 then decide (3 ≤ count1047 b) else decide (4 ≤ count1047 b)) else (if i < 1052 then decide (5 ≤ count1047 b) else decide (6 ≤ count1047 b))))) else (if i < 1060 then (if i < 1056 then (if i < 1054 then decide (7 ≤ count1047 b) else (if i < 1055 then decide (8 ≤ count1047 b) else decide (1 ≤ count1055 b))) else (if i < 1058 then (if i < 1057 then decide (2 ≤ count1055 b) else decide (1 ≤ count1057 b)) else (if i < 1059 then decide (2 ≤ count1057 b) else decide (1 ≤ count1059 b)))) else (if i < 1063 then (if i < 1061 then decide (2 ≤ count1059 b) else (if i < 1062 then decide (3 ≤ count1059 b) else decide (4 ≤ count1059 b))) else (if i < 1065 then (if i < 1064 then decide (1 ≤ count1063 b) else decide (2 ≤ count1063 b)) else (if i < 1066 then decide (1 ≤ count1065 b) else decide (2 ≤ count1065 b))))))) else (if i < 1095 then (if i < 1081 then (if i < 1074 then (if i < 1070 then (if i < 1068 then decide (1 ≤ count1067 b) else (if i < 1069 then decide (2 ≤ count1067 b) else decide (3 ≤ count1067 b))) else (if i < 1072 then (if i < 1071 then decide (4 ≤ count1067 b) else decide (1 ≤ count1071 b)) else (if i < 1073 then decide (2 ≤ count1071 b) else decide (3 ≤ count1071 b)))) else (if i < 1077 then (if i < 1075 then decide (4 ≤ count1071 b) else (if i < 1076 then decide (5 ≤ count1071 b) else decide (6 ≤ count1071 b))) else (if i < 1079 then (if i < 1078 then decide (7 ≤ count1071 b) else decide (8 ≤ count1071 b)) else (if i < 1080 then decide (1 ≤ count1079 b) else decide (2 ≤ count1079 b))))) else (if i < 1088 then (if i < 1084 then (if i < 1082 then decide (3 ≤ count1079 b) else (if i < 1083 then decide (4 ≤ count1079 b) else decide (5 ≤ count1079 b))) else (if i < 1086 then (if i < 1085 then decide (6 ≤ count1079 b) else decide (7 ≤ count1079 b)) else (if i < 1087 then decide (8 ≤ count1079 b) else decide (9 ≤ count1079 b)))) else (if i < 1091 then (if i < 1089 then decide (10 ≤ count1079 b) else (if i < 1090 then decide (11 ≤ count1079 b) else decide (12 ≤ count1079 b))) else (if i < 1093 then (if i < 1092 then decide (13 ≤ count1079 b) else decide (14 ≤ count1079 b)) else (if i < 1094 then decide (15 ≤ count1079 b) else decide (16 ≤ count1079 b)))))) else (if i < 1109 then (if i < 1102 then (if i < 1098 then (if i < 1096 then decide (1 ≤ count1095 b) else (if i < 1097 then decide (2 ≤ count1095 b) else decide (3 ≤ count1095 b))) else (if i < 1100 then (if i < 1099 then decide (4 ≤ count1095 b) else decide (5 ≤ count1095 b)) else (if i < 1101 then decide (6 ≤ count1095 b) else decide (7 ≤ count1095 b)))) else (if i < 1105 then (if i < 1103 then decide (8 ≤ count1095 b) else (if i < 1104 then decide (9 ≤ count1095 b) else decide (10 ≤ count1095 b))) else (if i < 1107 then (if i < 1106 then decide (11 ≤ count1095 b) else decide (12 ≤ count1095 b)) else (if i < 1108 then decide (13 ≤ count1095 b) else decide (14 ≤ count1095 b))))) else (if i < 1116 then (if i < 1112 then (if i < 1110 then decide (15 ≤ count1095 b) else (if i < 1111 then decide (16 ≤ count1095 b) else decide (17 ≤ count1095 b))) else (if i < 1114 then (if i < 1113 then decide (18 ≤ count1095 b) else decide (19 ≤ count1095 b)) else (if i < 1115 then decide (20 ≤ count1095 b) else decide (21 ≤ count1095 b)))) else (if i < 1120 then (if i < 1118 then (if i < 1117 then decide (1 ≤ count1116 b) else decide (2 ≤ count1116 b)) else (if i < 1119 then decide (3 ≤ count1116 b) else decide (4 ≤ count1116 b))) else (if i < 1122 then (if i < 1121 then decide (5 ≤ count1116 b) else decide (6 ≤ count1116 b)) else (if i < 1123 then decide (7 ≤ count1116 b) else decide (8 ≤ count1116 b))))))))) else (if i < 1236 then (if i < 1180 then (if i < 1152 then (if i < 1138 then (if i < 1131 then (if i < 1127 then (if i < 1125 then decide (9 ≤ count1116 b) else (if i < 1126 then decide (10 ≤ count1116 b) else decide (11 ≤ count1116 b))) else (if i < 1129 then (if i < 1128 then decide (12 ≤ count1116 b) else decide (13 ≤ count1116 b)) else (if i < 1130 then decide (14 ≤ count1116 b) else decide (15 ≤ count1116 b)))) else (if i < 1134 then (if i < 1132 then decide (16 ≤ count1116 b) else (if i < 1133 then decide (17 ≤ count1116 b) else decide (18 ≤ count1116 b))) else (if i < 1136 then (if i < 1135 then decide (19 ≤ count1116 b) else decide (20 ≤ count1116 b)) else (if i < 1137 then decide (21 ≤ count1116 b) else decide (1 ≤ count1137 b))))) else (if i < 1145 then (if i < 1141 then (if i < 1139 then decide (2 ≤ count1137 b) else (if i < 1140 then decide (1 ≤ count1139 b) else decide (2 ≤ count1139 b))) else (if i < 1143 then (if i < 1142 then decide (3 ≤ count1139 b) else decide (1 ≤ count1142 b)) else (if i < 1144 then decide (2 ≤ count1142 b) else decide (1 ≤ count1144 b)))) else (if i < 1148 then (if i < 1146 then decide (2 ≤ count1144 b) else (if i < 1147 then decide (1 ≤ count1146 b) else decide (2 ≤ count1146 b))) else (if i < 1150 then (if i < 1149 then decide (3 ≤ count1146 b) else decide (4 ≤ count1146 b)) else (if i < 1151 then decide (1 ≤ count1150 b) else decide (2 ≤ count1150 b)))))) else (if i < 1166 then (if i < 1159 then (if i < 1155 then (if i < 1153 then decide (3 ≤ count1150 b) else (if i < 1154 then decide (4 ≤ count1150 b) else decide (5 ≤ count1150 b))) else (if i < 1157 then (if i < 1156 then decide (6 ≤ count1150 b) else decide (7 ≤ count1150 b)) else (if i < 1158 then decide (1 ≤ count1157 b) else decide (2 ≤ count1157 b)))) else (if i < 1162 then (if i < 1160 then decide (1 ≤ count1159 b) else (if i < 1161 then decide (2 ≤ count1159 b) else decide (1 ≤ count1161 b))) else (if i < 1164 then (if i < 1163 then decide (2 ≤ count1161 b) else decide (3 ≤ count1161 b)) else (if i < 1165 then decide (4 ≤ count1161 b) else decide (1 ≤ count1165 b))))) else (if i < 1173 then (if i < 1169 then (if i < 1167 then decide (2 ≤ count1165 b) else (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b))) else (if i < 1171 then (if i < 1170 then decide (1 ≤ count1169 b) else decide (2 ≤ count1169 b)) else (if i < 1172 then decide (3 ≤ count1169 b) else decide (4 ≤ count1169 b)))) else (if i < 1176 then (if i < 1174 then decide (1 ≤ count1173 b) else (if i < 1175 then decide (2 ≤ count1173 b) else decide (3 ≤ count1173 b))) else (if i < 1178 then (if i < 1177 then decide (4 ≤ count1173 b) else decide (5 ≤ count1173 b)) else (if i < 1179 then decide (6 ≤ count1173 b) else decide (7 ≤ count1173 b))))))) else (if i < 1208 then (if i < 1194 then (if i < 1187 then (if i < 1183 then (if i < 1181 then decide (8 ≤ count1173 b) else (if i < 1182 then decide (1 ≤ count1181 b) else decide (2 ≤ count1181 b))) else (if i < 1185 then (if i < 1184 then decide (3 ≤ count1181 b) else decide (4 ≤ count1181 b)) else (if i < 1186 then decide (5 ≤ count1181 b) else decide (6 ≤ count1181 b)))) else (if i < 1190 then (if i < 1188 then decide (7 ≤ count1181 b) else (if i < 1189 then decide (8 ≤ count1181 b) else decide (9 ≤ count1181 b))) else (if i < 1192 then (if i < 1191 then decide (10 ≤ count1181 b) else decide (11 ≤ count1181 b)) else (if i < 1193 then decide (12 ≤ count1181 b) else decide (13 ≤ count1181 b))))) else (if i < 1201 then (if i < 1197 then (if i < 1195 then decide (14 ≤ count1181 b) else (if i < 1196 then decide (15 ≤ count1181 b) else decide (1 ≤ count1196 b))) else (if i < 1199 then (if i < 1198 then decide (2 ≤ count1196 b) else decide (1 ≤ count1198 b)) else (if i < 1200 then decide (2 ≤ count1198 b) else decide (1 ≤ count1200 b)))) else (if i < 1204 then (if i < 1202 then decide (2 ≤ count1200 b) else (if i < 1203 then decide (3 ≤ count1200 b) else decide (4 ≤ count1200 b))) else (if i < 1206 then (if i < 1205 then decide (1 ≤ count1204 b) else decide (2 ≤ count1204 b)) else (if i < 1207 then decide (1 ≤ count1206 b) else decide (2 ≤ count1206 b)))))) else (if i < 1222 then (if i < 1215 then (if i < 1211 then (if i < 1209 then decide (1 ≤ count1208 b) else (if i < 1210 then decide (2 ≤ count1208 b) else decide (3 ≤ count1208 b))) else (if i < 1213 then (if i < 1212 then decide (4 ≤ count1208 b) else decide (1 ≤ count1212 b)) else (if i < 1214 then decide (2 ≤ count1212 b) else decide (3 ≤ count1212 b)))) else (if i < 1218 then (if i < 1216 then decide (4 ≤ count1212 b) else (if i < 1217 then decide (5 ≤ count1212 b) else decide (6 ≤ count1212 b))) else (if i < 1220 then (if i < 1219 then decide (7 ≤ count1212 b) else decide (8 ≤ count1212 b)) else (if i < 1221 then decide (1 ≤ count1220 b) else decide (2 ≤ count1220 b))))) else (if i < 1229 then (if i < 1225 then (if i < 1223 then decide (1 ≤ count1222 b) else (if i < 1224 then decide (2 ≤ count1222 b) else decide (1 ≤ count1224 b))) else (if i < 1227 then (if i < 1226 then decide (2 ≤ count1224 b) else decide (3 ≤ count1224 b)) else (if i < 1228 then decide (4 ≤ count1224 b) else decide (1 ≤ count1228 b)))) else (if i < 1232 then (if i < 1230 then decide (2 ≤ count1228 b) else (if i < 1231 then decide (1 ≤ count1230 b) else decide (2 ≤ count1230 b))) else (if i < 1234 then (if i < 1233 then decide (1 ≤ count1232 b) else decide (2 ≤ count1232 b)) else (if i < 1235 then decide (3 ≤ count1232 b) else decide (4 ≤ count1232 b)))))))) else (if i < 1292 then (if i < 1264 then (if i < 1250 then (if i < 1243 then (if i < 1239 then (if i < 1237 then decide (1 ≤ count1236 b) else (if i < 1238 then decide (2 ≤ count1236 b) else decide (3 ≤ count1236 b))) else (if i < 1241 then (if i < 1240 then decide (4 ≤ count1236 b) else decide (5 ≤ count1236 b)) else (if i < 1242 then decide (6 ≤ count1236 b) else decide (7 ≤ count1236 b)))) else (if i < 1246 then (if i < 1244 then decide (8 ≤ count1236 b) else (if i < 1245 then decide (1 ≤ count1244 b) else decide (2 ≤ count1244 b))) else (if i < 1248 then (if i < 1247 then decide (3 ≤ count1244 b) else decide (4 ≤ count1244 b)) else (if i < 1249 then decide (5 ≤ count1244 b) else decide (6 ≤ count1244 b))))) else (if i < 1257 then (if i < 1253 then (if i < 1251 then decide (7 ≤ count1244 b) else (if i < 1252 then decide (8 ≤ count1244 b) else decide (9 ≤ count1244 b))) else (if i < 1255 then (if i < 1254 then decide (10 ≤ count1244 b) else decide (11 ≤ count1244 b)) else (if i < 1256 then decide (12 ≤ count1244 b) else decide (13 ≤ count1244 b)))) else (if i < 1260 then (if i < 1258 then decide (14 ≤ count1244 b) else (if i < 1259 then decide (15 ≤ count1244 b) else decide (16 ≤ count1244 b))) else (if i < 1262 then (if i < 1261 then decide (1 ≤ count1260 b) else decide (2 ≤ count1260 b)) else (if i < 1263 then decide (3 ≤ count1260 b) else decide (4 ≤ count1260 b)))))) else (if i < 1278 then (if i < 1271 then (if i < 1267 then (if i < 1265 then decide (5 ≤ count1260 b) else (if i < 1266 then decide (6 ≤ count1260 b) else decide (7 ≤ count1260 b))) else (if i < 1269 then (if i < 1268 then decide (8 ≤ count1260 b) else decide (9 ≤ count1260 b)) else (if i < 1270 then decide (10 ≤ count1260 b) else decide (11 ≤ count1260 b)))) else (if i < 1274 then (if i < 1272 then decide (12 ≤ count1260 b) else (if i < 1273 then decide (13 ≤ count1260 b) else decide (14 ≤ count1260 b))) else (if i < 1276 then (if i < 1275 then decide (15 ≤ count1260 b) else decide (16 ≤ count1260 b)) else (if i < 1277 then decide (17 ≤ count1260 b) else decide (18 ≤ count1260 b))))) else (if i < 1285 then (if i < 1281 then (if i < 1279 then decide (19 ≤ count1260 b) else (if i < 1280 then decide (20 ≤ count1260 b) else decide (21 ≤ count1260 b))) else (if i < 1283 then (if i < 1282 then decide (22 ≤ count1260 b) else decide (23 ≤ count1260 b)) else (if i < 1284 then decide (24 ≤ count1260 b) else decide (25 ≤ count1260 b)))) else (if i < 1288 then (if i < 1286 then decide (26 ≤ count1260 b) else (if i < 1287 then decide (27 ≤ count1260 b) else decide (28 ≤ count1260 b))) else (if i < 1290 then (if i < 1289 then decide (29 ≤ count1260 b) else decide (30 ≤ count1260 b)) else (if i < 1291 then decide (31 ≤ count1260 b) else decide (1 ≤ count1291 b))))))) else (if i < 1320 then (if i < 1306 then (if i < 1299 then (if i < 1295 then (if i < 1293 then decide (2 ≤ count1291 b) else (if i < 1294 then decide (1 ≤ count1293 b) else decide (2 ≤ count1293 b))) else (if i < 1297 then (if i < 1296 then decide (3 ≤ count1293 b) else decide (1 ≤ count1296 b)) else (if i < 1298 then decide (2 ≤ count1296 b) else decide (1 ≤ count1298 b)))) else (if i < 1302 then (if i < 1300 then decide (2 ≤ count1298 b) else (if i < 1301 then decide (1 ≤ count1300 b) else decide (2 ≤ count1300 b))) else (if i < 1304 then (if i < 1303 then decide (3 ≤ count1300 b) else decide (4 ≤ count1300 b)) else (if i < 1305 then decide (1 ≤ count1304 b) else decide (2 ≤ count1304 b))))) else (if i < 1313 then (if i < 1309 then (if i < 1307 then decide (3 ≤ count1304 b) else (if i < 1308 then decide (4 ≤ count1304 b) else decide (5 ≤ count1304 b))) else (if i < 1311 then (if i < 1310 then decide (6 ≤ count1304 b) else decide (7 ≤ count1304 b)) else (if i < 1312 then decide (1 ≤ count1311 b) else decide (2 ≤ count1311 b)))) else (if i < 1316 then (if i < 1314 then decide (1 ≤ count1313 b) else (if i < 1315 then decide (2 ≤ count1313 b) else decide (1 ≤ count1315 b))) else (if i < 1318 then (if i < 1317 then decide (2 ≤ count1315 b) else decide (3 ≤ count1315 b)) else (if i < 1319 then decide (4 ≤ count1315 b) else decide (1 ≤ count1319 b)))))) else (if i < 1334 then (if i < 1327 then (if i < 1323 then (if i < 1321 then decide (2 ≤ count1319 b) else (if i < 1322 then decide (1 ≤ count1321 b) else decide (2 ≤ count1321 b))) else (if i < 1325 then (if i < 1324 then decide (1 ≤ count1323 b) else decide (2 ≤ count1323 b)) else (if i < 1326 then decide (3 ≤ count1323 b) else decide (4 ≤ count1323 b)))) else (if i < 1330 then (if i < 1328 then decide (1 ≤ count1327 b) else (if i < 1329 then decide (2 ≤ count1327 b) else decide (3 ≤ count1327 b))) else (if i < 1332 then (if i < 1331 then decide (4 ≤ count1327 b) else decide (5 ≤ count1327 b)) else (if i < 1333 then decide (6 ≤ count1327 b) else decide (7 ≤ count1327 b))))) else (if i < 1341 then (if i < 1337 then (if i < 1335 then decide (8 ≤ count1327 b) else (if i < 1336 then decide (1 ≤ count1335 b) else decide (2 ≤ count1335 b))) else (if i < 1339 then (if i < 1338 then decide (3 ≤ count1335 b) else decide (4 ≤ count1335 b)) else (if i < 1340 then decide (5 ≤ count1335 b) else decide (6 ≤ count1335 b)))) else (if i < 1345 then (if i < 1343 then (if i < 1342 then decide (7 ≤ count1335 b) else decide (8 ≤ count1335 b)) else (if i < 1344 then decide (9 ≤ count1335 b) else decide (10 ≤ count1335 b))) else (if i < 1347 then (if i < 1346 then decide (11 ≤ count1335 b) else decide (12 ≤ count1335 b)) else (if i < 1348 then decide (13 ≤ count1335 b) else decide (14 ≤ count1335 b)))))))))) else (if i < 1574 then (if i < 1461 then (if i < 1405 then (if i < 1377 then (if i < 1363 then (if i < 1356 then (if i < 1352 then (if i < 1350 then decide (15 ≤ count1335 b) else (if i < 1351 then decide (1 ≤ count1350 b) else decide (2 ≤ count1350 b))) else (if i < 1354 then (if i < 1353 then decide (1 ≤ count1352 b) else decide (2 ≤ count1352 b)) else (if i < 1355 then decide (1 ≤ count1354 b) else decide (2 ≤ count1354 b)))) else (if i < 1359 then (if i < 1357 then decide (3 ≤ count1354 b) else (if i < 1358 then decide (4 ≤ count1354 b) else decide (1 ≤ count1358 b))) else (if i < 1361 then (if i < 1360 then decide (2 ≤ count1358 b) else decide (1 ≤ count1360 b)) else (if i < 1362 then decide (2 ≤ count1360 b) else decide (1 ≤ count1362 b))))) else (if i < 1370 then (if i < 1366 then (if i < 1364 then decide (2 ≤ count1362 b) else (if i < 1365 then decide (3 ≤ count1362 b) else decide (4 ≤ count1362 b))) else (if i < 1368 then (if i < 1367 then decide (1 ≤ count1366 b) else decide (2 ≤ count1366 b)) else (if i < 1369 then decide (3 ≤ count1366 b) else decide (4 ≤ count1366 b)))) else (if i < 1373 then (if i < 1371 then decide (5 ≤ count1366 b) else (if i < 1372 then decide (6 ≤ count1366 b) else decide (7 ≤ count1366 b))) else (if i < 1375 then (if i < 1374 then decide (8 ≤ count1366 b) else decide (1 ≤ count1374 b)) else (if i < 1376 then decide (2 ≤ count1374 b) else decide (1 ≤ count1376 b)))))) else (if i < 1391 then (if i < 1384 then (if i < 1380 then (if i < 1378 then decide (2 ≤ count1376 b) else (if i < 1379 then decide (1 ≤ count1378 b) else decide (2 ≤ count1378 b))) else (if i < 1382 then (if i < 1381 then decide (3 ≤ count1378 b) else decide (4 ≤ count1378 b)) else (if i < 1383 then decide (1 ≤ count1382 b) else decide (2 ≤ count1382 b)))) else (if i < 1387 then (if i < 1385 then decide (1 ≤ count1384 b) else (if i < 1386 then decide (2 ≤ count1384 b) else decide (1 ≤ count1386 b))) else (if i < 1389 then (if i < 1388 then decide (2 ≤ count1386 b) else decide (3 ≤ count1386 b)) else (if i < 1390 then decide (4 ≤ count1386 b) else decide (1 ≤ count1390 b))))) else (if i < 1398 then (if i < 1394 then (if i < 1392 then decide (2 ≤ count1390 b) else (if i < 1393 then decide (3 ≤ count1390 b) else decide (4 ≤ count1390 b))) else (if i < 1396 then (if i < 1395 then decide (5 ≤ count1390 b) else decide (6 ≤ count1390 b)) else (if i < 1397 then decide (7 ≤ count1390 b) else decide (8 ≤ count1390 b)))) else (if i < 1401 then (if i < 1399 then decide (1 ≤ count1398 b) else (if i < 1400 then decide (2 ≤ count1398 b) else decide (3 ≤ count1398 b))) else (if i < 1403 then (if i < 1402 then decide (4 ≤ count1398 b) else decide (5 ≤ count1398 b)) else (if i < 1404 then decide (6 ≤ count1398 b) else decide (7 ≤ count1398 b))))))) else (if i < 1433 then (if i < 1419 then (if i < 1412 then (if i < 1408 then (if i < 1406 then decide (8 ≤ count1398 b) else (if i < 1407 then decide (9 ≤ count1398 b) else decide (10 ≤ count1398 b))) else (if i < 1410 then (if i < 1409 then decide (11 ≤ count1398 b) else decide (12 ≤ count1398 b)) else (if i < 1411 then decide (13 ≤ count1398 b) else decide (14 ≤ count1398 b)))) else (if i < 1415 then (if i < 1413 then decide (15 ≤ count1398 b) else (if i < 1414 then decide (16 ≤ count1398 b) else decide (1 ≤ count1414 b))) else (if i < 1417 then (if i < 1416 then decide (2 ≤ count1414 b) else decide (3 ≤ count1414 b)) else (if i < 1418 then decide (4 ≤ count1414 b) else decide (5 ≤ count1414 b))))) else (if i < 1426 then (if i < 1422 then (if i < 1420 then decide (6 ≤ count1414 b) else (if i < 1421 then decide (7 ≤ count1414 b) else decide (8 ≤ count1414 b))) else (if i < 1424 then (if i < 1423 then decide (9 ≤ count1414 b) else decide (10 ≤ count1414 b)) else (if i < 1425 then decide (11 ≤ count1414 b) else decide (12 ≤ count1414 b)))) else (if i < 1429 then (if i < 1427 then decide (13 ≤ count1414 b) else (if i < 1428 then decide (14 ≤ count1414 b) else decide (15 ≤ count1414 b))) else (if i < 1431 then (if i < 1430 then decide (16 ≤ count1414 b) else decide (17 ≤ count1414 b)) else (if i < 1432 then decide (18 ≤ count1414 b) else decide (19 ≤ count1414 b)))))) else (if i < 1447 then (if i < 1440 then (if i < 1436 then (if i < 1434 then decide (20 ≤ count1414 b) else (if i < 1435 then decide (21 ≤ count1414 b) else decide (22 ≤ count1414 b))) else (if i < 1438 then (if i < 1437 then decide (23 ≤ count1414 b) else decide (24 ≤ count1414 b)) else (if i < 1439 then decide (25 ≤ count1414 b) else decide (26 ≤ count1414 b)))) else (if i < 1443 then (if i < 1441 then decide (27 ≤ count1414 b) else (if i < 1442 then decide (28 ≤ count1414 b) else decide (29 ≤ count1414 b))) else (if i < 1445 then (if i < 1444 then decide (30 ≤ count1414 b) else decide (31 ≤ count1414 b)) else (if i < 1446 then decide (1 ≤ count1445 b) else decide (2 ≤ count1445 b))))) else (if i < 1454 then (if i < 1450 then (if i < 1448 then decide (3 ≤ count1445 b) else (if i < 1449 then decide (4 ≤ count1445 b) else decide (5 ≤ count1445 b))) else (if i < 1452 then (if i < 1451 then decide (6 ≤ count1445 b) else decide (7 ≤ count1445 b)) else (if i < 1453 then decide (8 ≤ count1445 b) else decide (9 ≤ count1445 b)))) else (if i < 1457 then (if i < 1455 then decide (10 ≤ count1445 b) else (if i < 1456 then decide (11 ≤ count1445 b) else decide (12 ≤ count1445 b))) else (if i < 1459 then (if i < 1458 then decide (13 ≤ count1445 b) else decide (14 ≤ count1445 b)) else (if i < 1460 then decide (15 ≤ count1445 b) else decide (16 ≤ count1445 b)))))))) else (if i < 1517 then (if i < 1489 then (if i < 1475 then (if i < 1468 then (if i < 1464 then (if i < 1462 then decide (17 ≤ count1445 b) else (if i < 1463 then decide (18 ≤ count1445 b) else decide (19 ≤ count1445 b))) else (if i < 1466 then (if i < 1465 then decide (20 ≤ count1445 b) else decide (21 ≤ count1445 b)) else (if i < 1467 then decide (22 ≤ count1445 b) else decide (23 ≤ count1445 b)))) else (if i < 1471 then (if i < 1469 then decide (24 ≤ count1445 b) else (if i < 1470 then decide (25 ≤ count1445 b) else decide (26 ≤ count1445 b))) else (if i < 1473 then (if i < 1472 then decide (27 ≤ count1445 b) else decide (28 ≤ count1445 b)) else (if i < 1474 then decide (29 ≤ count1445 b) else decide (30 ≤ count1445 b))))) else (if i < 1482 then (if i < 1478 then (if i < 1476 then decide (31 ≤ count1445 b) else (if i < 1477 then decide (32 ≤ count1445 b) else decide (33 ≤ count1445 b))) else (if i < 1480 then (if i < 1479 then decide (34 ≤ count1445 b) else decide (35 ≤ count1445 b)) else (if i < 1481 then decide (36 ≤ count1445 b) else decide (37 ≤ count1445 b)))) else (if i < 1485 then (if i < 1483 then decide (38 ≤ count1445 b) else (if i < 1484 then decide (39 ≤ count1445 b) else decide (40 ≤ count1445 b))) else (if i < 1487 then (if i < 1486 then decide (41 ≤ count1445 b) else decide (42 ≤ count1445 b)) else (if i < 1488 then decide (1 ≤ count1487 b) else decide (2 ≤ count1487 b)))))) else (if i < 1503 then (if i < 1496 then (if i < 1492 then (if i < 1490 then decide (1 ≤ count1489 b) else (if i < 1491 then decide (2 ≤ count1489 b) else decide (3 ≤ count1489 b))) else (if i < 1494 then (if i < 1493 then decide (1 ≤ count1492 b) else decide (2 ≤ count1492 b)) else (if i < 1495 then decide (1 ≤ count1494 b) else decide (2 ≤ count1494 b)))) else (if i < 1499 then (if i < 1497 then decide (1 ≤ count1496 b) else (if i < 1498 then decide (2 ≤ count1496 b) else decide (3 ≤ count1496 b))) else (if i < 1501 then (if i < 1500 then decide (4 ≤ count1496 b) else decide (1 ≤ count1500 b)) else (if i < 1502 then decide (2 ≤ count1500 b) else decide (3 ≤ count1500 b))))) else (if i < 1510 then (if i < 1506 then (if i < 1504 then decide (4 ≤ count1500 b) else (if i < 1505 then decide (5 ≤ count1500 b) else decide (6 ≤ count1500 b))) else (if i < 1508 then (if i < 1507 then decide (7 ≤ count1500 b) else decide (1 ≤ count1507 b)) else (if i < 1509 then decide (2 ≤ count1507 b) else decide (1 ≤ count1509 b)))) else (if i < 1513 then (if i < 1511 then decide (2 ≤ count1509 b) else (if i < 1512 then decide (1 ≤ count1511 b) else decide (2 ≤ count1511 b))) else (if i < 1515 then (if i < 1514 then decide (3 ≤ count1511 b) else decide (4 ≤ count1511 b)) else (if i < 1516 then decide (1 ≤ count1515 b) else decide (2 ≤ count1515 b))))))) else (if i < 1545 then (if i < 1531 then (if i < 1524 then (if i < 1520 then (if i < 1518 then decide (1 ≤ count1517 b) else (if i < 1519 then decide (2 ≤ count1517 b) else decide (1 ≤ count1519 b))) else (if i < 1522 then (if i < 1521 then decide (2 ≤ count1519 b) else decide (3 ≤ count1519 b)) else (if i < 1523 then decide (4 ≤ count1519 b) else decide (1 ≤ count1523 b)))) else (if i < 1527 then (if i < 1525 then decide (2 ≤ count1523 b) else (if i < 1526 then decide (3 ≤ count1523 b) else decide (4 ≤ count1523 b))) else (if i < 1529 then (if i < 1528 then decide (5 ≤ count1523 b) else decide (6 ≤ count1523 b)) else (if i < 1530 then decide (7 ≤ count1523 b) else decide (8 ≤ count1523 b))))) else (if i < 1538 then (if i < 1534 then (if i < 1532 then decide (1 ≤ count1531 b) else (if i < 1533 then decide (2 ≤ count1531 b) else decide (3 ≤ count1531 b))) else (if i < 1536 then (if i < 1535 then decide (4 ≤ count1531 b) else decide (5 ≤ count1531 b)) else (if i < 1537 then decide (6 ≤ count1531 b) else decide (7 ≤ count1531 b)))) else (if i < 1541 then (if i < 1539 then decide (8 ≤ count1531 b) else (if i < 1540 then decide (9 ≤ count1531 b) else decide (10 ≤ count1531 b))) else (if i < 1543 then (if i < 1542 then decide (11 ≤ count1531 b) else decide (12 ≤ count1531 b)) else (if i < 1544 then decide (13 ≤ count1531 b) else decide (14 ≤ count1531 b)))))) else (if i < 1559 then (if i < 1552 then (if i < 1548 then (if i < 1546 then decide (15 ≤ count1531 b) else (if i < 1547 then decide (1 ≤ count1546 b) else decide (2 ≤ count1546 b))) else (if i < 1550 then (if i < 1549 then decide (1 ≤ count1548 b) else decide (2 ≤ count1548 b)) else (if i < 1551 then decide (1 ≤ count1550 b) else decide (2 ≤ count1550 b)))) else (if i < 1555 then (if i < 1553 then decide (3 ≤ count1550 b) else (if i < 1554 then decide (4 ≤ count1550 b) else decide (1 ≤ count1554 b))) else (if i < 1557 then (if i < 1556 then decide (2 ≤ count1554 b) else decide (1 ≤ count1556 b)) else (if i < 1558 then decide (2 ≤ count1556 b) else decide (1 ≤ count1558 b))))) else (if i < 1566 then (if i < 1562 then (if i < 1560 then decide (2 ≤ count1558 b) else (if i < 1561 then decide (3 ≤ count1558 b) else decide (4 ≤ count1558 b))) else (if i < 1564 then (if i < 1563 then decide (1 ≤ count1562 b) else decide (2 ≤ count1562 b)) else (if i < 1565 then decide (3 ≤ count1562 b) else decide (4 ≤ count1562 b)))) else (if i < 1570 then (if i < 1568 then (if i < 1567 then decide (5 ≤ count1562 b) else decide (6 ≤ count1562 b)) else (if i < 1569 then decide (7 ≤ count1562 b) else decide (8 ≤ count1562 b))) else (if i < 1572 then (if i < 1571 then decide (1 ≤ count1570 b) else decide (2 ≤ count1570 b)) else (if i < 1573 then decide (1 ≤ count1572 b) else decide (2 ≤ count1572 b))))))))) else (if i < 1686 then (if i < 1630 then (if i < 1602 then (if i < 1588 then (if i < 1581 then (if i < 1577 then (if i < 1575 then decide (1 ≤ count1574 b) else (if i < 1576 then decide (2 ≤ count1574 b) else decide (3 ≤ count1574 b))) else (if i < 1579 then (if i < 1578 then decide (4 ≤ count1574 b) else decide (1 ≤ count1578 b)) else (if i < 1580 then decide (2 ≤ count1578 b) else decide (1 ≤ count1580 b)))) else (if i < 1584 then (if i < 1582 then decide (2 ≤ count1580 b) else (if i < 1583 then decide (1 ≤ count1582 b) else decide (2 ≤ count1582 b))) else (if i < 1586 then (if i < 1585 then decide (3 ≤ count1582 b) else decide (4 ≤ count1582 b)) else (if i < 1587 then decide (1 ≤ count1586 b) else decide (2 ≤ count1586 b))))) else (if i < 1595 then (if i < 1591 then (if i < 1589 then decide (3 ≤ count1586 b) else (if i < 1590 then decide (4 ≤ count1586 b) else decide (5 ≤ count1586 b))) else (if i < 1593 then (if i < 1592 then decide (6 ≤ count1586 b) else decide (7 ≤ count1586 b)) else (if i < 1594 then decide (8 ≤ count1586 b) else decide (1 ≤ count1594 b)))) else (if i < 1598 then (if i < 1596 then decide (2 ≤ count1594 b) else (if i < 1597 then decide (3 ≤ count1594 b) else decide (4 ≤ count1594 b))) else (if i < 1600 then (if i < 1599 then decide (5 ≤ count1594 b) else decide (6 ≤ count1594 b)) else (if i < 1601 then decide (7 ≤ count1594 b) else decide (8 ≤ count1594 b)))))) else (if i < 1616 then (if i < 1609 then (if i < 1605 then (if i < 1603 then decide (9 ≤ count1594 b) else (if i < 1604 then decide (10 ≤ count1594 b) else decide (11 ≤ count1594 b))) else (if i < 1607 then (if i < 1606 then decide (12 ≤ count1594 b) else decide (13 ≤ count1594 b)) else (if i < 1608 then decide (14 ≤ count1594 b) else decide (15 ≤ count1594 b)))) else (if i < 1612 then (if i < 1610 then decide (16 ≤ count1594 b) else (if i < 1611 then decide (1 ≤ count1610 b) else decide (2 ≤ count1610 b))) else (if i < 1614 then (if i < 1613 then decide (3 ≤ count1610 b) else decide (4 ≤ count1610 b)) else (if i < 1615 then decide (5 ≤ count1610 b) else decide (6 ≤ count1610 b))))) else (if i < 1623 then (if i < 1619 then (if i < 1617 then decide (7 ≤ count1610 b) else (if i < 1618 then decide (8 ≤ count1610 b) else decide (9 ≤ count1610 b))) else (if i < 1621 then (if i < 1620 then decide (10 ≤ count1610 b) else decide (11 ≤ count1610 b)) else (if i < 1622 then decide (12 ≤ count1610 b) else decide (13 ≤ count1610 b)))) else (if i < 1626 then (if i < 1624 then decide (14 ≤ count1610 b) else (if i < 1625 then decide (15 ≤ count1610 b) else decide (16 ≤ count1610 b))) else (if i < 1628 then (if i < 1627 then decide (17 ≤ count1610 b) else decide (18 ≤ count1610 b)) else (if i < 1629 then decide (19 ≤ count1610 b) else decide (20 ≤ count1610 b))))))) else (if i < 1658 then (if i < 1644 then (if i < 1637 then (if i < 1633 then (if i < 1631 then decide (21 ≤ count1610 b) else (if i < 1632 then decide (22 ≤ count1610 b) else decide (1 ≤ count1632 b))) else (if i < 1635 then (if i < 1634 then decide (2 ≤ count1632 b) else decide (1 ≤ count1634 b)) else (if i < 1636 then decide (2 ≤ count1634 b) else decide (3 ≤ count1634 b)))) else (if i < 1640 then (if i < 1638 then decide (1 ≤ count1637 b) else (if i < 1639 then decide (2 ≤ count1637 b) else decide (1 ≤ count1639 b))) else (if i < 1642 then (if i < 1641 then decide (2 ≤ count1639 b) else decide (1 ≤ count1641 b)) else (if i < 1643 then decide (2 ≤ count1641 b) else decide (3 ≤ count1641 b))))) else (if i < 1651 then (if i < 1647 then (if i < 1645 then decide (4 ≤ count1641 b) else (if i < 1646 then decide (1 ≤ count1645 b) else decide (2 ≤ count1645 b))) else (if i < 1649 then (if i < 1648 then decide (3 ≤ count1645 b) else decide (4 ≤ count1645 b)) else (if i < 1650 then decide (5 ≤ count1645 b) else decide (6 ≤ count1645 b)))) else (if i < 1654 then (if i < 1652 then decide (7 ≤ count1645 b) else (if i < 1653 then decide (1 ≤ count1652 b) else decide (2 ≤ count1652 b))) else (if i < 1656 then (if i < 1655 then decide (1 ≤ count1654 b) else decide (2 ≤ count1654 b)) else (if i < 1657 then decide (1 ≤ count1656 b) else decide (2 ≤ count1656 b)))))) else (if i < 1672 then (if i < 1665 then (if i < 1661 then (if i < 1659 then decide (3 ≤ count1656 b) else (if i < 1660 then decide (4 ≤ count1656 b) else decide (1 ≤ count1660 b))) else (if i < 1663 then (if i < 1662 then decide (2 ≤ count1660 b) else decide (1 ≤ count1662 b)) else (if i < 1664 then decide (2 ≤ count1662 b) else decide (1 ≤ count1664 b)))) else (if i < 1668 then (if i < 1666 then decide (2 ≤ count1664 b) else (if i < 1667 then decide (3 ≤ count1664 b) else decide (4 ≤ count1664 b))) else (if i < 1670 then (if i < 1669 then decide (1 ≤ count1668 b) else decide (2 ≤ count1668 b)) else (if i < 1671 then decide (3 ≤ count1668 b) else decide (4 ≤ count1668 b))))) else (if i < 1679 then (if i < 1675 then (if i < 1673 then decide (5 ≤ count1668 b) else (if i < 1674 then decide (6 ≤ count1668 b) else decide (7 ≤ count1668 b))) else (if i < 1677 then (if i < 1676 then decide (8 ≤ count1668 b) else decide (1 ≤ count1676 b)) else (if i < 1678 then decide (2 ≤ count1676 b) else decide (3 ≤ count1676 b)))) else (if i < 1682 then (if i < 1680 then decide (4 ≤ count1676 b) else (if i < 1681 then decide (5 ≤ count1676 b) else decide (6 ≤ count1676 b))) else (if i < 1684 then (if i < 1683 then decide (7 ≤ count1676 b) else decide (8 ≤ count1676 b)) else (if i < 1685 then decide (9 ≤ count1676 b) else decide (10 ≤ count1676 b)))))))) else (if i < 1742 then (if i < 1714 then (if i < 1700 then (if i < 1693 then (if i < 1689 then (if i < 1687 then decide (11 ≤ count1676 b) else (if i < 1688 then decide (12 ≤ count1676 b) else decide (13 ≤ count1676 b))) else (if i < 1691 then (if i < 1690 then decide (14 ≤ count1676 b) else decide (15 ≤ count1676 b)) else (if i < 1692 then decide (1 ≤ count1691 b) else decide (2 ≤ count1691 b)))) else (if i < 1696 then (if i < 1694 then decide (1 ≤ count1693 b) else (if i < 1695 then decide (2 ≤ count1693 b) else decide (1 ≤ count1695 b))) else (if i < 1698 then (if i < 1697 then decide (2 ≤ count1695 b) else decide (3 ≤ count1695 b)) else (if i < 1699 then decide (4 ≤ count1695 b) else decide (1 ≤ count1699 b))))) else (if i < 1707 then (if i < 1703 then (if i < 1701 then decide (2 ≤ count1699 b) else (if i < 1702 then decide (1 ≤ count1701 b) else decide (2 ≤ count1701 b))) else (if i < 1705 then (if i < 1704 then decide (1 ≤ count1703 b) else decide (2 ≤ count1703 b)) else (if i < 1706 then decide (3 ≤ count1703 b) else decide (4 ≤ count1703 b)))) else (if i < 1710 then (if i < 1708 then decide (1 ≤ count1707 b) else (if i < 1709 then decide (2 ≤ count1707 b) else decide (3 ≤ count1707 b))) else (if i < 1712 then (if i < 1711 then decide (4 ≤ count1707 b) else decide (5 ≤ count1707 b)) else (if i < 1713 then decide (6 ≤ count1707 b) else decide (7 ≤ count1707 b)))))) else (if i < 1728 then (if i < 1721 then (if i < 1717 then (if i < 1715 then decide (8 ≤ count1707 b) else (if i < 1716 then decide (1 ≤ count1715 b) else decide (2 ≤ count1715 b))) else (if i < 1719 then (if i < 1718 then decide (1 ≤ count1717 b) else decide (2 ≤ count1717 b)) else (if i < 1720 then decide (1 ≤ count1719 b) else decide (2 ≤ count1719 b)))) else (if i < 1724 then (if i < 1722 then decide (3 ≤ count1719 b) else (if i < 1723 then decide (4 ≤ count1719 b) else decide (1 ≤ count1723 b))) else (if i < 1726 then (if i < 1725 then decide (2 ≤ count1723 b) else decide (1 ≤ count1725 b)) else (if i < 1727 then decide (2 ≤ count1725 b) else decide (1 ≤ count1727 b))))) else (if i < 1735 then (if i < 1731 then (if i < 1729 then decide (2 ≤ count1727 b) else (if i < 1730 then decide (3 ≤ count1727 b) else decide (4 ≤ count1727 b))) else (if i < 1733 then (if i < 1732 then decide (1 ≤ count1731 b) else decide (2 ≤ count1731 b)) else (if i < 1734 then decide (3 ≤ count1731 b) else decide (4 ≤ count1731 b)))) else (if i < 1738 then (if i < 1736 then decide (5 ≤ count1731 b) else (if i < 1737 then decide (6 ≤ count1731 b) else decide (7 ≤ count1731 b))) else (if i < 1740 then (if i < 1739 then decide (8 ≤ count1731 b) else decide (1 ≤ count1739 b)) else (if i < 1741 then decide (2 ≤ count1739 b) else decide (3 ≤ count1739 b))))))) else (if i < 1770 then (if i < 1756 then (if i < 1749 then (if i < 1745 then (if i < 1743 then decide (4 ≤ count1739 b) else (if i < 1744 then decide (5 ≤ count1739 b) else decide (6 ≤ count1739 b))) else (if i < 1747 then (if i < 1746 then decide (7 ≤ count1739 b) else decide (8 ≤ count1739 b)) else (if i < 1748 then decide (9 ≤ count1739 b) else decide (10 ≤ count1739 b)))) else (if i < 1752 then (if i < 1750 then decide (11 ≤ count1739 b) else (if i < 1751 then decide (12 ≤ count1739 b) else decide (13 ≤ count1739 b))) else (if i < 1754 then (if i < 1753 then decide (14 ≤ count1739 b) else decide (15 ≤ count1739 b)) else (if i < 1755 then decide (16 ≤ count1739 b) else decide (1 ≤ count1755 b))))) else (if i < 1763 then (if i < 1759 then (if i < 1757 then decide (2 ≤ count1755 b) else (if i < 1758 then decide (3 ≤ count1755 b) else decide (4 ≤ count1755 b))) else (if i < 1761 then (if i < 1760 then decide (5 ≤ count1755 b) else decide (6 ≤ count1755 b)) else (if i < 1762 then decide (7 ≤ count1755 b) else decide (8 ≤ count1755 b)))) else (if i < 1766 then (if i < 1764 then decide (9 ≤ count1755 b) else (if i < 1765 then decide (10 ≤ count1755 b) else decide (11 ≤ count1755 b))) else (if i < 1768 then (if i < 1767 then decide (12 ≤ count1755 b) else decide (13 ≤ count1755 b)) else (if i < 1769 then decide (14 ≤ count1755 b) else decide (15 ≤ count1755 b)))))) else (if i < 1784 then (if i < 1777 then (if i < 1773 then (if i < 1771 then decide (16 ≤ count1755 b) else (if i < 1772 then decide (17 ≤ count1755 b) else decide (18 ≤ count1755 b))) else (if i < 1775 then (if i < 1774 then decide (19 ≤ count1755 b) else decide (20 ≤ count1755 b)) else (if i < 1776 then decide (21 ≤ count1755 b) else decide (22 ≤ count1755 b)))) else (if i < 1780 then (if i < 1778 then decide (1 ≤ count1777 b) else (if i < 1779 then decide (2 ≤ count1777 b) else decide (3 ≤ count1777 b))) else (if i < 1782 then (if i < 1781 then decide (4 ≤ count1777 b) else decide (5 ≤ count1777 b)) else (if i < 1783 then decide (6 ≤ count1777 b) else decide (7 ≤ count1777 b))))) else (if i < 1791 then (if i < 1787 then (if i < 1785 then decide (8 ≤ count1777 b) else (if i < 1786 then decide (9 ≤ count1777 b) else decide (10 ≤ count1777 b))) else (if i < 1789 then (if i < 1788 then decide (11 ≤ count1777 b) else decide (12 ≤ count1777 b)) else (if i < 1790 then decide (13 ≤ count1777 b) else decide (14 ≤ count1777 b)))) else (if i < 1795 then (if i < 1793 then (if i < 1792 then decide (15 ≤ count1777 b) else decide (16 ≤ count1777 b)) else (if i < 1794 then decide (17 ≤ count1777 b) else decide (18 ≤ count1777 b))) else (if i < 1797 then (if i < 1796 then decide (19 ≤ count1777 b) else decide (20 ≤ count1777 b)) else (if i < 1798 then decide (21 ≤ count1777 b) else decide (22 ≤ count1777 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (8 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (12 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (33 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (35 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (39 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (40 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (48 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (50 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (51 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (52 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (56 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (160 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (162 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (164 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (167 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (168 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (170 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (171 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (172 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (177 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (180 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (181 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (182 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (183 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (185 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (186 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (187 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (225 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (227 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (229 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (230 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (231 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (232 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (233 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (238 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (239 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (240 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (242 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (243 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (244 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (248 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (250 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (252 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (253 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (255 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (288 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (290 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (292 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (294 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (295 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (296 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (297 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (298 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (300 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (302 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (305 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (307 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (308 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (309 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (311 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (313 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (314 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (315 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (353 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (355 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (357 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (358 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (359 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (360 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (361 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (366 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (367 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (368 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (370 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (371 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (372 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (376 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (380 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (381 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (383 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (417 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (419 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (421 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (422 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (424 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (427 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (428 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (430 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (431 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (432 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (433 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (434 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (435 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (438 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (440 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (444 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (445 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (446 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (447 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (480 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (481 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (482 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (484 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (485 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (486 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (488 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (489 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (490 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (491 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (492 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (494 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (495 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (497 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (500 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (501 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (502 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (503 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (505 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (506 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (507 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (509 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (511 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (12 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (33 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (35 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (39 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (40 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (48 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (50 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (51 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (52 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (56 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (164 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (170 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (172 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (180 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (181 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (183 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (185 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (187 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (225 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (232 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (239 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (242 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (243 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (250 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (252 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (253 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (290 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (292 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (297 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (298 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (300 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (302 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (308 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (309 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (311 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (313 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (314 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (315 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (353 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (359 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (360 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (367 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (370 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (371 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (380 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (381 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (383 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (424 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (431 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (434 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (438 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (444 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (445 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (490 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (500 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (503 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (505 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (507 : Vertex)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value274 (q : Snake 81) : valuation q 274 = decide (2 ≤ count273 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value332 (q : Snake 81) : valuation q 332 = decide (2 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value364 (q : Snake 81) : valuation q 364 = decide (2 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value366 (q : Snake 81) : valuation q 366 = decide (2 ≤ count365 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value422 (q : Snake 81) : valuation q 422 = decide (2 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value424 (q : Snake 81) : valuation q 424 = decide (2 ≤ count423 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value452 (q : Snake 81) : valuation q 452 = decide (2 ≤ count451 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 (baseVal q)) := rfl
theorem value480 (q : Snake 81) : valuation q 480 = decide (2 ≤ count479 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value482 (q : Snake 81) : valuation q 482 = decide (2 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value484 (q : Snake 81) : valuation q 484 = decide (2 ≤ count483 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value486 (q : Snake 81) : valuation q 486 = decide (2 ≤ count485 (baseVal q)) := rfl
theorem value488 (q : Snake 81) : valuation q 488 = decide (2 ≤ count487 (baseVal q)) := rfl
theorem value834 (q : Snake 81) : valuation q 834 = decide (2 ≤ count833 (baseVal q)) := rfl
theorem value836 (q : Snake 81) : valuation q 836 = decide (2 ≤ count835 (baseVal q)) := rfl
theorem value837 (q : Snake 81) : valuation q 837 = decide (3 ≤ count835 (baseVal q)) := rfl
theorem value838 (q : Snake 81) : valuation q 838 = decide (1 ≤ count838 (baseVal q)) := rfl
theorem value839 (q : Snake 81) : valuation q 839 = decide (2 ≤ count838 (baseVal q)) := rfl
theorem value840 (q : Snake 81) : valuation q 840 = decide (1 ≤ count840 (baseVal q)) := rfl
theorem value841 (q : Snake 81) : valuation q 841 = decide (2 ≤ count840 (baseVal q)) := rfl
theorem value842 (q : Snake 81) : valuation q 842 = decide (1 ≤ count842 (baseVal q)) := rfl
theorem value843 (q : Snake 81) : valuation q 843 = decide (2 ≤ count842 (baseVal q)) := rfl
theorem value844 (q : Snake 81) : valuation q 844 = decide (3 ≤ count842 (baseVal q)) := rfl
theorem value848 (q : Snake 81) : valuation q 848 = decide (3 ≤ count846 (baseVal q)) := rfl
theorem value849 (q : Snake 81) : valuation q 849 = decide (4 ≤ count846 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (5 ≤ count846 (baseVal q)) := rfl
theorem value851 (q : Snake 81) : valuation q 851 = decide (6 ≤ count846 (baseVal q)) := rfl
theorem value853 (q : Snake 81) : valuation q 853 = decide (1 ≤ count853 (baseVal q)) := rfl
theorem value854 (q : Snake 81) : valuation q 854 = decide (2 ≤ count853 (baseVal q)) := rfl
theorem value855 (q : Snake 81) : valuation q 855 = decide (1 ≤ count855 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (1 ≤ count857 (baseVal q)) := rfl
theorem value858 (q : Snake 81) : valuation q 858 = decide (2 ≤ count857 (baseVal q)) := rfl
theorem value859 (q : Snake 81) : valuation q 859 = decide (3 ≤ count857 (baseVal q)) := rfl
theorem value861 (q : Snake 81) : valuation q 861 = decide (1 ≤ count861 (baseVal q)) := rfl
theorem value862 (q : Snake 81) : valuation q 862 = decide (2 ≤ count861 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (1 ≤ count863 (baseVal q)) := rfl
theorem value864 (q : Snake 81) : valuation q 864 = decide (2 ≤ count863 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (1 ≤ count865 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (2 ≤ count865 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (3 ≤ count865 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (4 ≤ count865 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (1 ≤ count869 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (2 ≤ count869 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (3 ≤ count869 (baseVal q)) := rfl
theorem value872 (q : Snake 81) : valuation q 872 = decide (4 ≤ count869 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (5 ≤ count869 (baseVal q)) := rfl
theorem value879 (q : Snake 81) : valuation q 879 = decide (3 ≤ count877 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (4 ≤ count877 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (5 ≤ count877 (baseVal q)) := rfl
theorem value882 (q : Snake 81) : valuation q 882 = decide (6 ≤ count877 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (7 ≤ count877 (baseVal q)) := rfl
theorem value884 (q : Snake 81) : valuation q 884 = decide (8 ≤ count877 (baseVal q)) := rfl
theorem value892 (q : Snake 81) : valuation q 892 = decide (1 ≤ count892 (baseVal q)) := rfl
theorem value893 (q : Snake 81) : valuation q 893 = decide (2 ≤ count892 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (1 ≤ count894 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (2 ≤ count894 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (3 ≤ count894 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (1 ≤ count897 (baseVal q)) := rfl
theorem value898 (q : Snake 81) : valuation q 898 = decide (2 ≤ count897 (baseVal q)) := rfl
theorem value899 (q : Snake 81) : valuation q 899 = decide (1 ≤ count899 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (2 ≤ count899 (baseVal q)) := rfl
theorem value901 (q : Snake 81) : valuation q 901 = decide (1 ≤ count901 (baseVal q)) := rfl
theorem value902 (q : Snake 81) : valuation q 902 = decide (2 ≤ count901 (baseVal q)) := rfl
theorem value903 (q : Snake 81) : valuation q 903 = decide (3 ≤ count901 (baseVal q)) := rfl
theorem value905 (q : Snake 81) : valuation q 905 = decide (1 ≤ count905 (baseVal q)) := rfl
theorem value906 (q : Snake 81) : valuation q 906 = decide (2 ≤ count905 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (3 ≤ count905 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (4 ≤ count905 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (5 ≤ count905 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (1 ≤ count912 (baseVal q)) := rfl
theorem value913 (q : Snake 81) : valuation q 913 = decide (2 ≤ count912 (baseVal q)) := rfl
theorem value914 (q : Snake 81) : valuation q 914 = decide (1 ≤ count914 (baseVal q)) := rfl
theorem value915 (q : Snake 81) : valuation q 915 = decide (2 ≤ count914 (baseVal q)) := rfl
theorem value916 (q : Snake 81) : valuation q 916 = decide (1 ≤ count916 (baseVal q)) := rfl
theorem value917 (q : Snake 81) : valuation q 917 = decide (2 ≤ count916 (baseVal q)) := rfl
theorem value918 (q : Snake 81) : valuation q 918 = decide (3 ≤ count916 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (4 ≤ count916 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (1 ≤ count920 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (2 ≤ count920 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (1 ≤ count922 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (2 ≤ count922 (baseVal q)) := rfl
theorem value924 (q : Snake 81) : valuation q 924 = decide (1 ≤ count924 (baseVal q)) := rfl
theorem value925 (q : Snake 81) : valuation q 925 = decide (2 ≤ count924 (baseVal q)) := rfl
theorem value926 (q : Snake 81) : valuation q 926 = decide (3 ≤ count924 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (4 ≤ count924 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (1 ≤ count928 (baseVal q)) := rfl
theorem value929 (q : Snake 81) : valuation q 929 = decide (2 ≤ count928 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (3 ≤ count928 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (4 ≤ count928 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (5 ≤ count928 (baseVal q)) := rfl
theorem value933 (q : Snake 81) : valuation q 933 = decide (6 ≤ count928 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (2 ≤ count936 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (3 ≤ count936 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (4 ≤ count936 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (5 ≤ count936 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (6 ≤ count936 (baseVal q)) := rfl
theorem value942 (q : Snake 81) : valuation q 942 = decide (7 ≤ count936 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (8 ≤ count936 (baseVal q)) := rfl
theorem value944 (q : Snake 81) : valuation q 944 = decide (9 ≤ count936 (baseVal q)) := rfl
theorem value945 (q : Snake 81) : valuation q 945 = decide (10 ≤ count936 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (6 ≤ count951 (baseVal q)) := rfl
theorem value957 (q : Snake 81) : valuation q 957 = decide (7 ≤ count951 (baseVal q)) := rfl
theorem value958 (q : Snake 81) : valuation q 958 = decide (8 ≤ count951 (baseVal q)) := rfl
theorem value959 (q : Snake 81) : valuation q 959 = decide (9 ≤ count951 (baseVal q)) := rfl
theorem value960 (q : Snake 81) : valuation q 960 = decide (10 ≤ count951 (baseVal q)) := rfl
theorem value961 (q : Snake 81) : valuation q 961 = decide (11 ≤ count951 (baseVal q)) := rfl
theorem value962 (q : Snake 81) : valuation q 962 = decide (12 ≤ count951 (baseVal q)) := rfl
theorem value963 (q : Snake 81) : valuation q 963 = decide (13 ≤ count951 (baseVal q)) := rfl
theorem value964 (q : Snake 81) : valuation q 964 = decide (14 ≤ count951 (baseVal q)) := rfl
theorem value965 (q : Snake 81) : valuation q 965 = decide (15 ≤ count951 (baseVal q)) := rfl
theorem value972 (q : Snake 81) : valuation q 972 = decide (1 ≤ count972 (baseVal q)) := rfl
theorem value973 (q : Snake 81) : valuation q 973 = decide (2 ≤ count972 (baseVal q)) := rfl
theorem value974 (q : Snake 81) : valuation q 974 = decide (1 ≤ count974 (baseVal q)) := rfl
theorem value975 (q : Snake 81) : valuation q 975 = decide (2 ≤ count974 (baseVal q)) := rfl
theorem value976 (q : Snake 81) : valuation q 976 = decide (3 ≤ count974 (baseVal q)) := rfl
theorem value977 (q : Snake 81) : valuation q 977 = decide (1 ≤ count977 (baseVal q)) := rfl
theorem value978 (q : Snake 81) : valuation q 978 = decide (2 ≤ count977 (baseVal q)) := rfl
theorem value979 (q : Snake 81) : valuation q 979 = decide (1 ≤ count979 (baseVal q)) := rfl
theorem value980 (q : Snake 81) : valuation q 980 = decide (2 ≤ count979 (baseVal q)) := rfl
theorem value981 (q : Snake 81) : valuation q 981 = decide (1 ≤ count981 (baseVal q)) := rfl
theorem value982 (q : Snake 81) : valuation q 982 = decide (2 ≤ count981 (baseVal q)) := rfl
theorem value983 (q : Snake 81) : valuation q 983 = decide (3 ≤ count981 (baseVal q)) := rfl
theorem value985 (q : Snake 81) : valuation q 985 = decide (1 ≤ count985 (baseVal q)) := rfl
theorem value986 (q : Snake 81) : valuation q 986 = decide (2 ≤ count985 (baseVal q)) := rfl
theorem value987 (q : Snake 81) : valuation q 987 = decide (3 ≤ count985 (baseVal q)) := rfl
theorem value988 (q : Snake 81) : valuation q 988 = decide (4 ≤ count985 (baseVal q)) := rfl
theorem value989 (q : Snake 81) : valuation q 989 = decide (5 ≤ count985 (baseVal q)) := rfl
theorem value992 (q : Snake 81) : valuation q 992 = decide (1 ≤ count992 (baseVal q)) := rfl
theorem value993 (q : Snake 81) : valuation q 993 = decide (2 ≤ count992 (baseVal q)) := rfl
theorem value994 (q : Snake 81) : valuation q 994 = decide (1 ≤ count994 (baseVal q)) := rfl
theorem value995 (q : Snake 81) : valuation q 995 = decide (2 ≤ count994 (baseVal q)) := rfl
theorem value996 (q : Snake 81) : valuation q 996 = decide (1 ≤ count996 (baseVal q)) := rfl
theorem value997 (q : Snake 81) : valuation q 997 = decide (2 ≤ count996 (baseVal q)) := rfl
theorem value998 (q : Snake 81) : valuation q 998 = decide (3 ≤ count996 (baseVal q)) := rfl
theorem value999 (q : Snake 81) : valuation q 999 = decide (4 ≤ count996 (baseVal q)) := rfl
theorem value1000 (q : Snake 81) : valuation q 1000 = decide (1 ≤ count1000 (baseVal q)) := rfl
theorem value1001 (q : Snake 81) : valuation q 1001 = decide (2 ≤ count1000 (baseVal q)) := rfl
theorem value1002 (q : Snake 81) : valuation q 1002 = decide (1 ≤ count1002 (baseVal q)) := rfl
theorem value1003 (q : Snake 81) : valuation q 1003 = decide (2 ≤ count1002 (baseVal q)) := rfl
theorem value1004 (q : Snake 81) : valuation q 1004 = decide (1 ≤ count1004 (baseVal q)) := rfl
theorem value1005 (q : Snake 81) : valuation q 1005 = decide (2 ≤ count1004 (baseVal q)) := rfl
theorem value1006 (q : Snake 81) : valuation q 1006 = decide (3 ≤ count1004 (baseVal q)) := rfl
theorem value1007 (q : Snake 81) : valuation q 1007 = decide (4 ≤ count1004 (baseVal q)) := rfl
theorem value1008 (q : Snake 81) : valuation q 1008 = decide (1 ≤ count1008 (baseVal q)) := rfl
theorem value1009 (q : Snake 81) : valuation q 1009 = decide (2 ≤ count1008 (baseVal q)) := rfl
theorem value1010 (q : Snake 81) : valuation q 1010 = decide (3 ≤ count1008 (baseVal q)) := rfl
theorem value1011 (q : Snake 81) : valuation q 1011 = decide (4 ≤ count1008 (baseVal q)) := rfl
theorem value1012 (q : Snake 81) : valuation q 1012 = decide (5 ≤ count1008 (baseVal q)) := rfl
theorem value1013 (q : Snake 81) : valuation q 1013 = decide (6 ≤ count1008 (baseVal q)) := rfl
theorem value1014 (q : Snake 81) : valuation q 1014 = decide (7 ≤ count1008 (baseVal q)) := rfl
theorem value1015 (q : Snake 81) : valuation q 1015 = decide (8 ≤ count1008 (baseVal q)) := rfl
theorem value1016 (q : Snake 81) : valuation q 1016 = decide (1 ≤ count1016 (baseVal q)) := rfl
theorem value1017 (q : Snake 81) : valuation q 1017 = decide (2 ≤ count1016 (baseVal q)) := rfl
theorem value1018 (q : Snake 81) : valuation q 1018 = decide (3 ≤ count1016 (baseVal q)) := rfl
theorem value1019 (q : Snake 81) : valuation q 1019 = decide (4 ≤ count1016 (baseVal q)) := rfl
theorem value1020 (q : Snake 81) : valuation q 1020 = decide (5 ≤ count1016 (baseVal q)) := rfl
theorem value1021 (q : Snake 81) : valuation q 1021 = decide (6 ≤ count1016 (baseVal q)) := rfl
theorem value1022 (q : Snake 81) : valuation q 1022 = decide (7 ≤ count1016 (baseVal q)) := rfl
theorem value1023 (q : Snake 81) : valuation q 1023 = decide (8 ≤ count1016 (baseVal q)) := rfl
theorem value1024 (q : Snake 81) : valuation q 1024 = decide (9 ≤ count1016 (baseVal q)) := rfl
theorem value1031 (q : Snake 81) : valuation q 1031 = decide (1 ≤ count1031 (baseVal q)) := rfl
theorem value1032 (q : Snake 81) : valuation q 1032 = decide (2 ≤ count1031 (baseVal q)) := rfl
theorem value1033 (q : Snake 81) : valuation q 1033 = decide (1 ≤ count1033 (baseVal q)) := rfl
theorem value1034 (q : Snake 81) : valuation q 1034 = decide (2 ≤ count1033 (baseVal q)) := rfl
theorem value1035 (q : Snake 81) : valuation q 1035 = decide (1 ≤ count1035 (baseVal q)) := rfl
theorem value1036 (q : Snake 81) : valuation q 1036 = decide (2 ≤ count1035 (baseVal q)) := rfl
theorem value1037 (q : Snake 81) : valuation q 1037 = decide (3 ≤ count1035 (baseVal q)) := rfl
theorem value1038 (q : Snake 81) : valuation q 1038 = decide (4 ≤ count1035 (baseVal q)) := rfl
theorem value1039 (q : Snake 81) : valuation q 1039 = decide (1 ≤ count1039 (baseVal q)) := rfl
theorem value1040 (q : Snake 81) : valuation q 1040 = decide (2 ≤ count1039 (baseVal q)) := rfl
theorem value1041 (q : Snake 81) : valuation q 1041 = decide (1 ≤ count1041 (baseVal q)) := rfl
theorem value1042 (q : Snake 81) : valuation q 1042 = decide (2 ≤ count1041 (baseVal q)) := rfl
theorem value1043 (q : Snake 81) : valuation q 1043 = decide (1 ≤ count1043 (baseVal q)) := rfl
theorem value1044 (q : Snake 81) : valuation q 1044 = decide (2 ≤ count1043 (baseVal q)) := rfl
theorem value1045 (q : Snake 81) : valuation q 1045 = decide (3 ≤ count1043 (baseVal q)) := rfl
theorem value1046 (q : Snake 81) : valuation q 1046 = decide (4 ≤ count1043 (baseVal q)) := rfl
theorem value1047 (q : Snake 81) : valuation q 1047 = decide (1 ≤ count1047 (baseVal q)) := rfl
theorem value1048 (q : Snake 81) : valuation q 1048 = decide (2 ≤ count1047 (baseVal q)) := rfl
theorem value1049 (q : Snake 81) : valuation q 1049 = decide (3 ≤ count1047 (baseVal q)) := rfl
theorem value1050 (q : Snake 81) : valuation q 1050 = decide (4 ≤ count1047 (baseVal q)) := rfl
theorem value1051 (q : Snake 81) : valuation q 1051 = decide (5 ≤ count1047 (baseVal q)) := rfl
theorem value1052 (q : Snake 81) : valuation q 1052 = decide (6 ≤ count1047 (baseVal q)) := rfl
theorem value1053 (q : Snake 81) : valuation q 1053 = decide (7 ≤ count1047 (baseVal q)) := rfl
theorem value1055 (q : Snake 81) : valuation q 1055 = decide (1 ≤ count1055 (baseVal q)) := rfl
theorem value1056 (q : Snake 81) : valuation q 1056 = decide (2 ≤ count1055 (baseVal q)) := rfl
theorem value1057 (q : Snake 81) : valuation q 1057 = decide (1 ≤ count1057 (baseVal q)) := rfl
theorem value1058 (q : Snake 81) : valuation q 1058 = decide (2 ≤ count1057 (baseVal q)) := rfl
theorem value1059 (q : Snake 81) : valuation q 1059 = decide (1 ≤ count1059 (baseVal q)) := rfl
theorem value1060 (q : Snake 81) : valuation q 1060 = decide (2 ≤ count1059 (baseVal q)) := rfl
theorem value1061 (q : Snake 81) : valuation q 1061 = decide (3 ≤ count1059 (baseVal q)) := rfl
theorem value1062 (q : Snake 81) : valuation q 1062 = decide (4 ≤ count1059 (baseVal q)) := rfl
theorem value1063 (q : Snake 81) : valuation q 1063 = decide (1 ≤ count1063 (baseVal q)) := rfl
theorem value1064 (q : Snake 81) : valuation q 1064 = decide (2 ≤ count1063 (baseVal q)) := rfl
theorem value1065 (q : Snake 81) : valuation q 1065 = decide (1 ≤ count1065 (baseVal q)) := rfl
theorem value1066 (q : Snake 81) : valuation q 1066 = decide (2 ≤ count1065 (baseVal q)) := rfl
theorem value1067 (q : Snake 81) : valuation q 1067 = decide (1 ≤ count1067 (baseVal q)) := rfl
theorem value1068 (q : Snake 81) : valuation q 1068 = decide (2 ≤ count1067 (baseVal q)) := rfl
theorem value1069 (q : Snake 81) : valuation q 1069 = decide (3 ≤ count1067 (baseVal q)) := rfl
theorem value1070 (q : Snake 81) : valuation q 1070 = decide (4 ≤ count1067 (baseVal q)) := rfl
theorem value1071 (q : Snake 81) : valuation q 1071 = decide (1 ≤ count1071 (baseVal q)) := rfl
theorem value1072 (q : Snake 81) : valuation q 1072 = decide (2 ≤ count1071 (baseVal q)) := rfl
theorem value1073 (q : Snake 81) : valuation q 1073 = decide (3 ≤ count1071 (baseVal q)) := rfl
theorem value1074 (q : Snake 81) : valuation q 1074 = decide (4 ≤ count1071 (baseVal q)) := rfl
theorem value1075 (q : Snake 81) : valuation q 1075 = decide (5 ≤ count1071 (baseVal q)) := rfl
theorem value1076 (q : Snake 81) : valuation q 1076 = decide (6 ≤ count1071 (baseVal q)) := rfl
theorem value1077 (q : Snake 81) : valuation q 1077 = decide (7 ≤ count1071 (baseVal q)) := rfl
theorem value1078 (q : Snake 81) : valuation q 1078 = decide (8 ≤ count1071 (baseVal q)) := rfl
theorem value1080 (q : Snake 81) : valuation q 1080 = decide (2 ≤ count1079 (baseVal q)) := rfl
theorem value1081 (q : Snake 81) : valuation q 1081 = decide (3 ≤ count1079 (baseVal q)) := rfl
theorem value1082 (q : Snake 81) : valuation q 1082 = decide (4 ≤ count1079 (baseVal q)) := rfl
theorem value1083 (q : Snake 81) : valuation q 1083 = decide (5 ≤ count1079 (baseVal q)) := rfl
theorem value1084 (q : Snake 81) : valuation q 1084 = decide (6 ≤ count1079 (baseVal q)) := rfl
theorem value1085 (q : Snake 81) : valuation q 1085 = decide (7 ≤ count1079 (baseVal q)) := rfl
theorem value1086 (q : Snake 81) : valuation q 1086 = decide (8 ≤ count1079 (baseVal q)) := rfl
theorem value1087 (q : Snake 81) : valuation q 1087 = decide (9 ≤ count1079 (baseVal q)) := rfl
theorem value1088 (q : Snake 81) : valuation q 1088 = decide (10 ≤ count1079 (baseVal q)) := rfl
theorem value1089 (q : Snake 81) : valuation q 1089 = decide (11 ≤ count1079 (baseVal q)) := rfl
theorem value1090 (q : Snake 81) : valuation q 1090 = decide (12 ≤ count1079 (baseVal q)) := rfl
theorem value1100 (q : Snake 81) : valuation q 1100 = decide (6 ≤ count1095 (baseVal q)) := rfl
theorem value1101 (q : Snake 81) : valuation q 1101 = decide (7 ≤ count1095 (baseVal q)) := rfl
theorem value1102 (q : Snake 81) : valuation q 1102 = decide (8 ≤ count1095 (baseVal q)) := rfl
theorem value1103 (q : Snake 81) : valuation q 1103 = decide (9 ≤ count1095 (baseVal q)) := rfl
theorem value1104 (q : Snake 81) : valuation q 1104 = decide (10 ≤ count1095 (baseVal q)) := rfl
theorem value1105 (q : Snake 81) : valuation q 1105 = decide (11 ≤ count1095 (baseVal q)) := rfl
theorem value1106 (q : Snake 81) : valuation q 1106 = decide (12 ≤ count1095 (baseVal q)) := rfl
theorem value1107 (q : Snake 81) : valuation q 1107 = decide (13 ≤ count1095 (baseVal q)) := rfl
theorem value1108 (q : Snake 81) : valuation q 1108 = decide (14 ≤ count1095 (baseVal q)) := rfl
theorem value1109 (q : Snake 81) : valuation q 1109 = decide (15 ≤ count1095 (baseVal q)) := rfl
theorem value1136 (q : Snake 81) : valuation q 1136 = decide (21 ≤ count1116 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (1 ≤ count1492 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (1 ≤ count1496 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (1 ≤ count1500 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (1 ≤ count1507 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (1 ≤ count1509 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (1 ≤ count1511 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (2 ≤ count1511 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (1 ≤ count1515 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (1 ≤ count1517 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (1 ≤ count1519 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (2 ≤ count1519 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (3 ≤ count1523 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (4 ≤ count1531 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (1 ≤ count1548 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (1 ≤ count1550 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (1 ≤ count1554 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (1 ≤ count1558 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (2 ≤ count1562 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (1 ≤ count1570 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (2 ≤ count1570 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (1 ≤ count1572 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (2 ≤ count1574 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (3 ≤ count1574 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (1 ≤ count1578 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (2 ≤ count1578 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (2 ≤ count1582 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (3 ≤ count1582 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (5 ≤ count1586 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (7 ≤ count1594 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (11 ≤ count1610 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (1 ≤ count1632 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (1 ≤ count1634 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (1 ≤ count1637 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (1 ≤ count1639 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (1 ≤ count1641 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (1 ≤ count1645 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (1 ≤ count1652 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (1 ≤ count1656 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (1 ≤ count1660 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (1 ≤ count1662 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (1 ≤ count1664 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (2 ≤ count1664 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (2 ≤ count1668 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (3 ≤ count1668 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (3 ≤ count1676 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (4 ≤ count1676 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (1 ≤ count1691 (baseVal q)) := rfl
theorem value1693 (q : Snake 81) : valuation q 1693 = decide (1 ≤ count1693 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (2 ≤ count1695 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (1 ≤ count1699 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (1 ≤ count1701 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (1 ≤ count1703 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (2 ≤ count1703 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (3 ≤ count1707 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (4 ≤ count1707 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (2 ≤ count1717 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (2 ≤ count1719 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (1 ≤ count1723 (baseVal q)) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (2 ≤ count1723 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (1 ≤ count1725 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (2 ≤ count1727 (baseVal q)) := rfl
theorem value1729 (q : Snake 81) : valuation q 1729 = decide (3 ≤ count1727 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (4 ≤ count1731 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (5 ≤ count1731 (baseVal q)) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (7 ≤ count1739 (baseVal q)) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (8 ≤ count1739 (baseVal q)) := rfl
theorem value1765 (q : Snake 81) : valuation q 1765 = decide (11 ≤ count1755 (baseVal q)) := rfl
theorem value1798 (q : Snake 81) : valuation q 1798 = decide (22 ≤ count1777 (baseVal q)) := rfl
theorem meaningNeg123 (b : Nat → Bool) : literal (valuationOf b) (-123) = decide (1 ≤ countLit b [-123]) := by
  change literal b (-123) = decide (1 ≤ countLit b [-123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-123) <;> decide
theorem meaningNeg122 (b : Nat → Bool) : literal (valuationOf b) (-122) = decide (1 ≤ countLit b [-122]) := by
  change literal b (-122) = decide (1 ≤ countLit b [-122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-122) <;> decide
theorem meaningNeg121 (b : Nat → Bool) : literal (valuationOf b) (-121) = decide (1 ≤ countLit b [-121]) := by
  change literal b (-121) = decide (1 ≤ countLit b [-121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-121) <;> decide
theorem meaningNeg119 (b : Nat → Bool) : literal (valuationOf b) (-119) = decide (1 ≤ countLit b [-119]) := by
  change literal b (-119) = decide (1 ≤ countLit b [-119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-119) <;> decide
theorem meaningNeg118 (b : Nat → Bool) : literal (valuationOf b) (-118) = decide (1 ≤ countLit b [-118]) := by
  change literal b (-118) = decide (1 ≤ countLit b [-118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-118) <;> decide
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
theorem meaningNeg115 (b : Nat → Bool) : literal (valuationOf b) (-115) = decide (1 ≤ countLit b [-115]) := by
  change literal b (-115) = decide (1 ≤ countLit b [-115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-115) <;> decide
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
theorem meaningNeg106 (b : Nat → Bool) : literal (valuationOf b) (-106) = decide (1 ≤ countLit b [-106]) := by
  change literal b (-106) = decide (1 ≤ countLit b [-106])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-106) <;> decide
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
theorem meaningNeg102 (b : Nat → Bool) : literal (valuationOf b) (-102) = decide (1 ≤ countLit b [-102]) := by
  change literal b (-102) = decide (1 ≤ countLit b [-102])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-102) <;> decide
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
theorem meaningNeg98 (b : Nat → Bool) : literal (valuationOf b) (-98) = decide (1 ≤ countLit b [-98]) := by
  change literal b (-98) = decide (1 ≤ countLit b [-98])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-98) <;> decide
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
theorem meaningNeg53 (b : Nat → Bool) : literal (valuationOf b) (-53) = decide (1 ≤ countLit b [-53]) := by
  change literal b (-53) = decide (1 ≤ countLit b [-53])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-53) <;> decide
theorem meaningNeg51 (b : Nat → Bool) : literal (valuationOf b) (-51) = decide (1 ≤ countLit b [-51]) := by
  change literal b (-51) = decide (1 ≤ countLit b [-51])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-51) <;> decide
theorem meaningNeg50 (b : Nat → Bool) : literal (valuationOf b) (-50) = decide (1 ≤ countLit b [-50]) := by
  change literal b (-50) = decide (1 ≤ countLit b [-50])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-50) <;> decide
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
theorem meaningNeg43 (b : Nat → Bool) : literal (valuationOf b) (-43) = decide (1 ≤ countLit b [-43]) := by
  change literal b (-43) = decide (1 ≤ countLit b [-43])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-43) <;> decide
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
theorem meaningNeg10 (b : Nat → Bool) : literal (valuationOf b) (-10) = decide (1 ≤ countLit b [-10]) := by
  change literal b (-10) = decide (1 ≤ countLit b [-10])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-10) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
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
theorem meaning142 (b : Nat → Bool) : literal (valuationOf b) (142) = decide (1 ≤ countLit b [142]) := by
  change literal b (142) = decide (1 ≤ countLit b [142])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (142) <;> decide
theorem meaning146 (b : Nat → Bool) : literal (valuationOf b) (146) = decide (1 ≤ countLit b [146]) := by
  change literal b (146) = decide (1 ≤ countLit b [146])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (146) <;> decide
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
theorem meaning153 (b : Nat → Bool) : literal (valuationOf b) (153) = decide (1 ≤ countLit b [153]) := by
  change literal b (153) = decide (1 ≤ countLit b [153])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (153) <;> decide
theorem meaning154 (b : Nat → Bool) : literal (valuationOf b) (154) = decide (1 ≤ countLit b [154]) := by
  change literal b (154) = decide (1 ≤ countLit b [154])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (154) <;> decide
theorem meaning155 (b : Nat → Bool) : literal (valuationOf b) (155) = decide (1 ≤ countLit b [155]) := by
  change literal b (155) = decide (1 ≤ countLit b [155])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (155) <;> decide
theorem meaning158 (b : Nat → Bool) : literal (valuationOf b) (158) = decide (1 ≤ countLit b [158]) := by
  change literal b (158) = decide (1 ≤ countLit b [158])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (158) <;> decide
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
theorem meaning164 (b : Nat → Bool) : literal (valuationOf b) (164) = decide (1 ≤ countLit b [164]) := by
  change literal b (164) = decide (1 ≤ countLit b [164])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (164) <;> decide
theorem meaning165 (b : Nat → Bool) : literal (valuationOf b) (165) = decide (1 ≤ countLit b [165]) := by
  change literal b (165) = decide (1 ≤ countLit b [165])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (165) <;> decide
theorem meaning168 (b : Nat → Bool) : literal (valuationOf b) (168) = decide (1 ≤ countLit b [168]) := by
  change literal b (168) = decide (1 ≤ countLit b [168])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (168) <;> decide
theorem meaning171 (b : Nat → Bool) : literal (valuationOf b) (171) = decide (1 ≤ countLit b [171]) := by
  change literal b (171) = decide (1 ≤ countLit b [171])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (171) <;> decide
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
theorem meaning179 (b : Nat → Bool) : literal (valuationOf b) (179) = decide (1 ≤ countLit b [179]) := by
  change literal b (179) = decide (1 ≤ countLit b [179])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (179) <;> decide
theorem meaning183 (b : Nat → Bool) : literal (valuationOf b) (183) = decide (1 ≤ countLit b [183]) := by
  change literal b (183) = decide (1 ≤ countLit b [183])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (183) <;> decide
theorem meaning185 (b : Nat → Bool) : literal (valuationOf b) (185) = decide (1 ≤ countLit b [185]) := by
  change literal b (185) = decide (1 ≤ countLit b [185])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (185) <;> decide
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
theorem meaning189 (b : Nat → Bool) : literal (valuationOf b) (189) = decide (1 ≤ countLit b [189]) := by
  change literal b (189) = decide (1 ≤ countLit b [189])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (189) <;> decide
theorem meaning190 (b : Nat → Bool) : literal (valuationOf b) (190) = decide (1 ≤ countLit b [190]) := by
  change literal b (190) = decide (1 ≤ countLit b [190])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (190) <;> decide
theorem meaning196 (b : Nat → Bool) : literal (valuationOf b) (196) = decide (1 ≤ countLit b [196]) := by
  change literal b (196) = decide (1 ≤ countLit b [196])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (196) <;> decide
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) (201) = decide (1 ≤ countLit b [201]) := by
  change literal b (201) = decide (1 ≤ countLit b [201])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (201) <;> decide
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) (203) = decide (1 ≤ countLit b [203]) := by
  change literal b (203) = decide (1 ≤ countLit b [203])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (203) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning207 (b : Nat → Bool) : literal (valuationOf b) (207) = decide (1 ≤ countLit b [207]) := by
  change literal b (207) = decide (1 ≤ countLit b [207])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (207) <;> decide
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) (219) = decide (1 ≤ countLit b [219]) := by
  change literal b (219) = decide (1 ≤ countLit b [219])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (219) <;> decide
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) (221) = decide (1 ≤ countLit b [221]) := by
  change literal b (221) = decide (1 ≤ countLit b [221])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (221) <;> decide
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) (222) = decide (1 ≤ countLit b [222]) := by
  change literal b (222) = decide (1 ≤ countLit b [222])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (222) <;> decide
theorem meaning226 (b : Nat → Bool) : literal (valuationOf b) (226) = decide (1 ≤ countLit b [226]) := by
  change literal b (226) = decide (1 ≤ countLit b [226])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (226) <;> decide
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) (230) = decide (1 ≤ countLit b [230]) := by
  change literal b (230) = decide (1 ≤ countLit b [230])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (230) <;> decide
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) (233) = decide (1 ≤ countLit b [233]) := by
  change literal b (233) = decide (1 ≤ countLit b [233])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (233) <;> decide
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) (242) = decide (1 ≤ countLit b [242]) := by
  change literal b (242) = decide (1 ≤ countLit b [242])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (242) <;> decide
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) (243) = decide (1 ≤ countLit b [243]) := by
  change literal b (243) = decide (1 ≤ countLit b [243])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (243) <;> decide
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning274 (b : Nat → Bool) : literal (valuationOf b) 274 = decide (2 ≤ count273 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning332 (b : Nat → Bool) : literal (valuationOf b) 332 = decide (2 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning364 (b : Nat → Bool) : literal (valuationOf b) 364 = decide (2 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning366 (b : Nat → Bool) : literal (valuationOf b) 366 = decide (2 ≤ count365 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning422 (b : Nat → Bool) : literal (valuationOf b) 422 = decide (2 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning424 (b : Nat → Bool) : literal (valuationOf b) 424 = decide (2 ≤ count423 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning452 (b : Nat → Bool) : literal (valuationOf b) 452 = decide (2 ≤ count451 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning479 (b : Nat → Bool) : literal (valuationOf b) 479 = decide (1 ≤ count479 b) := rfl
theorem meaning480 (b : Nat → Bool) : literal (valuationOf b) 480 = decide (2 ≤ count479 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning482 (b : Nat → Bool) : literal (valuationOf b) 482 = decide (2 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning484 (b : Nat → Bool) : literal (valuationOf b) 484 = decide (2 ≤ count483 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning486 (b : Nat → Bool) : literal (valuationOf b) 486 = decide (2 ≤ count485 b) := rfl
theorem meaning488 (b : Nat → Bool) : literal (valuationOf b) 488 = decide (2 ≤ count487 b) := rfl
theorem meaning834 (b : Nat → Bool) : literal (valuationOf b) 834 = decide (2 ≤ count833 b) := rfl
theorem meaning836 (b : Nat → Bool) : literal (valuationOf b) 836 = decide (2 ≤ count835 b) := rfl
theorem meaning837 (b : Nat → Bool) : literal (valuationOf b) 837 = decide (3 ≤ count835 b) := rfl
theorem meaning838 (b : Nat → Bool) : literal (valuationOf b) 838 = decide (1 ≤ count838 b) := rfl
theorem meaning839 (b : Nat → Bool) : literal (valuationOf b) 839 = decide (2 ≤ count838 b) := rfl
theorem meaning840 (b : Nat → Bool) : literal (valuationOf b) 840 = decide (1 ≤ count840 b) := rfl
theorem meaning841 (b : Nat → Bool) : literal (valuationOf b) 841 = decide (2 ≤ count840 b) := rfl
theorem meaning842 (b : Nat → Bool) : literal (valuationOf b) 842 = decide (1 ≤ count842 b) := rfl
theorem meaning843 (b : Nat → Bool) : literal (valuationOf b) 843 = decide (2 ≤ count842 b) := rfl
theorem meaning844 (b : Nat → Bool) : literal (valuationOf b) 844 = decide (3 ≤ count842 b) := rfl
theorem meaning848 (b : Nat → Bool) : literal (valuationOf b) 848 = decide (3 ≤ count846 b) := rfl
theorem meaning849 (b : Nat → Bool) : literal (valuationOf b) 849 = decide (4 ≤ count846 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (5 ≤ count846 b) := rfl
theorem meaning851 (b : Nat → Bool) : literal (valuationOf b) 851 = decide (6 ≤ count846 b) := rfl
theorem meaning853 (b : Nat → Bool) : literal (valuationOf b) 853 = decide (1 ≤ count853 b) := rfl
theorem meaning854 (b : Nat → Bool) : literal (valuationOf b) 854 = decide (2 ≤ count853 b) := rfl
theorem meaning855 (b : Nat → Bool) : literal (valuationOf b) 855 = decide (1 ≤ count855 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (1 ≤ count857 b) := rfl
theorem meaning858 (b : Nat → Bool) : literal (valuationOf b) 858 = decide (2 ≤ count857 b) := rfl
theorem meaning859 (b : Nat → Bool) : literal (valuationOf b) 859 = decide (3 ≤ count857 b) := rfl
theorem meaning861 (b : Nat → Bool) : literal (valuationOf b) 861 = decide (1 ≤ count861 b) := rfl
theorem meaning862 (b : Nat → Bool) : literal (valuationOf b) 862 = decide (2 ≤ count861 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (1 ≤ count863 b) := rfl
theorem meaning864 (b : Nat → Bool) : literal (valuationOf b) 864 = decide (2 ≤ count863 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (1 ≤ count865 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (2 ≤ count865 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (3 ≤ count865 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (4 ≤ count865 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (1 ≤ count869 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (2 ≤ count869 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (3 ≤ count869 b) := rfl
theorem meaning872 (b : Nat → Bool) : literal (valuationOf b) 872 = decide (4 ≤ count869 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (5 ≤ count869 b) := rfl
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (3 ≤ count877 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (4 ≤ count877 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (5 ≤ count877 b) := rfl
theorem meaning882 (b : Nat → Bool) : literal (valuationOf b) 882 = decide (6 ≤ count877 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (7 ≤ count877 b) := rfl
theorem meaning884 (b : Nat → Bool) : literal (valuationOf b) 884 = decide (8 ≤ count877 b) := rfl
theorem meaning892 (b : Nat → Bool) : literal (valuationOf b) 892 = decide (1 ≤ count892 b) := rfl
theorem meaning893 (b : Nat → Bool) : literal (valuationOf b) 893 = decide (2 ≤ count892 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (1 ≤ count894 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (2 ≤ count894 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (3 ≤ count894 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (1 ≤ count897 b) := rfl
theorem meaning898 (b : Nat → Bool) : literal (valuationOf b) 898 = decide (2 ≤ count897 b) := rfl
theorem meaning899 (b : Nat → Bool) : literal (valuationOf b) 899 = decide (1 ≤ count899 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (2 ≤ count899 b) := rfl
theorem meaning901 (b : Nat → Bool) : literal (valuationOf b) 901 = decide (1 ≤ count901 b) := rfl
theorem meaning902 (b : Nat → Bool) : literal (valuationOf b) 902 = decide (2 ≤ count901 b) := rfl
theorem meaning903 (b : Nat → Bool) : literal (valuationOf b) 903 = decide (3 ≤ count901 b) := rfl
theorem meaning905 (b : Nat → Bool) : literal (valuationOf b) 905 = decide (1 ≤ count905 b) := rfl
theorem meaning906 (b : Nat → Bool) : literal (valuationOf b) 906 = decide (2 ≤ count905 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (3 ≤ count905 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (4 ≤ count905 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (5 ≤ count905 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (1 ≤ count912 b) := rfl
theorem meaning913 (b : Nat → Bool) : literal (valuationOf b) 913 = decide (2 ≤ count912 b) := rfl
theorem meaning914 (b : Nat → Bool) : literal (valuationOf b) 914 = decide (1 ≤ count914 b) := rfl
theorem meaning915 (b : Nat → Bool) : literal (valuationOf b) 915 = decide (2 ≤ count914 b) := rfl
theorem meaning916 (b : Nat → Bool) : literal (valuationOf b) 916 = decide (1 ≤ count916 b) := rfl
theorem meaning917 (b : Nat → Bool) : literal (valuationOf b) 917 = decide (2 ≤ count916 b) := rfl
theorem meaning918 (b : Nat → Bool) : literal (valuationOf b) 918 = decide (3 ≤ count916 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (4 ≤ count916 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (1 ≤ count920 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (2 ≤ count920 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (1 ≤ count922 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (2 ≤ count922 b) := rfl
theorem meaning924 (b : Nat → Bool) : literal (valuationOf b) 924 = decide (1 ≤ count924 b) := rfl
theorem meaning925 (b : Nat → Bool) : literal (valuationOf b) 925 = decide (2 ≤ count924 b) := rfl
theorem meaning926 (b : Nat → Bool) : literal (valuationOf b) 926 = decide (3 ≤ count924 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (4 ≤ count924 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (1 ≤ count928 b) := rfl
theorem meaning929 (b : Nat → Bool) : literal (valuationOf b) 929 = decide (2 ≤ count928 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (3 ≤ count928 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (4 ≤ count928 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (5 ≤ count928 b) := rfl
theorem meaning933 (b : Nat → Bool) : literal (valuationOf b) 933 = decide (6 ≤ count928 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (2 ≤ count936 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (3 ≤ count936 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (4 ≤ count936 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (5 ≤ count936 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (6 ≤ count936 b) := rfl
theorem meaning942 (b : Nat → Bool) : literal (valuationOf b) 942 = decide (7 ≤ count936 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (8 ≤ count936 b) := rfl
theorem meaning944 (b : Nat → Bool) : literal (valuationOf b) 944 = decide (9 ≤ count936 b) := rfl
theorem meaning945 (b : Nat → Bool) : literal (valuationOf b) 945 = decide (10 ≤ count936 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (6 ≤ count951 b) := rfl
theorem meaning957 (b : Nat → Bool) : literal (valuationOf b) 957 = decide (7 ≤ count951 b) := rfl
theorem meaning958 (b : Nat → Bool) : literal (valuationOf b) 958 = decide (8 ≤ count951 b) := rfl
theorem meaning959 (b : Nat → Bool) : literal (valuationOf b) 959 = decide (9 ≤ count951 b) := rfl
theorem meaning960 (b : Nat → Bool) : literal (valuationOf b) 960 = decide (10 ≤ count951 b) := rfl
theorem meaning961 (b : Nat → Bool) : literal (valuationOf b) 961 = decide (11 ≤ count951 b) := rfl
theorem meaning962 (b : Nat → Bool) : literal (valuationOf b) 962 = decide (12 ≤ count951 b) := rfl
theorem meaning963 (b : Nat → Bool) : literal (valuationOf b) 963 = decide (13 ≤ count951 b) := rfl
theorem meaning964 (b : Nat → Bool) : literal (valuationOf b) 964 = decide (14 ≤ count951 b) := rfl
theorem meaning965 (b : Nat → Bool) : literal (valuationOf b) 965 = decide (15 ≤ count951 b) := rfl
theorem meaning972 (b : Nat → Bool) : literal (valuationOf b) 972 = decide (1 ≤ count972 b) := rfl
theorem meaning973 (b : Nat → Bool) : literal (valuationOf b) 973 = decide (2 ≤ count972 b) := rfl
theorem meaning974 (b : Nat → Bool) : literal (valuationOf b) 974 = decide (1 ≤ count974 b) := rfl
theorem meaning975 (b : Nat → Bool) : literal (valuationOf b) 975 = decide (2 ≤ count974 b) := rfl
theorem meaning976 (b : Nat → Bool) : literal (valuationOf b) 976 = decide (3 ≤ count974 b) := rfl
theorem meaning977 (b : Nat → Bool) : literal (valuationOf b) 977 = decide (1 ≤ count977 b) := rfl
theorem meaning978 (b : Nat → Bool) : literal (valuationOf b) 978 = decide (2 ≤ count977 b) := rfl
theorem meaning979 (b : Nat → Bool) : literal (valuationOf b) 979 = decide (1 ≤ count979 b) := rfl
theorem meaning980 (b : Nat → Bool) : literal (valuationOf b) 980 = decide (2 ≤ count979 b) := rfl
theorem meaning981 (b : Nat → Bool) : literal (valuationOf b) 981 = decide (1 ≤ count981 b) := rfl
theorem meaning982 (b : Nat → Bool) : literal (valuationOf b) 982 = decide (2 ≤ count981 b) := rfl
theorem meaning983 (b : Nat → Bool) : literal (valuationOf b) 983 = decide (3 ≤ count981 b) := rfl
theorem meaning985 (b : Nat → Bool) : literal (valuationOf b) 985 = decide (1 ≤ count985 b) := rfl
theorem meaning986 (b : Nat → Bool) : literal (valuationOf b) 986 = decide (2 ≤ count985 b) := rfl
theorem meaning987 (b : Nat → Bool) : literal (valuationOf b) 987 = decide (3 ≤ count985 b) := rfl
theorem meaning988 (b : Nat → Bool) : literal (valuationOf b) 988 = decide (4 ≤ count985 b) := rfl
theorem meaning989 (b : Nat → Bool) : literal (valuationOf b) 989 = decide (5 ≤ count985 b) := rfl
theorem meaning992 (b : Nat → Bool) : literal (valuationOf b) 992 = decide (1 ≤ count992 b) := rfl
theorem meaning993 (b : Nat → Bool) : literal (valuationOf b) 993 = decide (2 ≤ count992 b) := rfl
theorem meaning994 (b : Nat → Bool) : literal (valuationOf b) 994 = decide (1 ≤ count994 b) := rfl
theorem meaning995 (b : Nat → Bool) : literal (valuationOf b) 995 = decide (2 ≤ count994 b) := rfl
theorem meaning996 (b : Nat → Bool) : literal (valuationOf b) 996 = decide (1 ≤ count996 b) := rfl
theorem meaning997 (b : Nat → Bool) : literal (valuationOf b) 997 = decide (2 ≤ count996 b) := rfl
theorem meaning998 (b : Nat → Bool) : literal (valuationOf b) 998 = decide (3 ≤ count996 b) := rfl
theorem meaning999 (b : Nat → Bool) : literal (valuationOf b) 999 = decide (4 ≤ count996 b) := rfl
theorem meaning1000 (b : Nat → Bool) : literal (valuationOf b) 1000 = decide (1 ≤ count1000 b) := rfl
theorem meaning1001 (b : Nat → Bool) : literal (valuationOf b) 1001 = decide (2 ≤ count1000 b) := rfl
theorem meaning1002 (b : Nat → Bool) : literal (valuationOf b) 1002 = decide (1 ≤ count1002 b) := rfl
theorem meaning1003 (b : Nat → Bool) : literal (valuationOf b) 1003 = decide (2 ≤ count1002 b) := rfl
theorem meaning1004 (b : Nat → Bool) : literal (valuationOf b) 1004 = decide (1 ≤ count1004 b) := rfl
theorem meaning1005 (b : Nat → Bool) : literal (valuationOf b) 1005 = decide (2 ≤ count1004 b) := rfl
theorem meaning1006 (b : Nat → Bool) : literal (valuationOf b) 1006 = decide (3 ≤ count1004 b) := rfl
theorem meaning1007 (b : Nat → Bool) : literal (valuationOf b) 1007 = decide (4 ≤ count1004 b) := rfl
theorem meaning1008 (b : Nat → Bool) : literal (valuationOf b) 1008 = decide (1 ≤ count1008 b) := rfl
theorem meaning1009 (b : Nat → Bool) : literal (valuationOf b) 1009 = decide (2 ≤ count1008 b) := rfl
theorem meaning1010 (b : Nat → Bool) : literal (valuationOf b) 1010 = decide (3 ≤ count1008 b) := rfl
theorem meaning1011 (b : Nat → Bool) : literal (valuationOf b) 1011 = decide (4 ≤ count1008 b) := rfl
theorem meaning1012 (b : Nat → Bool) : literal (valuationOf b) 1012 = decide (5 ≤ count1008 b) := rfl
theorem meaning1013 (b : Nat → Bool) : literal (valuationOf b) 1013 = decide (6 ≤ count1008 b) := rfl
theorem meaning1014 (b : Nat → Bool) : literal (valuationOf b) 1014 = decide (7 ≤ count1008 b) := rfl
theorem meaning1015 (b : Nat → Bool) : literal (valuationOf b) 1015 = decide (8 ≤ count1008 b) := rfl
theorem meaning1016 (b : Nat → Bool) : literal (valuationOf b) 1016 = decide (1 ≤ count1016 b) := rfl
theorem meaning1017 (b : Nat → Bool) : literal (valuationOf b) 1017 = decide (2 ≤ count1016 b) := rfl
theorem meaning1018 (b : Nat → Bool) : literal (valuationOf b) 1018 = decide (3 ≤ count1016 b) := rfl
theorem meaning1019 (b : Nat → Bool) : literal (valuationOf b) 1019 = decide (4 ≤ count1016 b) := rfl
theorem meaning1020 (b : Nat → Bool) : literal (valuationOf b) 1020 = decide (5 ≤ count1016 b) := rfl
theorem meaning1021 (b : Nat → Bool) : literal (valuationOf b) 1021 = decide (6 ≤ count1016 b) := rfl
theorem meaning1022 (b : Nat → Bool) : literal (valuationOf b) 1022 = decide (7 ≤ count1016 b) := rfl
theorem meaning1023 (b : Nat → Bool) : literal (valuationOf b) 1023 = decide (8 ≤ count1016 b) := rfl
theorem meaning1024 (b : Nat → Bool) : literal (valuationOf b) 1024 = decide (9 ≤ count1016 b) := rfl
theorem meaning1031 (b : Nat → Bool) : literal (valuationOf b) 1031 = decide (1 ≤ count1031 b) := rfl
theorem meaning1032 (b : Nat → Bool) : literal (valuationOf b) 1032 = decide (2 ≤ count1031 b) := rfl
theorem meaning1033 (b : Nat → Bool) : literal (valuationOf b) 1033 = decide (1 ≤ count1033 b) := rfl
theorem meaning1034 (b : Nat → Bool) : literal (valuationOf b) 1034 = decide (2 ≤ count1033 b) := rfl
theorem meaning1035 (b : Nat → Bool) : literal (valuationOf b) 1035 = decide (1 ≤ count1035 b) := rfl
theorem meaning1036 (b : Nat → Bool) : literal (valuationOf b) 1036 = decide (2 ≤ count1035 b) := rfl
theorem meaning1037 (b : Nat → Bool) : literal (valuationOf b) 1037 = decide (3 ≤ count1035 b) := rfl
theorem meaning1038 (b : Nat → Bool) : literal (valuationOf b) 1038 = decide (4 ≤ count1035 b) := rfl
theorem meaning1039 (b : Nat → Bool) : literal (valuationOf b) 1039 = decide (1 ≤ count1039 b) := rfl
theorem meaning1040 (b : Nat → Bool) : literal (valuationOf b) 1040 = decide (2 ≤ count1039 b) := rfl
theorem meaning1041 (b : Nat → Bool) : literal (valuationOf b) 1041 = decide (1 ≤ count1041 b) := rfl
theorem meaning1042 (b : Nat → Bool) : literal (valuationOf b) 1042 = decide (2 ≤ count1041 b) := rfl
theorem meaning1043 (b : Nat → Bool) : literal (valuationOf b) 1043 = decide (1 ≤ count1043 b) := rfl
theorem meaning1044 (b : Nat → Bool) : literal (valuationOf b) 1044 = decide (2 ≤ count1043 b) := rfl
theorem meaning1045 (b : Nat → Bool) : literal (valuationOf b) 1045 = decide (3 ≤ count1043 b) := rfl
theorem meaning1046 (b : Nat → Bool) : literal (valuationOf b) 1046 = decide (4 ≤ count1043 b) := rfl
theorem meaning1047 (b : Nat → Bool) : literal (valuationOf b) 1047 = decide (1 ≤ count1047 b) := rfl
theorem meaning1048 (b : Nat → Bool) : literal (valuationOf b) 1048 = decide (2 ≤ count1047 b) := rfl
theorem meaning1049 (b : Nat → Bool) : literal (valuationOf b) 1049 = decide (3 ≤ count1047 b) := rfl
theorem meaning1050 (b : Nat → Bool) : literal (valuationOf b) 1050 = decide (4 ≤ count1047 b) := rfl
theorem meaning1051 (b : Nat → Bool) : literal (valuationOf b) 1051 = decide (5 ≤ count1047 b) := rfl
theorem meaning1052 (b : Nat → Bool) : literal (valuationOf b) 1052 = decide (6 ≤ count1047 b) := rfl
theorem meaning1053 (b : Nat → Bool) : literal (valuationOf b) 1053 = decide (7 ≤ count1047 b) := rfl
theorem meaning1055 (b : Nat → Bool) : literal (valuationOf b) 1055 = decide (1 ≤ count1055 b) := rfl
theorem meaning1056 (b : Nat → Bool) : literal (valuationOf b) 1056 = decide (2 ≤ count1055 b) := rfl
theorem meaning1057 (b : Nat → Bool) : literal (valuationOf b) 1057 = decide (1 ≤ count1057 b) := rfl
theorem meaning1058 (b : Nat → Bool) : literal (valuationOf b) 1058 = decide (2 ≤ count1057 b) := rfl
theorem meaning1059 (b : Nat → Bool) : literal (valuationOf b) 1059 = decide (1 ≤ count1059 b) := rfl
theorem meaning1060 (b : Nat → Bool) : literal (valuationOf b) 1060 = decide (2 ≤ count1059 b) := rfl
theorem meaning1061 (b : Nat → Bool) : literal (valuationOf b) 1061 = decide (3 ≤ count1059 b) := rfl
theorem meaning1062 (b : Nat → Bool) : literal (valuationOf b) 1062 = decide (4 ≤ count1059 b) := rfl
theorem meaning1063 (b : Nat → Bool) : literal (valuationOf b) 1063 = decide (1 ≤ count1063 b) := rfl
theorem meaning1064 (b : Nat → Bool) : literal (valuationOf b) 1064 = decide (2 ≤ count1063 b) := rfl
theorem meaning1065 (b : Nat → Bool) : literal (valuationOf b) 1065 = decide (1 ≤ count1065 b) := rfl
theorem meaning1066 (b : Nat → Bool) : literal (valuationOf b) 1066 = decide (2 ≤ count1065 b) := rfl
theorem meaning1067 (b : Nat → Bool) : literal (valuationOf b) 1067 = decide (1 ≤ count1067 b) := rfl
theorem meaning1068 (b : Nat → Bool) : literal (valuationOf b) 1068 = decide (2 ≤ count1067 b) := rfl
theorem meaning1069 (b : Nat → Bool) : literal (valuationOf b) 1069 = decide (3 ≤ count1067 b) := rfl
theorem meaning1070 (b : Nat → Bool) : literal (valuationOf b) 1070 = decide (4 ≤ count1067 b) := rfl
theorem meaning1071 (b : Nat → Bool) : literal (valuationOf b) 1071 = decide (1 ≤ count1071 b) := rfl
theorem meaning1072 (b : Nat → Bool) : literal (valuationOf b) 1072 = decide (2 ≤ count1071 b) := rfl
theorem meaning1073 (b : Nat → Bool) : literal (valuationOf b) 1073 = decide (3 ≤ count1071 b) := rfl
theorem meaning1074 (b : Nat → Bool) : literal (valuationOf b) 1074 = decide (4 ≤ count1071 b) := rfl
theorem meaning1075 (b : Nat → Bool) : literal (valuationOf b) 1075 = decide (5 ≤ count1071 b) := rfl
theorem meaning1076 (b : Nat → Bool) : literal (valuationOf b) 1076 = decide (6 ≤ count1071 b) := rfl
theorem meaning1077 (b : Nat → Bool) : literal (valuationOf b) 1077 = decide (7 ≤ count1071 b) := rfl
theorem meaning1078 (b : Nat → Bool) : literal (valuationOf b) 1078 = decide (8 ≤ count1071 b) := rfl
theorem meaning1080 (b : Nat → Bool) : literal (valuationOf b) 1080 = decide (2 ≤ count1079 b) := rfl
theorem meaning1081 (b : Nat → Bool) : literal (valuationOf b) 1081 = decide (3 ≤ count1079 b) := rfl
theorem meaning1082 (b : Nat → Bool) : literal (valuationOf b) 1082 = decide (4 ≤ count1079 b) := rfl
theorem meaning1083 (b : Nat → Bool) : literal (valuationOf b) 1083 = decide (5 ≤ count1079 b) := rfl
theorem meaning1084 (b : Nat → Bool) : literal (valuationOf b) 1084 = decide (6 ≤ count1079 b) := rfl
theorem meaning1085 (b : Nat → Bool) : literal (valuationOf b) 1085 = decide (7 ≤ count1079 b) := rfl
theorem meaning1086 (b : Nat → Bool) : literal (valuationOf b) 1086 = decide (8 ≤ count1079 b) := rfl
theorem meaning1087 (b : Nat → Bool) : literal (valuationOf b) 1087 = decide (9 ≤ count1079 b) := rfl
theorem meaning1088 (b : Nat → Bool) : literal (valuationOf b) 1088 = decide (10 ≤ count1079 b) := rfl
theorem meaning1089 (b : Nat → Bool) : literal (valuationOf b) 1089 = decide (11 ≤ count1079 b) := rfl
theorem meaning1090 (b : Nat → Bool) : literal (valuationOf b) 1090 = decide (12 ≤ count1079 b) := rfl
theorem meaning1100 (b : Nat → Bool) : literal (valuationOf b) 1100 = decide (6 ≤ count1095 b) := rfl
theorem meaning1101 (b : Nat → Bool) : literal (valuationOf b) 1101 = decide (7 ≤ count1095 b) := rfl
theorem meaning1102 (b : Nat → Bool) : literal (valuationOf b) 1102 = decide (8 ≤ count1095 b) := rfl
theorem meaning1103 (b : Nat → Bool) : literal (valuationOf b) 1103 = decide (9 ≤ count1095 b) := rfl
theorem meaning1104 (b : Nat → Bool) : literal (valuationOf b) 1104 = decide (10 ≤ count1095 b) := rfl
theorem meaning1105 (b : Nat → Bool) : literal (valuationOf b) 1105 = decide (11 ≤ count1095 b) := rfl
theorem meaning1106 (b : Nat → Bool) : literal (valuationOf b) 1106 = decide (12 ≤ count1095 b) := rfl
theorem meaning1107 (b : Nat → Bool) : literal (valuationOf b) 1107 = decide (13 ≤ count1095 b) := rfl
theorem meaning1108 (b : Nat → Bool) : literal (valuationOf b) 1108 = decide (14 ≤ count1095 b) := rfl
theorem meaning1109 (b : Nat → Bool) : literal (valuationOf b) 1109 = decide (15 ≤ count1095 b) := rfl
theorem meaning1136 (b : Nat → Bool) : literal (valuationOf b) 1136 = decide (21 ≤ count1116 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (1 ≤ count1492 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (1 ≤ count1496 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (1 ≤ count1500 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (1 ≤ count1507 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (1 ≤ count1509 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (1 ≤ count1511 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (2 ≤ count1511 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (1 ≤ count1515 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (1 ≤ count1517 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (1 ≤ count1519 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (2 ≤ count1519 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (3 ≤ count1523 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (4 ≤ count1531 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (1 ≤ count1548 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (1 ≤ count1550 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (1 ≤ count1554 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (1 ≤ count1558 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (2 ≤ count1562 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (1 ≤ count1570 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (2 ≤ count1570 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (1 ≤ count1572 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (2 ≤ count1574 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (3 ≤ count1574 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (1 ≤ count1578 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (2 ≤ count1578 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (2 ≤ count1582 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (3 ≤ count1582 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (5 ≤ count1586 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (7 ≤ count1594 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (11 ≤ count1610 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (1 ≤ count1632 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (1 ≤ count1634 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (1 ≤ count1637 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (1 ≤ count1639 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (1 ≤ count1641 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (1 ≤ count1645 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (1 ≤ count1652 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (1 ≤ count1656 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (1 ≤ count1660 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (1 ≤ count1662 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (1 ≤ count1664 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (2 ≤ count1664 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (2 ≤ count1668 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (3 ≤ count1668 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (3 ≤ count1676 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (4 ≤ count1676 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (1 ≤ count1691 b) := rfl
theorem meaning1693 (b : Nat → Bool) : literal (valuationOf b) 1693 = decide (1 ≤ count1693 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (2 ≤ count1695 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (1 ≤ count1699 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (1 ≤ count1701 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (1 ≤ count1703 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (2 ≤ count1703 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (3 ≤ count1707 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (4 ≤ count1707 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (2 ≤ count1717 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (2 ≤ count1719 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (1 ≤ count1723 b) := rfl
theorem meaning1724 (b : Nat → Bool) : literal (valuationOf b) 1724 = decide (2 ≤ count1723 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (1 ≤ count1725 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (2 ≤ count1727 b) := rfl
theorem meaning1729 (b : Nat → Bool) : literal (valuationOf b) 1729 = decide (3 ≤ count1727 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (4 ≤ count1731 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (5 ≤ count1731 b) := rfl
theorem meaning1745 (b : Nat → Bool) : literal (valuationOf b) 1745 = decide (7 ≤ count1739 b) := rfl
theorem meaning1746 (b : Nat → Bool) : literal (valuationOf b) 1746 = decide (8 ≤ count1739 b) := rfl
theorem meaning1765 (b : Nat → Bool) : literal (valuationOf b) 1765 = decide (11 ≤ count1755 b) := rfl
theorem meaning1798 (b : Nat → Bool) : literal (valuationOf b) 1798 = decide (22 ≤ count1777 b) := rfl
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
end Snake9.Regrowth.E112097
