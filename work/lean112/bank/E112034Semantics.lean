import E112034Data
namespace Snake9.Regrowth.E112034
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 128 then (if i < 64 then (if i < 32 then (if i < 16 then (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then false else decide (InPath q (33 : Vertex))) else (if i < 3 then decide (InPath q (35 : Vertex)) else decide (InPath q (37 : Vertex)))) else (if i < 6 then (if i < 5 then decide (InPath q (43 : Vertex)) else decide (InPath q (45 : Vertex))) else (if i < 7 then decide (InPath q (47 : Vertex)) else decide (InPath q (49 : Vertex))))) else (if i < 12 then (if i < 10 then (if i < 9 then decide (InPath q (52 : Vertex)) else decide (InPath q (56 : Vertex))) else (if i < 11 then decide (InPath q (60 : Vertex)) else decide (InPath q (62 : Vertex)))) else (if i < 14 then (if i < 13 then decide (InPath q (63 : Vertex)) else decide (InPath q (97 : Vertex))) else (if i < 15 then decide (InPath q (160 : Vertex)) else decide (InPath q (161 : Vertex)))))) else (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then decide (InPath q (164 : Vertex)) else decide (InPath q (166 : Vertex))) else (if i < 19 then decide (InPath q (167 : Vertex)) else decide (InPath q (168 : Vertex)))) else (if i < 22 then (if i < 21 then decide (InPath q (169 : Vertex)) else decide (InPath q (171 : Vertex))) else (if i < 23 then decide (InPath q (172 : Vertex)) else decide (InPath q (174 : Vertex))))) else (if i < 28 then (if i < 26 then (if i < 25 then decide (InPath q (181 : Vertex)) else decide (InPath q (182 : Vertex))) else (if i < 27 then decide (InPath q (183 : Vertex)) else decide (InPath q (184 : Vertex)))) else (if i < 30 then (if i < 29 then decide (InPath q (185 : Vertex)) else decide (InPath q (186 : Vertex))) else (if i < 31 then decide (InPath q (187 : Vertex)) else decide (InPath q (189 : Vertex))))))) else (if i < 48 then (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then decide (InPath q (226 : Vertex)) else decide (InPath q (227 : Vertex))) else (if i < 35 then decide (InPath q (228 : Vertex)) else decide (InPath q (229 : Vertex)))) else (if i < 38 then (if i < 37 then decide (InPath q (233 : Vertex)) else decide (InPath q (234 : Vertex))) else (if i < 39 then decide (InPath q (235 : Vertex)) else decide (InPath q (237 : Vertex))))) else (if i < 44 then (if i < 42 then (if i < 41 then decide (InPath q (239 : Vertex)) else decide (InPath q (240 : Vertex))) else (if i < 43 then decide (InPath q (241 : Vertex)) else decide (InPath q (243 : Vertex)))) else (if i < 46 then (if i < 45 then decide (InPath q (244 : Vertex)) else decide (InPath q (246 : Vertex))) else (if i < 47 then decide (InPath q (248 : Vertex)) else decide (InPath q (252 : Vertex)))))) else (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then decide (InPath q (254 : Vertex)) else decide (InPath q (255 : Vertex))) else (if i < 51 then decide (InPath q (288 : Vertex)) else decide (InPath q (289 : Vertex)))) else (if i < 54 then (if i < 53 then decide (InPath q (290 : Vertex)) else decide (InPath q (292 : Vertex))) else (if i < 55 then decide (InPath q (293 : Vertex)) else decide (InPath q (294 : Vertex))))) else (if i < 60 then (if i < 58 then (if i < 57 then decide (InPath q (296 : Vertex)) else decide (InPath q (298 : Vertex))) else (if i < 59 then decide (InPath q (299 : Vertex)) else decide (InPath q (300 : Vertex)))) else (if i < 62 then (if i < 61 then decide (InPath q (302 : Vertex)) else decide (InPath q (309 : Vertex))) else (if i < 63 then decide (InPath q (310 : Vertex)) else decide (InPath q (311 : Vertex)))))))) else (if i < 96 then (if i < 80 then (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then decide (InPath q (312 : Vertex)) else decide (InPath q (313 : Vertex))) else (if i < 67 then decide (InPath q (315 : Vertex)) else decide (InPath q (317 : Vertex)))) else (if i < 70 then (if i < 69 then decide (InPath q (319 : Vertex)) else decide (InPath q (354 : Vertex))) else (if i < 71 then decide (InPath q (355 : Vertex)) else decide (InPath q (356 : Vertex))))) else (if i < 76 then (if i < 74 then (if i < 73 then decide (InPath q (357 : Vertex)) else decide (InPath q (361 : Vertex))) else (if i < 75 then decide (InPath q (362 : Vertex)) else decide (InPath q (363 : Vertex)))) else (if i < 78 then (if i < 77 then decide (InPath q (365 : Vertex)) else decide (InPath q (367 : Vertex))) else (if i < 79 then decide (InPath q (368 : Vertex)) else decide (InPath q (369 : Vertex)))))) else (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then decide (InPath q (371 : Vertex)) else decide (InPath q (372 : Vertex))) else (if i < 83 then decide (InPath q (376 : Vertex)) else decide (InPath q (380 : Vertex)))) else (if i < 86 then (if i < 85 then decide (InPath q (382 : Vertex)) else decide (InPath q (383 : Vertex))) else (if i < 87 then decide (InPath q (416 : Vertex)) else decide (InPath q (417 : Vertex))))) else (if i < 92 then (if i < 90 then (if i < 89 then decide (InPath q (418 : Vertex)) else decide (InPath q (419 : Vertex))) else (if i < 91 then decide (InPath q (420 : Vertex)) else decide (InPath q (423 : Vertex)))) else (if i < 94 then (if i < 93 then decide (InPath q (425 : Vertex)) else decide (InPath q (426 : Vertex))) else (if i < 95 then decide (InPath q (429 : Vertex)) else decide (InPath q (431 : Vertex))))))) else (if i < 112 then (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then decide (InPath q (432 : Vertex)) else decide (InPath q (433 : Vertex))) else (if i < 99 then decide (InPath q (434 : Vertex)) else decide (InPath q (435 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (436 : Vertex)) else decide (InPath q (442 : Vertex))) else (if i < 103 then decide (InPath q (444 : Vertex)) else decide (InPath q (445 : Vertex))))) else (if i < 108 then (if i < 106 then (if i < 105 then decide (InPath q (446 : Vertex)) else decide (InPath q (447 : Vertex))) else (if i < 107 then decide (InPath q (480 : Vertex)) else decide (InPath q (482 : Vertex)))) else (if i < 110 then (if i < 109 then decide (InPath q (483 : Vertex)) else decide (InPath q (484 : Vertex))) else (if i < 111 then decide (InPath q (485 : Vertex)) else decide (InPath q (486 : Vertex)))))) else (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then decide (InPath q (487 : Vertex)) else decide (InPath q (488 : Vertex))) else (if i < 115 then decide (InPath q (489 : Vertex)) else decide (InPath q (490 : Vertex)))) else (if i < 118 then (if i < 117 then decide (InPath q (492 : Vertex)) else decide (InPath q (493 : Vertex))) else (if i < 119 then decide (InPath q (494 : Vertex)) else decide (InPath q (497 : Vertex))))) else (if i < 124 then (if i < 122 then (if i < 121 then decide (InPath q (499 : Vertex)) else decide (InPath q (501 : Vertex))) else (if i < 123 then decide (InPath q (502 : Vertex)) else decide (InPath q (503 : Vertex)))) else (if i < 126 then (if i < 125 then decide (InPath q (504 : Vertex)) else decide (InPath q (505 : Vertex))) else (if i < 127 then decide (InPath q (506 : Vertex)) else decide (InPath q (507 : Vertex))))))))) else (if i < 192 then (if i < 160 then (if i < 144 then (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then decide (InPath q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (33 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (35 : Vertex)) else decide (BallClauseLogic.Endpoint q (37 : Vertex)))) else (if i < 134 then (if i < 133 then decide (BallClauseLogic.Endpoint q (43 : Vertex)) else decide (BallClauseLogic.Endpoint q (45 : Vertex))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (47 : Vertex)) else decide (BallClauseLogic.Endpoint q (49 : Vertex))))) else (if i < 140 then (if i < 138 then (if i < 137 then decide (BallClauseLogic.Endpoint q (52 : Vertex)) else decide (BallClauseLogic.Endpoint q (56 : Vertex))) else (if i < 139 then decide (BallClauseLogic.Endpoint q (60 : Vertex)) else decide (BallClauseLogic.Endpoint q (62 : Vertex)))) else (if i < 142 then (if i < 141 then decide (BallClauseLogic.Endpoint q (63 : Vertex)) else decide (BallClauseLogic.Endpoint q (97 : Vertex))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex)))))) else (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then decide (BallClauseLogic.Endpoint q (164 : Vertex)) else decide (BallClauseLogic.Endpoint q (166 : Vertex))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (167 : Vertex)) else decide (BallClauseLogic.Endpoint q (168 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (169 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (172 : Vertex)) else decide (BallClauseLogic.Endpoint q (174 : Vertex))))) else (if i < 156 then (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (183 : Vertex)) else decide (BallClauseLogic.Endpoint q (184 : Vertex)))) else (if i < 158 then (if i < 157 then decide (BallClauseLogic.Endpoint q (185 : Vertex)) else decide (BallClauseLogic.Endpoint q (186 : Vertex))) else (if i < 159 then decide (BallClauseLogic.Endpoint q (187 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex))))))) else (if i < 176 then (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else decide (BallClauseLogic.Endpoint q (229 : Vertex)))) else (if i < 166 then (if i < 165 then decide (BallClauseLogic.Endpoint q (233 : Vertex)) else decide (BallClauseLogic.Endpoint q (234 : Vertex))) else (if i < 167 then decide (BallClauseLogic.Endpoint q (235 : Vertex)) else decide (BallClauseLogic.Endpoint q (237 : Vertex))))) else (if i < 172 then (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (239 : Vertex)) else decide (BallClauseLogic.Endpoint q (240 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (241 : Vertex)) else decide (BallClauseLogic.Endpoint q (243 : Vertex)))) else (if i < 174 then (if i < 173 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (246 : Vertex))) else (if i < 175 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else decide (BallClauseLogic.Endpoint q (252 : Vertex)))))) else (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then decide (BallClauseLogic.Endpoint q (254 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex))) else (if i < 179 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else decide (BallClauseLogic.Endpoint q (289 : Vertex)))) else (if i < 182 then (if i < 181 then decide (BallClauseLogic.Endpoint q (290 : Vertex)) else decide (BallClauseLogic.Endpoint q (292 : Vertex))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (293 : Vertex)) else decide (BallClauseLogic.Endpoint q (294 : Vertex))))) else (if i < 188 then (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else decide (BallClauseLogic.Endpoint q (298 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (299 : Vertex)) else decide (BallClauseLogic.Endpoint q (300 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (302 : Vertex)) else decide (BallClauseLogic.Endpoint q (309 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (310 : Vertex)) else decide (BallClauseLogic.Endpoint q (311 : Vertex)))))))) else (if i < 224 then (if i < 208 then (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then decide (BallClauseLogic.Endpoint q (312 : Vertex)) else decide (BallClauseLogic.Endpoint q (313 : Vertex))) else (if i < 195 then decide (BallClauseLogic.Endpoint q (315 : Vertex)) else decide (BallClauseLogic.Endpoint q (317 : Vertex)))) else (if i < 198 then (if i < 197 then decide (BallClauseLogic.Endpoint q (319 : Vertex)) else decide (BallClauseLogic.Endpoint q (354 : Vertex))) else (if i < 199 then decide (BallClauseLogic.Endpoint q (355 : Vertex)) else decide (BallClauseLogic.Endpoint q (356 : Vertex))))) else (if i < 204 then (if i < 202 then (if i < 201 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (361 : Vertex))) else (if i < 203 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else decide (BallClauseLogic.Endpoint q (363 : Vertex)))) else (if i < 206 then (if i < 205 then decide (BallClauseLogic.Endpoint q (365 : Vertex)) else decide (BallClauseLogic.Endpoint q (367 : Vertex))) else (if i < 207 then decide (BallClauseLogic.Endpoint q (368 : Vertex)) else decide (BallClauseLogic.Endpoint q (369 : Vertex)))))) else (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (371 : Vertex)) else decide (BallClauseLogic.Endpoint q (372 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (376 : Vertex)) else decide (BallClauseLogic.Endpoint q (380 : Vertex)))) else (if i < 214 then (if i < 213 then decide (BallClauseLogic.Endpoint q (382 : Vertex)) else decide (BallClauseLogic.Endpoint q (383 : Vertex))) else (if i < 215 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex))))) else (if i < 220 then (if i < 218 then (if i < 217 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (419 : Vertex))) else (if i < 219 then decide (BallClauseLogic.Endpoint q (420 : Vertex)) else decide (BallClauseLogic.Endpoint q (423 : Vertex)))) else (if i < 222 then (if i < 221 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (426 : Vertex))) else (if i < 223 then decide (BallClauseLogic.Endpoint q (429 : Vertex)) else decide (BallClauseLogic.Endpoint q (431 : Vertex))))))) else (if i < 240 then (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else decide (BallClauseLogic.Endpoint q (433 : Vertex))) else (if i < 227 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex)))) else (if i < 230 then (if i < 229 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (442 : Vertex))) else (if i < 231 then decide (BallClauseLogic.Endpoint q (444 : Vertex)) else decide (BallClauseLogic.Endpoint q (445 : Vertex))))) else (if i < 236 then (if i < 234 then (if i < 233 then decide (BallClauseLogic.Endpoint q (446 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))) else (if i < 235 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (482 : Vertex)))) else (if i < 238 then (if i < 237 then decide (BallClauseLogic.Endpoint q (483 : Vertex)) else decide (BallClauseLogic.Endpoint q (484 : Vertex))) else (if i < 239 then decide (BallClauseLogic.Endpoint q (485 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex)))))) else (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex))) else (if i < 243 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (490 : Vertex)))) else (if i < 246 then (if i < 245 then decide (BallClauseLogic.Endpoint q (492 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))) else (if i < 247 then decide (BallClauseLogic.Endpoint q (494 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 252 then (if i < 250 then (if i < 249 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (501 : Vertex))) else (if i < 251 then decide (BallClauseLogic.Endpoint q (502 : Vertex)) else decide (BallClauseLogic.Endpoint q (503 : Vertex)))) else (if i < 254 then (if i < 253 then decide (BallClauseLogic.Endpoint q (504 : Vertex)) else decide (BallClauseLogic.Endpoint q (505 : Vertex))) else (if i < 255 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else (if i < 256 then decide (BallClauseLogic.Endpoint q (507 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex)))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count257 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [129, 130, 131]
def count261 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [140, 142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count303 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count309 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160]
def count311 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160]
def count313 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]
def count317 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164, 165, 166, 167, 168]
def count331 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count335 (b : Nat → Bool) : Nat := countLit b [169, 170, 171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count341 (b : Nat → Bool) : Nat := countLit b [173, 174, 175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [169, 170, 171, 172, 173, 174, 175, 176]
def count345 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]
def count347 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180, 181, 182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count365 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192]
def count373 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190, 191, 192]
def count375 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]
def count379 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]
def count381 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count383 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196]
def count387 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200]
def count395 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count397 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204, 205, 206, 207, 208]
def count409 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count411 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count421 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212, 213, 214, 215, 216]
def count425 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count435 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220, 221, 222, 223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]
def count441 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224]
def count443 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count445 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count449 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231, 232]
def count457 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236]
def count463 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236, 237, 238, 239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240]
def count473 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count475 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count477 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244]
def count479 (b : Nat → Bool) : Nat := countLit b [245, 246]
def count481 (b : Nat → Bool) : Nat := countLit b [247, 248]
def count483 (b : Nat → Bool) : Nat := countLit b [245, 246, 247, 248]
def count485 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244, 245, 246, 247, 248]
def count487 (b : Nat → Bool) : Nat := countLit b [249, 250]
def count489 (b : Nat → Bool) : Nat := countLit b [251, 252]
def count491 (b : Nat → Bool) : Nat := countLit b [249, 250, 251, 252]
def count493 (b : Nat → Bool) : Nat := countLit b [253, 254]
def count495 (b : Nat → Bool) : Nat := countLit b [255, 256]
def count497 (b : Nat → Bool) : Nat := countLit b [253, 254, 255, 256]
def count499 (b : Nat → Bool) : Nat := countLit b [249, 250, 251, 252, 253, 254, 255, 256]
def count501 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]
def count503 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]
def count505 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]
def count507 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256]
def count509 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count511 (b : Nat → Bool) : Nat := countLit b [1, 4, 5]
def count514 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count516 (b : Nat → Bool) : Nat := countLit b [14, 17]
def count518 (b : Nat → Bool) : Nat := countLit b [10, 12, 14, 17]
def count522 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 10, 12, 14, 17]
def count529 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count531 (b : Nat → Bool) : Nat := countLit b [26, 27]
def count533 (b : Nat → Bool) : Nat := countLit b [20, 22, 26, 27]
def count537 (b : Nat → Bool) : Nat := countLit b [30, 31]
def count539 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count541 (b : Nat → Bool) : Nat := countLit b [30, 31, 32, 34]
def count545 (b : Nat → Bool) : Nat := countLit b [20, 22, 26, 27, 30, 31, 32, 34]
def count553 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 10, 12, 14, 17, 20, 22, 26, 27, 30, 31, 32, 34]
def count568 (b : Nat → Bool) : Nat := countLit b [39, 41]
def count570 (b : Nat → Bool) : Nat := countLit b [38, 39, 41]
def count573 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count575 (b : Nat → Bool) : Nat := countLit b [47, 49]
def count577 (b : Nat → Bool) : Nat := countLit b [43, 45, 47, 49]
def count581 (b : Nat → Bool) : Nat := countLit b [38, 39, 41, 43, 45, 47, 49]
def count588 (b : Nat → Bool) : Nat := countLit b [50, 54]
def count590 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count592 (b : Nat → Bool) : Nat := countLit b [50, 54, 55, 57]
def count596 (b : Nat → Bool) : Nat := countLit b [59, 63]
def count598 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count600 (b : Nat → Bool) : Nat := countLit b [59, 63, 64, 66]
def count604 (b : Nat → Bool) : Nat := countLit b [50, 54, 55, 57, 59, 63, 64, 66]
def count612 (b : Nat → Bool) : Nat := countLit b [38, 39, 41, 43, 45, 47, 49, 50, 54, 55, 57, 59, 63, 64, 66]
def count627 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 10, 12, 14, 17, 20, 22, 26, 27, 30, 31, 32, 34, 38, 39, 41, 43, 45, 47, 49, 50, 54, 55, 57, 59, 63, 64, 66]
def count657 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count659 (b : Nat → Bool) : Nat := countLit b [67, 69, 71]
def count662 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count664 (b : Nat → Bool) : Nat := countLit b [78, 80]
def count666 (b : Nat → Bool) : Nat := countLit b [75, 76, 78, 80]
def count670 (b : Nat → Bool) : Nat := countLit b [67, 69, 71, 75, 76, 78, 80]
def count677 (b : Nat → Bool) : Nat := countLit b [83, 85]
def count679 (b : Nat → Bool) : Nat := countLit b [87, 88]
def count681 (b : Nat → Bool) : Nat := countLit b [83, 85, 87, 88]
def count685 (b : Nat → Bool) : Nat := countLit b [90, 91]
def count687 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count689 (b : Nat → Bool) : Nat := countLit b [90, 91, 94, 96]
def count693 (b : Nat → Bool) : Nat := countLit b [83, 85, 87, 88, 90, 91, 94, 96]
def count701 (b : Nat → Bool) : Nat := countLit b [67, 69, 71, 75, 76, 78, 80, 83, 85, 87, 88, 90, 91, 94, 96]
def count716 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count718 (b : Nat → Bool) : Nat := countLit b [102, 105]
def count720 (b : Nat → Bool) : Nat := countLit b [99, 101, 102, 105]
def count724 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count726 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count728 (b : Nat → Bool) : Nat := countLit b [106, 108, 110, 111]
def count732 (b : Nat → Bool) : Nat := countLit b [99, 101, 102, 105, 106, 108, 110, 111]
def count740 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count742 (b : Nat → Bool) : Nat := countLit b [116, 119]
def count744 (b : Nat → Bool) : Nat := countLit b [114, 115, 116, 119]
def count748 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count750 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count752 (b : Nat → Bool) : Nat := countLit b [123, 124, 127, 128]
def count756 (b : Nat → Bool) : Nat := countLit b [114, 115, 116, 119, 123, 124, 127, 128]
def count764 (b : Nat → Bool) : Nat := countLit b [99, 101, 102, 105, 106, 108, 110, 111, 114, 115, 116, 119, 123, 124, 127, 128]
def count780 (b : Nat → Bool) : Nat := countLit b [67, 69, 71, 75, 76, 78, 80, 83, 85, 87, 88, 90, 91, 94, 96, 99, 101, 102, 105, 106, 108, 110, 111, 114, 115, 116, 119, 123, 124, 127, 128]
def count811 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 10, 12, 14, 17, 20, 22, 26, 27, 30, 31, 32, 34, 38, 39, 41, 43, 45, 47, 49, 50, 54, 55, 57, 59, 63, 64, 66, 67, 69, 71, 75, 76, 78, 80, 83, 85, 87, 88, 90, 91, 94, 96, 99, 101, 102, 105, 106, 108, 110, 111, 114, 115, 116, 119, 123, 124, 127, 128]
def count853 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count855 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5]
def count858 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count860 (b : Nat → Bool) : Nat := countLit b [-14, -17]
def count862 (b : Nat → Bool) : Nat := countLit b [-10, -12, -14, -17]
def count866 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -10, -12, -14, -17]
def count873 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count875 (b : Nat → Bool) : Nat := countLit b [-26, -27]
def count877 (b : Nat → Bool) : Nat := countLit b [-20, -22, -26, -27]
def count881 (b : Nat → Bool) : Nat := countLit b [-30, -31]
def count883 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count885 (b : Nat → Bool) : Nat := countLit b [-30, -31, -32, -34]
def count889 (b : Nat → Bool) : Nat := countLit b [-20, -22, -26, -27, -30, -31, -32, -34]
def count897 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -10, -12, -14, -17, -20, -22, -26, -27, -30, -31, -32, -34]
def count912 (b : Nat → Bool) : Nat := countLit b [-39, -41]
def count914 (b : Nat → Bool) : Nat := countLit b [-38, -39, -41]
def count917 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count919 (b : Nat → Bool) : Nat := countLit b [-47, -49]
def count921 (b : Nat → Bool) : Nat := countLit b [-43, -45, -47, -49]
def count925 (b : Nat → Bool) : Nat := countLit b [-38, -39, -41, -43, -45, -47, -49]
def count932 (b : Nat → Bool) : Nat := countLit b [-50, -54]
def count934 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count936 (b : Nat → Bool) : Nat := countLit b [-50, -54, -55, -57]
def count940 (b : Nat → Bool) : Nat := countLit b [-59, -63]
def count942 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count944 (b : Nat → Bool) : Nat := countLit b [-59, -63, -64, -66]
def count948 (b : Nat → Bool) : Nat := countLit b [-50, -54, -55, -57, -59, -63, -64, -66]
def count956 (b : Nat → Bool) : Nat := countLit b [-38, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57, -59, -63, -64, -66]
def count971 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -10, -12, -14, -17, -20, -22, -26, -27, -30, -31, -32, -34, -38, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57, -59, -63, -64, -66]
def count992 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count994 (b : Nat → Bool) : Nat := countLit b [-67, -69, -71]
def count997 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count999 (b : Nat → Bool) : Nat := countLit b [-78, -80]
def count1001 (b : Nat → Bool) : Nat := countLit b [-75, -76, -78, -80]
def count1005 (b : Nat → Bool) : Nat := countLit b [-67, -69, -71, -75, -76, -78, -80]
def count1012 (b : Nat → Bool) : Nat := countLit b [-83, -85]
def count1014 (b : Nat → Bool) : Nat := countLit b [-87, -88]
def count1016 (b : Nat → Bool) : Nat := countLit b [-83, -85, -87, -88]
def count1020 (b : Nat → Bool) : Nat := countLit b [-90, -91]
def count1022 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1024 (b : Nat → Bool) : Nat := countLit b [-90, -91, -94, -96]
def count1028 (b : Nat → Bool) : Nat := countLit b [-83, -85, -87, -88, -90, -91, -94, -96]
def count1036 (b : Nat → Bool) : Nat := countLit b [-67, -69, -71, -75, -76, -78, -80, -83, -85, -87, -88, -90, -91, -94, -96]
def count1051 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count1053 (b : Nat → Bool) : Nat := countLit b [-102, -105]
def count1055 (b : Nat → Bool) : Nat := countLit b [-99, -101, -102, -105]
def count1059 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count1061 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1063 (b : Nat → Bool) : Nat := countLit b [-106, -108, -110, -111]
def count1067 (b : Nat → Bool) : Nat := countLit b [-99, -101, -102, -105, -106, -108, -110, -111]
def count1075 (b : Nat → Bool) : Nat := countLit b [-114, -115]
def count1077 (b : Nat → Bool) : Nat := countLit b [-116, -119]
def count1079 (b : Nat → Bool) : Nat := countLit b [-114, -115, -116, -119]
def count1083 (b : Nat → Bool) : Nat := countLit b [-123, -124]
def count1085 (b : Nat → Bool) : Nat := countLit b [-127, -128]
def count1087 (b : Nat → Bool) : Nat := countLit b [-123, -124, -127, -128]
def count1091 (b : Nat → Bool) : Nat := countLit b [-114, -115, -116, -119, -123, -124, -127, -128]
def count1099 (b : Nat → Bool) : Nat := countLit b [-99, -101, -102, -105, -106, -108, -110, -111, -114, -115, -116, -119, -123, -124, -127, -128]
def count1115 (b : Nat → Bool) : Nat := countLit b [-67, -69, -71, -75, -76, -78, -80, -83, -85, -87, -88, -90, -91, -94, -96, -99, -101, -102, -105, -106, -108, -110, -111, -114, -115, -116, -119, -123, -124, -127, -128]
def count1136 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -10, -12, -14, -17, -20, -22, -26, -27, -30, -31, -32, -34, -38, -39, -41, -43, -45, -47, -49, -50, -54, -55, -57, -59, -63, -64, -66, -67, -69, -71, -75, -76, -78, -80, -83, -85, -87, -88, -90, -91, -94, -96, -99, -101, -102, -105, -106, -108, -110, -111, -114, -115, -116, -119, -123, -124, -127, -128]
def count1157 (b : Nat → Bool) : Nat := countLit b [2, 3]
def count1159 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count1161 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 7]
def count1165 (b : Nat → Bool) : Nat := countLit b [8, 9]
def count1167 (b : Nat → Bool) : Nat := countLit b [11, 13]
def count1169 (b : Nat → Bool) : Nat := countLit b [8, 9, 11, 13]
def count1173 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 7, 8, 9, 11, 13]
def count1181 (b : Nat → Bool) : Nat := countLit b [15, 16]
def count1183 (b : Nat → Bool) : Nat := countLit b [18, 19]
def count1185 (b : Nat → Bool) : Nat := countLit b [15, 16, 18, 19]
def count1189 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count1191 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count1193 (b : Nat → Bool) : Nat := countLit b [21, 23, 24, 25]
def count1197 (b : Nat → Bool) : Nat := countLit b [15, 16, 18, 19, 21, 23, 24, 25]
def count1205 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 7, 8, 9, 11, 13, 15, 16, 18, 19, 21, 23, 24, 25]
def count1221 (b : Nat → Bool) : Nat := countLit b [28, 29]
def count1223 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count1225 (b : Nat → Bool) : Nat := countLit b [28, 29, 33, 35]
def count1229 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count1231 (b : Nat → Bool) : Nat := countLit b [40, 42]
def count1233 (b : Nat → Bool) : Nat := countLit b [36, 37, 40, 42]
def count1237 (b : Nat → Bool) : Nat := countLit b [28, 29, 33, 35, 36, 37, 40, 42]
def count1245 (b : Nat → Bool) : Nat := countLit b [44, 46]
def count1247 (b : Nat → Bool) : Nat := countLit b [48, 51]
def count1249 (b : Nat → Bool) : Nat := countLit b [44, 46, 48, 51]
def count1253 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count1255 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count1257 (b : Nat → Bool) : Nat := countLit b [56, 58, 60]
def count1260 (b : Nat → Bool) : Nat := countLit b [52, 53, 56, 58, 60]
def count1265 (b : Nat → Bool) : Nat := countLit b [44, 46, 48, 51, 52, 53, 56, 58, 60]
def count1274 (b : Nat → Bool) : Nat := countLit b [28, 29, 33, 35, 36, 37, 40, 42, 44, 46, 48, 51, 52, 53, 56, 58, 60]
def count1291 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 7, 8, 9, 11, 13, 15, 16, 18, 19, 21, 23, 24, 25, 28, 29, 33, 35, 36, 37, 40, 42, 44, 46, 48, 51, 52, 53, 56, 58, 60]
def count1324 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count1326 (b : Nat → Bool) : Nat := countLit b [65, 68]
def count1328 (b : Nat → Bool) : Nat := countLit b [61, 62, 65, 68]
def count1332 (b : Nat → Bool) : Nat := countLit b [70, 72]
def count1334 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count1336 (b : Nat → Bool) : Nat := countLit b [70, 72, 73, 74]
def count1340 (b : Nat → Bool) : Nat := countLit b [61, 62, 65, 68, 70, 72, 73, 74]
def count1348 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count1350 (b : Nat → Bool) : Nat := countLit b [81, 82]
def count1352 (b : Nat → Bool) : Nat := countLit b [77, 79, 81, 82]
def count1356 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count1358 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count1360 (b : Nat → Bool) : Nat := countLit b [89, 92, 93]
def count1363 (b : Nat → Bool) : Nat := countLit b [84, 86, 89, 92, 93]
def count1368 (b : Nat → Bool) : Nat := countLit b [77, 79, 81, 82, 84, 86, 89, 92, 93]
def count1377 (b : Nat → Bool) : Nat := countLit b [61, 62, 65, 68, 70, 72, 73, 74, 77, 79, 81, 82, 84, 86, 89, 92, 93]
def count1394 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count1396 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count1398 (b : Nat → Bool) : Nat := countLit b [95, 97, 98, 100]
def count1402 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count1404 (b : Nat → Bool) : Nat := countLit b [107, 109]
def count1406 (b : Nat → Bool) : Nat := countLit b [103, 104, 107, 109]
def count1410 (b : Nat → Bool) : Nat := countLit b [95, 97, 98, 100, 103, 104, 107, 109]
def count1418 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count1420 (b : Nat → Bool) : Nat := countLit b [117, 118]
def count1422 (b : Nat → Bool) : Nat := countLit b [112, 113, 117, 118]
def count1426 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count1428 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count1430 (b : Nat → Bool) : Nat := countLit b [122, 125, 126]
def count1433 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 125, 126]
def count1438 (b : Nat → Bool) : Nat := countLit b [112, 113, 117, 118, 120, 121, 122, 125, 126]
def count1447 (b : Nat → Bool) : Nat := countLit b [95, 97, 98, 100, 103, 104, 107, 109, 112, 113, 117, 118, 120, 121, 122, 125, 126]
def count1464 (b : Nat → Bool) : Nat := countLit b [61, 62, 65, 68, 70, 72, 73, 74, 77, 79, 81, 82, 84, 86, 89, 92, 93, 95, 97, 98, 100, 103, 104, 107, 109, 112, 113, 117, 118, 120, 121, 122, 125, 126]
def count1498 (b : Nat → Bool) : Nat := countLit b [2, 3, 6, 7, 8, 9, 11, 13, 15, 16, 18, 19, 21, 23, 24, 25, 28, 29, 33, 35, 36, 37, 40, 42, 44, 46, 48, 51, 52, 53, 56, 58, 60, 61, 62, 65, 68, 70, 72, 73, 74, 77, 79, 81, 82, 84, 86, 89, 92, 93, 95, 97, 98, 100, 103, 104, 107, 109, 112, 113, 117, 118, 120, 121, 122, 125, 126]
def count1540 (b : Nat → Bool) : Nat := countLit b [-2, -3]
def count1542 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count1544 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -7]
def count1548 (b : Nat → Bool) : Nat := countLit b [-8, -9]
def count1550 (b : Nat → Bool) : Nat := countLit b [-11, -13]
def count1552 (b : Nat → Bool) : Nat := countLit b [-8, -9, -11, -13]
def count1556 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -7, -8, -9, -11, -13]
def count1564 (b : Nat → Bool) : Nat := countLit b [-15, -16]
def count1566 (b : Nat → Bool) : Nat := countLit b [-18, -19]
def count1568 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18, -19]
def count1572 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count1574 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1576 (b : Nat → Bool) : Nat := countLit b [-21, -23, -24, -25]
def count1580 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18, -19, -21, -23, -24, -25]
def count1588 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25]
def count1604 (b : Nat → Bool) : Nat := countLit b [-28, -29]
def count1606 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count1608 (b : Nat → Bool) : Nat := countLit b [-28, -29, -33, -35]
def count1612 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count1614 (b : Nat → Bool) : Nat := countLit b [-40, -42]
def count1616 (b : Nat → Bool) : Nat := countLit b [-36, -37, -40, -42]
def count1620 (b : Nat → Bool) : Nat := countLit b [-28, -29, -33, -35, -36, -37, -40, -42]
def count1628 (b : Nat → Bool) : Nat := countLit b [-44, -46]
def count1630 (b : Nat → Bool) : Nat := countLit b [-48, -51]
def count1632 (b : Nat → Bool) : Nat := countLit b [-44, -46, -48, -51]
def count1636 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count1638 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count1640 (b : Nat → Bool) : Nat := countLit b [-56, -58, -60]
def count1643 (b : Nat → Bool) : Nat := countLit b [-52, -53, -56, -58, -60]
def count1648 (b : Nat → Bool) : Nat := countLit b [-44, -46, -48, -51, -52, -53, -56, -58, -60]
def count1657 (b : Nat → Bool) : Nat := countLit b [-28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]
def count1674 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60]
def count1701 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count1703 (b : Nat → Bool) : Nat := countLit b [-65, -68]
def count1705 (b : Nat → Bool) : Nat := countLit b [-61, -62, -65, -68]
def count1709 (b : Nat → Bool) : Nat := countLit b [-70, -72]
def count1711 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count1713 (b : Nat → Bool) : Nat := countLit b [-70, -72, -73, -74]
def count1717 (b : Nat → Bool) : Nat := countLit b [-61, -62, -65, -68, -70, -72, -73, -74]
def count1725 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count1727 (b : Nat → Bool) : Nat := countLit b [-81, -82]
def count1729 (b : Nat → Bool) : Nat := countLit b [-77, -79, -81, -82]
def count1733 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count1735 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1737 (b : Nat → Bool) : Nat := countLit b [-89, -92, -93]
def count1740 (b : Nat → Bool) : Nat := countLit b [-84, -86, -89, -92, -93]
def count1745 (b : Nat → Bool) : Nat := countLit b [-77, -79, -81, -82, -84, -86, -89, -92, -93]
def count1754 (b : Nat → Bool) : Nat := countLit b [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]
def count1771 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count1773 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count1775 (b : Nat → Bool) : Nat := countLit b [-95, -97, -98, -100]
def count1779 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1781 (b : Nat → Bool) : Nat := countLit b [-107, -109]
def count1783 (b : Nat → Bool) : Nat := countLit b [-103, -104, -107, -109]
def count1787 (b : Nat → Bool) : Nat := countLit b [-95, -97, -98, -100, -103, -104, -107, -109]
def count1795 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1797 (b : Nat → Bool) : Nat := countLit b [-117, -118]
def count1799 (b : Nat → Bool) : Nat := countLit b [-112, -113, -117, -118]
def count1803 (b : Nat → Bool) : Nat := countLit b [-120, -121]
def count1805 (b : Nat → Bool) : Nat := countLit b [-125, -126]
def count1807 (b : Nat → Bool) : Nat := countLit b [-122, -125, -126]
def count1810 (b : Nat → Bool) : Nat := countLit b [-120, -121, -122, -125, -126]
def count1815 (b : Nat → Bool) : Nat := countLit b [-112, -113, -117, -118, -120, -121, -122, -125, -126]
def count1824 (b : Nat → Bool) : Nat := countLit b [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]
def count1841 (b : Nat → Bool) : Nat := countLit b [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]
def count1868 (b : Nat → Bool) : Nat := countLit b [-2, -3, -6, -7, -8, -9, -11, -13, -15, -16, -18, -19, -21, -23, -24, -25, -28, -29, -33, -35, -36, -37, -40, -42, -44, -46, -48, -51, -52, -53, -56, -58, -60, -61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93, -95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 947 then (if i < 473 then (if i < 236 then (if i < 118 then (if i < 59 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 25 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else b 24)) else (if i < 27 then (if i < 26 then b 25 else b 26) else (if i < 28 then b 27 else b 28))))) else (if i < 44 then (if i < 36 then (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else b 35))) else (if i < 40 then (if i < 38 then (if i < 37 then b 36 else b 37) else (if i < 39 then b 38 else b 39)) else (if i < 42 then (if i < 41 then b 40 else b 41) else (if i < 43 then b 42 else b 43)))) else (if i < 51 then (if i < 47 then (if i < 45 then b 44 else (if i < 46 then b 45 else b 46)) else (if i < 49 then (if i < 48 then b 47 else b 48) else (if i < 50 then b 49 else b 50))) else (if i < 55 then (if i < 53 then (if i < 52 then b 51 else b 52) else (if i < 54 then b 53 else b 54)) else (if i < 57 then (if i < 56 then b 55 else b 56) else (if i < 58 then b 57 else b 58)))))) else (if i < 88 then (if i < 73 then (if i < 66 then (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 64 then (if i < 63 then b 62 else b 63) else (if i < 65 then b 64 else b 65))) else (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 71 then (if i < 70 then b 69 else b 70) else (if i < 72 then b 71 else b 72)))) else (if i < 80 then (if i < 76 then (if i < 74 then b 73 else (if i < 75 then b 74 else b 75)) else (if i < 78 then (if i < 77 then b 76 else b 77) else (if i < 79 then b 78 else b 79))) else (if i < 84 then (if i < 82 then (if i < 81 then b 80 else b 81) else (if i < 83 then b 82 else b 83)) else (if i < 86 then (if i < 85 then b 84 else b 85) else (if i < 87 then b 86 else b 87))))) else (if i < 103 then (if i < 95 then (if i < 91 then (if i < 89 then b 88 else (if i < 90 then b 89 else b 90)) else (if i < 93 then (if i < 92 then b 91 else b 92) else (if i < 94 then b 93 else b 94))) else (if i < 99 then (if i < 97 then (if i < 96 then b 95 else b 96) else (if i < 98 then b 97 else b 98)) else (if i < 101 then (if i < 100 then b 99 else b 100) else (if i < 102 then b 101 else b 102)))) else (if i < 110 then (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 108 then (if i < 107 then b 106 else b 107) else (if i < 109 then b 108 else b 109))) else (if i < 114 then (if i < 112 then (if i < 111 then b 110 else b 111) else (if i < 113 then b 112 else b 113)) else (if i < 116 then (if i < 115 then b 114 else b 115) else (if i < 117 then b 116 else b 117))))))) else (if i < 177 then (if i < 147 then (if i < 132 then (if i < 125 then (if i < 121 then (if i < 119 then b 118 else (if i < 120 then b 119 else b 120)) else (if i < 123 then (if i < 122 then b 121 else b 122) else (if i < 124 then b 123 else b 124))) else (if i < 128 then (if i < 126 then b 125 else (if i < 127 then b 126 else b 127)) else (if i < 130 then (if i < 129 then b 128 else b 129) else (if i < 131 then b 130 else b 131)))) else (if i < 139 then (if i < 135 then (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)) else (if i < 137 then (if i < 136 then b 135 else b 136) else (if i < 138 then b 137 else b 138))) else (if i < 143 then (if i < 141 then (if i < 140 then b 139 else b 140) else (if i < 142 then b 141 else b 142)) else (if i < 145 then (if i < 144 then b 143 else b 144) else (if i < 146 then b 145 else b 146))))) else (if i < 162 then (if i < 154 then (if i < 150 then (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)) else (if i < 152 then (if i < 151 then b 150 else b 151) else (if i < 153 then b 152 else b 153))) else (if i < 158 then (if i < 156 then (if i < 155 then b 154 else b 155) else (if i < 157 then b 156 else b 157)) else (if i < 160 then (if i < 159 then b 158 else b 159) else (if i < 161 then b 160 else b 161)))) else (if i < 169 then (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 167 then (if i < 166 then b 165 else b 166) else (if i < 168 then b 167 else b 168))) else (if i < 173 then (if i < 171 then (if i < 170 then b 169 else b 170) else (if i < 172 then b 171 else b 172)) else (if i < 175 then (if i < 174 then b 173 else b 174) else (if i < 176 then b 175 else b 176)))))) else (if i < 206 then (if i < 191 then (if i < 184 then (if i < 180 then (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)) else (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else b 183))) else (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 189 then (if i < 188 then b 187 else b 188) else (if i < 190 then b 189 else b 190)))) else (if i < 198 then (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else b 197))) else (if i < 202 then (if i < 200 then (if i < 199 then b 198 else b 199) else (if i < 201 then b 200 else b 201)) else (if i < 204 then (if i < 203 then b 202 else b 203) else (if i < 205 then b 204 else b 205))))) else (if i < 221 then (if i < 213 then (if i < 209 then (if i < 207 then b 206 else (if i < 208 then b 207 else b 208)) else (if i < 211 then (if i < 210 then b 209 else b 210) else (if i < 212 then b 211 else b 212))) else (if i < 217 then (if i < 215 then (if i < 214 then b 213 else b 214) else (if i < 216 then b 215 else b 216)) else (if i < 219 then (if i < 218 then b 217 else b 218) else (if i < 220 then b 219 else b 220)))) else (if i < 228 then (if i < 224 then (if i < 222 then b 221 else (if i < 223 then b 222 else b 223)) else (if i < 226 then (if i < 225 then b 224 else b 225) else (if i < 227 then b 226 else b 227))) else (if i < 232 then (if i < 230 then (if i < 229 then b 228 else b 229) else (if i < 231 then b 230 else b 231)) else (if i < 234 then (if i < 233 then b 232 else b 233) else (if i < 235 then b 234 else b 235)))))))) else (if i < 354 then (if i < 295 then (if i < 265 then (if i < 250 then (if i < 243 then (if i < 239 then (if i < 237 then b 236 else (if i < 238 then b 237 else b 238)) else (if i < 241 then (if i < 240 then b 239 else b 240) else (if i < 242 then b 241 else b 242))) else (if i < 246 then (if i < 244 then b 243 else (if i < 245 then b 244 else b 245)) else (if i < 248 then (if i < 247 then b 246 else b 247) else (if i < 249 then b 248 else b 249)))) else (if i < 257 then (if i < 253 then (if i < 251 then b 250 else (if i < 252 then b 251 else b 252)) else (if i < 255 then (if i < 254 then b 253 else b 254) else (if i < 256 then b 255 else b 256))) else (if i < 261 then (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 263 then (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b)) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))))) else (if i < 280 then (if i < 272 then (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 270 then (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)))) else (if i < 276 then (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 278 then (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))))) else (if i < 287 then (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))) else (if i < 291 then (if i < 289 then (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))) else (if i < 293 then (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))))))) else (if i < 324 then (if i < 309 then (if i < 302 then (if i < 298 then (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))) else (if i < 300 then (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))) else (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 307 then (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))))) else (if i < 316 then (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)))) else (if i < 320 then (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b))) else (if i < 322 then (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b)) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)))))) else (if i < 339 then (if i < 331 then (if i < 327 then (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))) else (if i < 329 then (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)))) else (if i < 335 then (if i < 333 then (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))))) else (if i < 346 then (if i < 342 then (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))) else (if i < 344 then (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b)) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b)))) else (if i < 350 then (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))))))) else (if i < 413 then (if i < 383 then (if i < 368 then (if i < 361 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))) else (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))))) else (if i < 375 then (if i < 371 then (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))) else (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 379 then (if i < 377 then (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b))) else (if i < 381 then (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b)) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))))) else (if i < 398 then (if i < 390 then (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 388 then (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b)))) else (if i < 394 then (if i < 392 then (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b)) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 396 then (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))))) else (if i < 405 then (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 403 then (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b)) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b)))) else (if i < 409 then (if i < 407 then (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b)) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 411 then (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))))))) else (if i < 443 then (if i < 428 then (if i < 420 then (if i < 416 then (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b))) else (if i < 418 then (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)))) else (if i < 424 then (if i < 422 then (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b)) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))) else (if i < 426 then (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b)) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b))))) else (if i < 435 then (if i < 431 then (if i < 429 then decide (2 ≤ count427 b) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))) else (if i < 433 then (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)) else (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b)))) else (if i < 439 then (if i < 437 then (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b))) else (if i < 441 then (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b)) else (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b)))))) else (if i < 458 then (if i < 450 then (if i < 446 then (if i < 444 then decide (1 ≤ count443 b) else (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b))) else (if i < 448 then (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b)) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b)))) else (if i < 454 then (if i < 452 then (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)) else (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b))) else (if i < 456 then (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b)) else (if i < 457 then decide (2 ≤ count455 b) else decide (1 ≤ count457 b))))) else (if i < 465 then (if i < 461 then (if i < 459 then decide (2 ≤ count457 b) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b))) else (if i < 463 then (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)) else (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b)))) else (if i < 469 then (if i < 467 then (if i < 466 then decide (1 ≤ count465 b) else decide (2 ≤ count465 b)) else (if i < 468 then decide (1 ≤ count467 b) else decide (2 ≤ count467 b))) else (if i < 471 then (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b)) else (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b)))))))))) else (if i < 710 then (if i < 591 then (if i < 532 then (if i < 502 then (if i < 487 then (if i < 480 then (if i < 476 then (if i < 474 then decide (1 ≤ count473 b) else (if i < 475 then decide (2 ≤ count473 b) else decide (1 ≤ count475 b))) else (if i < 478 then (if i < 477 then decide (2 ≤ count475 b) else decide (1 ≤ count477 b)) else (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b)))) else (if i < 483 then (if i < 481 then decide (2 ≤ count479 b) else (if i < 482 then decide (1 ≤ count481 b) else decide (2 ≤ count481 b))) else (if i < 485 then (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b)) else (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b))))) else (if i < 494 then (if i < 490 then (if i < 488 then decide (1 ≤ count487 b) else (if i < 489 then decide (2 ≤ count487 b) else decide (1 ≤ count489 b))) else (if i < 492 then (if i < 491 then decide (2 ≤ count489 b) else decide (1 ≤ count491 b)) else (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b)))) else (if i < 498 then (if i < 496 then (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b)) else (if i < 497 then decide (2 ≤ count495 b) else decide (1 ≤ count497 b))) else (if i < 500 then (if i < 499 then decide (2 ≤ count497 b) else decide (1 ≤ count499 b)) else (if i < 501 then decide (2 ≤ count499 b) else decide (1 ≤ count501 b)))))) else (if i < 517 then (if i < 509 then (if i < 505 then (if i < 503 then decide (2 ≤ count501 b) else (if i < 504 then decide (1 ≤ count503 b) else decide (2 ≤ count503 b))) else (if i < 507 then (if i < 506 then decide (1 ≤ count505 b) else decide (2 ≤ count505 b)) else (if i < 508 then decide (1 ≤ count507 b) else decide (2 ≤ count507 b)))) else (if i < 513 then (if i < 511 then (if i < 510 then decide (1 ≤ count509 b) else decide (2 ≤ count509 b)) else (if i < 512 then decide (1 ≤ count511 b) else decide (2 ≤ count511 b))) else (if i < 515 then (if i < 514 then decide (3 ≤ count511 b) else decide (1 ≤ count514 b)) else (if i < 516 then decide (2 ≤ count514 b) else decide (1 ≤ count516 b))))) else (if i < 524 then (if i < 520 then (if i < 518 then decide (2 ≤ count516 b) else (if i < 519 then decide (1 ≤ count518 b) else decide (2 ≤ count518 b))) else (if i < 522 then (if i < 521 then decide (3 ≤ count518 b) else decide (4 ≤ count518 b)) else (if i < 523 then decide (1 ≤ count522 b) else decide (2 ≤ count522 b)))) else (if i < 528 then (if i < 526 then (if i < 525 then decide (3 ≤ count522 b) else decide (4 ≤ count522 b)) else (if i < 527 then decide (5 ≤ count522 b) else decide (6 ≤ count522 b))) else (if i < 530 then (if i < 529 then decide (7 ≤ count522 b) else decide (1 ≤ count529 b)) else (if i < 531 then decide (2 ≤ count529 b) else decide (1 ≤ count531 b))))))) else (if i < 561 then (if i < 546 then (if i < 539 then (if i < 535 then (if i < 533 then decide (2 ≤ count531 b) else (if i < 534 then decide (1 ≤ count533 b) else decide (2 ≤ count533 b))) else (if i < 537 then (if i < 536 then decide (3 ≤ count533 b) else decide (4 ≤ count533 b)) else (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b)))) else (if i < 542 then (if i < 540 then decide (1 ≤ count539 b) else (if i < 541 then decide (2 ≤ count539 b) else decide (1 ≤ count541 b))) else (if i < 544 then (if i < 543 then decide (2 ≤ count541 b) else decide (3 ≤ count541 b)) else (if i < 545 then decide (4 ≤ count541 b) else decide (1 ≤ count545 b))))) else (if i < 553 then (if i < 549 then (if i < 547 then decide (2 ≤ count545 b) else (if i < 548 then decide (3 ≤ count545 b) else decide (4 ≤ count545 b))) else (if i < 551 then (if i < 550 then decide (5 ≤ count545 b) else decide (6 ≤ count545 b)) else (if i < 552 then decide (7 ≤ count545 b) else decide (8 ≤ count545 b)))) else (if i < 557 then (if i < 555 then (if i < 554 then decide (1 ≤ count553 b) else decide (2 ≤ count553 b)) else (if i < 556 then decide (3 ≤ count553 b) else decide (4 ≤ count553 b))) else (if i < 559 then (if i < 558 then decide (5 ≤ count553 b) else decide (6 ≤ count553 b)) else (if i < 560 then decide (7 ≤ count553 b) else decide (8 ≤ count553 b)))))) else (if i < 576 then (if i < 568 then (if i < 564 then (if i < 562 then decide (9 ≤ count553 b) else (if i < 563 then decide (10 ≤ count553 b) else decide (11 ≤ count553 b))) else (if i < 566 then (if i < 565 then decide (12 ≤ count553 b) else decide (13 ≤ count553 b)) else (if i < 567 then decide (14 ≤ count553 b) else decide (15 ≤ count553 b)))) else (if i < 572 then (if i < 570 then (if i < 569 then decide (1 ≤ count568 b) else decide (2 ≤ count568 b)) else (if i < 571 then decide (1 ≤ count570 b) else decide (2 ≤ count570 b))) else (if i < 574 then (if i < 573 then decide (3 ≤ count570 b) else decide (1 ≤ count573 b)) else (if i < 575 then decide (2 ≤ count573 b) else decide (1 ≤ count575 b))))) else (if i < 583 then (if i < 579 then (if i < 577 then decide (2 ≤ count575 b) else (if i < 578 then decide (1 ≤ count577 b) else decide (2 ≤ count577 b))) else (if i < 581 then (if i < 580 then decide (3 ≤ count577 b) else decide (4 ≤ count577 b)) else (if i < 582 then decide (1 ≤ count581 b) else decide (2 ≤ count581 b)))) else (if i < 587 then (if i < 585 then (if i < 584 then decide (3 ≤ count581 b) else decide (4 ≤ count581 b)) else (if i < 586 then decide (5 ≤ count581 b) else decide (6 ≤ count581 b))) else (if i < 589 then (if i < 588 then decide (7 ≤ count581 b) else decide (1 ≤ count588 b)) else (if i < 590 then decide (2 ≤ count588 b) else decide (1 ≤ count590 b)))))))) else (if i < 650 then (if i < 620 then (if i < 605 then (if i < 598 then (if i < 594 then (if i < 592 then decide (2 ≤ count590 b) else (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b))) else (if i < 596 then (if i < 595 then decide (3 ≤ count592 b) else decide (4 ≤ count592 b)) else (if i < 597 then decide (1 ≤ count596 b) else decide (2 ≤ count596 b)))) else (if i < 601 then (if i < 599 then decide (1 ≤ count598 b) else (if i < 600 then decide (2 ≤ count598 b) else decide (1 ≤ count600 b))) else (if i < 603 then (if i < 602 then decide (2 ≤ count600 b) else decide (3 ≤ count600 b)) else (if i < 604 then decide (4 ≤ count600 b) else decide (1 ≤ count604 b))))) else (if i < 612 then (if i < 608 then (if i < 606 then decide (2 ≤ count604 b) else (if i < 607 then decide (3 ≤ count604 b) else decide (4 ≤ count604 b))) else (if i < 610 then (if i < 609 then decide (5 ≤ count604 b) else decide (6 ≤ count604 b)) else (if i < 611 then decide (7 ≤ count604 b) else decide (8 ≤ count604 b)))) else (if i < 616 then (if i < 614 then (if i < 613 then decide (1 ≤ count612 b) else decide (2 ≤ count612 b)) else (if i < 615 then decide (3 ≤ count612 b) else decide (4 ≤ count612 b))) else (if i < 618 then (if i < 617 then decide (5 ≤ count612 b) else decide (6 ≤ count612 b)) else (if i < 619 then decide (7 ≤ count612 b) else decide (8 ≤ count612 b)))))) else (if i < 635 then (if i < 627 then (if i < 623 then (if i < 621 then decide (9 ≤ count612 b) else (if i < 622 then decide (10 ≤ count612 b) else decide (11 ≤ count612 b))) else (if i < 625 then (if i < 624 then decide (12 ≤ count612 b) else decide (13 ≤ count612 b)) else (if i < 626 then decide (14 ≤ count612 b) else decide (15 ≤ count612 b)))) else (if i < 631 then (if i < 629 then (if i < 628 then decide (1 ≤ count627 b) else decide (2 ≤ count627 b)) else (if i < 630 then decide (3 ≤ count627 b) else decide (4 ≤ count627 b))) else (if i < 633 then (if i < 632 then decide (5 ≤ count627 b) else decide (6 ≤ count627 b)) else (if i < 634 then decide (7 ≤ count627 b) else decide (8 ≤ count627 b))))) else (if i < 642 then (if i < 638 then (if i < 636 then decide (9 ≤ count627 b) else (if i < 637 then decide (10 ≤ count627 b) else decide (11 ≤ count627 b))) else (if i < 640 then (if i < 639 then decide (12 ≤ count627 b) else decide (13 ≤ count627 b)) else (if i < 641 then decide (14 ≤ count627 b) else decide (15 ≤ count627 b)))) else (if i < 646 then (if i < 644 then (if i < 643 then decide (16 ≤ count627 b) else decide (17 ≤ count627 b)) else (if i < 645 then decide (18 ≤ count627 b) else decide (19 ≤ count627 b))) else (if i < 648 then (if i < 647 then decide (20 ≤ count627 b) else decide (21 ≤ count627 b)) else (if i < 649 then decide (22 ≤ count627 b) else decide (23 ≤ count627 b))))))) else (if i < 680 then (if i < 665 then (if i < 657 then (if i < 653 then (if i < 651 then decide (24 ≤ count627 b) else (if i < 652 then decide (25 ≤ count627 b) else decide (26 ≤ count627 b))) else (if i < 655 then (if i < 654 then decide (27 ≤ count627 b) else decide (28 ≤ count627 b)) else (if i < 656 then decide (29 ≤ count627 b) else decide (30 ≤ count627 b)))) else (if i < 661 then (if i < 659 then (if i < 658 then decide (1 ≤ count657 b) else decide (2 ≤ count657 b)) else (if i < 660 then decide (1 ≤ count659 b) else decide (2 ≤ count659 b))) else (if i < 663 then (if i < 662 then decide (3 ≤ count659 b) else decide (1 ≤ count662 b)) else (if i < 664 then decide (2 ≤ count662 b) else decide (1 ≤ count664 b))))) else (if i < 672 then (if i < 668 then (if i < 666 then decide (2 ≤ count664 b) else (if i < 667 then decide (1 ≤ count666 b) else decide (2 ≤ count666 b))) else (if i < 670 then (if i < 669 then decide (3 ≤ count666 b) else decide (4 ≤ count666 b)) else (if i < 671 then decide (1 ≤ count670 b) else decide (2 ≤ count670 b)))) else (if i < 676 then (if i < 674 then (if i < 673 then decide (3 ≤ count670 b) else decide (4 ≤ count670 b)) else (if i < 675 then decide (5 ≤ count670 b) else decide (6 ≤ count670 b))) else (if i < 678 then (if i < 677 then decide (7 ≤ count670 b) else decide (1 ≤ count677 b)) else (if i < 679 then decide (2 ≤ count677 b) else decide (1 ≤ count679 b)))))) else (if i < 695 then (if i < 687 then (if i < 683 then (if i < 681 then decide (2 ≤ count679 b) else (if i < 682 then decide (1 ≤ count681 b) else decide (2 ≤ count681 b))) else (if i < 685 then (if i < 684 then decide (3 ≤ count681 b) else decide (4 ≤ count681 b)) else (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b)))) else (if i < 691 then (if i < 689 then (if i < 688 then decide (1 ≤ count687 b) else decide (2 ≤ count687 b)) else (if i < 690 then decide (1 ≤ count689 b) else decide (2 ≤ count689 b))) else (if i < 693 then (if i < 692 then decide (3 ≤ count689 b) else decide (4 ≤ count689 b)) else (if i < 694 then decide (1 ≤ count693 b) else decide (2 ≤ count693 b))))) else (if i < 702 then (if i < 698 then (if i < 696 then decide (3 ≤ count693 b) else (if i < 697 then decide (4 ≤ count693 b) else decide (5 ≤ count693 b))) else (if i < 700 then (if i < 699 then decide (6 ≤ count693 b) else decide (7 ≤ count693 b)) else (if i < 701 then decide (8 ≤ count693 b) else decide (1 ≤ count701 b)))) else (if i < 706 then (if i < 704 then (if i < 703 then decide (2 ≤ count701 b) else decide (3 ≤ count701 b)) else (if i < 705 then decide (4 ≤ count701 b) else decide (5 ≤ count701 b))) else (if i < 708 then (if i < 707 then decide (6 ≤ count701 b) else decide (7 ≤ count701 b)) else (if i < 709 then decide (8 ≤ count701 b) else decide (9 ≤ count701 b))))))))) else (if i < 828 then (if i < 769 then (if i < 739 then (if i < 724 then (if i < 717 then (if i < 713 then (if i < 711 then decide (10 ≤ count701 b) else (if i < 712 then decide (11 ≤ count701 b) else decide (12 ≤ count701 b))) else (if i < 715 then (if i < 714 then decide (13 ≤ count701 b) else decide (14 ≤ count701 b)) else (if i < 716 then decide (15 ≤ count701 b) else decide (1 ≤ count716 b)))) else (if i < 720 then (if i < 718 then decide (2 ≤ count716 b) else (if i < 719 then decide (1 ≤ count718 b) else decide (2 ≤ count718 b))) else (if i < 722 then (if i < 721 then decide (1 ≤ count720 b) else decide (2 ≤ count720 b)) else (if i < 723 then decide (3 ≤ count720 b) else decide (4 ≤ count720 b))))) else (if i < 731 then (if i < 727 then (if i < 725 then decide (1 ≤ count724 b) else (if i < 726 then decide (2 ≤ count724 b) else decide (1 ≤ count726 b))) else (if i < 729 then (if i < 728 then decide (2 ≤ count726 b) else decide (1 ≤ count728 b)) else (if i < 730 then decide (2 ≤ count728 b) else decide (3 ≤ count728 b)))) else (if i < 735 then (if i < 733 then (if i < 732 then decide (4 ≤ count728 b) else decide (1 ≤ count732 b)) else (if i < 734 then decide (2 ≤ count732 b) else decide (3 ≤ count732 b))) else (if i < 737 then (if i < 736 then decide (4 ≤ count732 b) else decide (5 ≤ count732 b)) else (if i < 738 then decide (6 ≤ count732 b) else decide (7 ≤ count732 b)))))) else (if i < 754 then (if i < 746 then (if i < 742 then (if i < 740 then decide (8 ≤ count732 b) else (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b))) else (if i < 744 then (if i < 743 then decide (1 ≤ count742 b) else decide (2 ≤ count742 b)) else (if i < 745 then decide (1 ≤ count744 b) else decide (2 ≤ count744 b)))) else (if i < 750 then (if i < 748 then (if i < 747 then decide (3 ≤ count744 b) else decide (4 ≤ count744 b)) else (if i < 749 then decide (1 ≤ count748 b) else decide (2 ≤ count748 b))) else (if i < 752 then (if i < 751 then decide (1 ≤ count750 b) else decide (2 ≤ count750 b)) else (if i < 753 then decide (1 ≤ count752 b) else decide (2 ≤ count752 b))))) else (if i < 761 then (if i < 757 then (if i < 755 then decide (3 ≤ count752 b) else (if i < 756 then decide (4 ≤ count752 b) else decide (1 ≤ count756 b))) else (if i < 759 then (if i < 758 then decide (2 ≤ count756 b) else decide (3 ≤ count756 b)) else (if i < 760 then decide (4 ≤ count756 b) else decide (5 ≤ count756 b)))) else (if i < 765 then (if i < 763 then (if i < 762 then decide (6 ≤ count756 b) else decide (7 ≤ count756 b)) else (if i < 764 then decide (8 ≤ count756 b) else decide (1 ≤ count764 b))) else (if i < 767 then (if i < 766 then decide (2 ≤ count764 b) else decide (3 ≤ count764 b)) else (if i < 768 then decide (4 ≤ count764 b) else decide (5 ≤ count764 b))))))) else (if i < 798 then (if i < 783 then (if i < 776 then (if i < 772 then (if i < 770 then decide (6 ≤ count764 b) else (if i < 771 then decide (7 ≤ count764 b) else decide (8 ≤ count764 b))) else (if i < 774 then (if i < 773 then decide (9 ≤ count764 b) else decide (10 ≤ count764 b)) else (if i < 775 then decide (11 ≤ count764 b) else decide (12 ≤ count764 b)))) else (if i < 779 then (if i < 777 then decide (13 ≤ count764 b) else (if i < 778 then decide (14 ≤ count764 b) else decide (15 ≤ count764 b))) else (if i < 781 then (if i < 780 then decide (16 ≤ count764 b) else decide (1 ≤ count780 b)) else (if i < 782 then decide (2 ≤ count780 b) else decide (3 ≤ count780 b))))) else (if i < 790 then (if i < 786 then (if i < 784 then decide (4 ≤ count780 b) else (if i < 785 then decide (5 ≤ count780 b) else decide (6 ≤ count780 b))) else (if i < 788 then (if i < 787 then decide (7 ≤ count780 b) else decide (8 ≤ count780 b)) else (if i < 789 then decide (9 ≤ count780 b) else decide (10 ≤ count780 b)))) else (if i < 794 then (if i < 792 then (if i < 791 then decide (11 ≤ count780 b) else decide (12 ≤ count780 b)) else (if i < 793 then decide (13 ≤ count780 b) else decide (14 ≤ count780 b))) else (if i < 796 then (if i < 795 then decide (15 ≤ count780 b) else decide (16 ≤ count780 b)) else (if i < 797 then decide (17 ≤ count780 b) else decide (18 ≤ count780 b)))))) else (if i < 813 then (if i < 805 then (if i < 801 then (if i < 799 then decide (19 ≤ count780 b) else (if i < 800 then decide (20 ≤ count780 b) else decide (21 ≤ count780 b))) else (if i < 803 then (if i < 802 then decide (22 ≤ count780 b) else decide (23 ≤ count780 b)) else (if i < 804 then decide (24 ≤ count780 b) else decide (25 ≤ count780 b)))) else (if i < 809 then (if i < 807 then (if i < 806 then decide (26 ≤ count780 b) else decide (27 ≤ count780 b)) else (if i < 808 then decide (28 ≤ count780 b) else decide (29 ≤ count780 b))) else (if i < 811 then (if i < 810 then decide (30 ≤ count780 b) else decide (31 ≤ count780 b)) else (if i < 812 then decide (1 ≤ count811 b) else decide (2 ≤ count811 b))))) else (if i < 820 then (if i < 816 then (if i < 814 then decide (3 ≤ count811 b) else (if i < 815 then decide (4 ≤ count811 b) else decide (5 ≤ count811 b))) else (if i < 818 then (if i < 817 then decide (6 ≤ count811 b) else decide (7 ≤ count811 b)) else (if i < 819 then decide (8 ≤ count811 b) else decide (9 ≤ count811 b)))) else (if i < 824 then (if i < 822 then (if i < 821 then decide (10 ≤ count811 b) else decide (11 ≤ count811 b)) else (if i < 823 then decide (12 ≤ count811 b) else decide (13 ≤ count811 b))) else (if i < 826 then (if i < 825 then decide (14 ≤ count811 b) else decide (15 ≤ count811 b)) else (if i < 827 then decide (16 ≤ count811 b) else decide (17 ≤ count811 b)))))))) else (if i < 887 then (if i < 857 then (if i < 842 then (if i < 835 then (if i < 831 then (if i < 829 then decide (18 ≤ count811 b) else (if i < 830 then decide (19 ≤ count811 b) else decide (20 ≤ count811 b))) else (if i < 833 then (if i < 832 then decide (21 ≤ count811 b) else decide (22 ≤ count811 b)) else (if i < 834 then decide (23 ≤ count811 b) else decide (24 ≤ count811 b)))) else (if i < 838 then (if i < 836 then decide (25 ≤ count811 b) else (if i < 837 then decide (26 ≤ count811 b) else decide (27 ≤ count811 b))) else (if i < 840 then (if i < 839 then decide (28 ≤ count811 b) else decide (29 ≤ count811 b)) else (if i < 841 then decide (30 ≤ count811 b) else decide (31 ≤ count811 b))))) else (if i < 849 then (if i < 845 then (if i < 843 then decide (32 ≤ count811 b) else (if i < 844 then decide (33 ≤ count811 b) else decide (34 ≤ count811 b))) else (if i < 847 then (if i < 846 then decide (35 ≤ count811 b) else decide (36 ≤ count811 b)) else (if i < 848 then decide (37 ≤ count811 b) else decide (38 ≤ count811 b)))) else (if i < 853 then (if i < 851 then (if i < 850 then decide (39 ≤ count811 b) else decide (40 ≤ count811 b)) else (if i < 852 then decide (41 ≤ count811 b) else decide (42 ≤ count811 b))) else (if i < 855 then (if i < 854 then decide (1 ≤ count853 b) else decide (2 ≤ count853 b)) else (if i < 856 then decide (1 ≤ count855 b) else decide (2 ≤ count855 b)))))) else (if i < 872 then (if i < 864 then (if i < 860 then (if i < 858 then decide (3 ≤ count855 b) else (if i < 859 then decide (1 ≤ count858 b) else decide (2 ≤ count858 b))) else (if i < 862 then (if i < 861 then decide (1 ≤ count860 b) else decide (2 ≤ count860 b)) else (if i < 863 then decide (1 ≤ count862 b) else decide (2 ≤ count862 b)))) else (if i < 868 then (if i < 866 then (if i < 865 then decide (3 ≤ count862 b) else decide (4 ≤ count862 b)) else (if i < 867 then decide (1 ≤ count866 b) else decide (2 ≤ count866 b))) else (if i < 870 then (if i < 869 then decide (3 ≤ count866 b) else decide (4 ≤ count866 b)) else (if i < 871 then decide (5 ≤ count866 b) else decide (6 ≤ count866 b))))) else (if i < 879 then (if i < 875 then (if i < 873 then decide (7 ≤ count866 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b))) else (if i < 877 then (if i < 876 then decide (1 ≤ count875 b) else decide (2 ≤ count875 b)) else (if i < 878 then decide (1 ≤ count877 b) else decide (2 ≤ count877 b)))) else (if i < 883 then (if i < 881 then (if i < 880 then decide (3 ≤ count877 b) else decide (4 ≤ count877 b)) else (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b))) else (if i < 885 then (if i < 884 then decide (1 ≤ count883 b) else decide (2 ≤ count883 b)) else (if i < 886 then decide (1 ≤ count885 b) else decide (2 ≤ count885 b))))))) else (if i < 917 then (if i < 902 then (if i < 894 then (if i < 890 then (if i < 888 then decide (3 ≤ count885 b) else (if i < 889 then decide (4 ≤ count885 b) else decide (1 ≤ count889 b))) else (if i < 892 then (if i < 891 then decide (2 ≤ count889 b) else decide (3 ≤ count889 b)) else (if i < 893 then decide (4 ≤ count889 b) else decide (5 ≤ count889 b)))) else (if i < 898 then (if i < 896 then (if i < 895 then decide (6 ≤ count889 b) else decide (7 ≤ count889 b)) else (if i < 897 then decide (8 ≤ count889 b) else decide (1 ≤ count897 b))) else (if i < 900 then (if i < 899 then decide (2 ≤ count897 b) else decide (3 ≤ count897 b)) else (if i < 901 then decide (4 ≤ count897 b) else decide (5 ≤ count897 b))))) else (if i < 909 then (if i < 905 then (if i < 903 then decide (6 ≤ count897 b) else (if i < 904 then decide (7 ≤ count897 b) else decide (8 ≤ count897 b))) else (if i < 907 then (if i < 906 then decide (9 ≤ count897 b) else decide (10 ≤ count897 b)) else (if i < 908 then decide (11 ≤ count897 b) else decide (12 ≤ count897 b)))) else (if i < 913 then (if i < 911 then (if i < 910 then decide (13 ≤ count897 b) else decide (14 ≤ count897 b)) else (if i < 912 then decide (15 ≤ count897 b) else decide (1 ≤ count912 b))) else (if i < 915 then (if i < 914 then decide (2 ≤ count912 b) else decide (1 ≤ count914 b)) else (if i < 916 then decide (2 ≤ count914 b) else decide (3 ≤ count914 b)))))) else (if i < 932 then (if i < 924 then (if i < 920 then (if i < 918 then decide (1 ≤ count917 b) else (if i < 919 then decide (2 ≤ count917 b) else decide (1 ≤ count919 b))) else (if i < 922 then (if i < 921 then decide (2 ≤ count919 b) else decide (1 ≤ count921 b)) else (if i < 923 then decide (2 ≤ count921 b) else decide (3 ≤ count921 b)))) else (if i < 928 then (if i < 926 then (if i < 925 then decide (4 ≤ count921 b) else decide (1 ≤ count925 b)) else (if i < 927 then decide (2 ≤ count925 b) else decide (3 ≤ count925 b))) else (if i < 930 then (if i < 929 then decide (4 ≤ count925 b) else decide (5 ≤ count925 b)) else (if i < 931 then decide (6 ≤ count925 b) else decide (7 ≤ count925 b))))) else (if i < 939 then (if i < 935 then (if i < 933 then decide (1 ≤ count932 b) else (if i < 934 then decide (2 ≤ count932 b) else decide (1 ≤ count934 b))) else (if i < 937 then (if i < 936 then decide (2 ≤ count934 b) else decide (1 ≤ count936 b)) else (if i < 938 then decide (2 ≤ count936 b) else decide (3 ≤ count936 b)))) else (if i < 943 then (if i < 941 then (if i < 940 then decide (4 ≤ count936 b) else decide (1 ≤ count940 b)) else (if i < 942 then decide (2 ≤ count940 b) else decide (1 ≤ count942 b))) else (if i < 945 then (if i < 944 then decide (2 ≤ count942 b) else decide (1 ≤ count944 b)) else (if i < 946 then decide (2 ≤ count944 b) else decide (3 ≤ count944 b))))))))))) else (if i < 1421 then (if i < 1184 then (if i < 1065 then (if i < 1006 then (if i < 976 then (if i < 961 then (if i < 954 then (if i < 950 then (if i < 948 then decide (4 ≤ count944 b) else (if i < 949 then decide (1 ≤ count948 b) else decide (2 ≤ count948 b))) else (if i < 952 then (if i < 951 then decide (3 ≤ count948 b) else decide (4 ≤ count948 b)) else (if i < 953 then decide (5 ≤ count948 b) else decide (6 ≤ count948 b)))) else (if i < 957 then (if i < 955 then decide (7 ≤ count948 b) else (if i < 956 then decide (8 ≤ count948 b) else decide (1 ≤ count956 b))) else (if i < 959 then (if i < 958 then decide (2 ≤ count956 b) else decide (3 ≤ count956 b)) else (if i < 960 then decide (4 ≤ count956 b) else decide (5 ≤ count956 b))))) else (if i < 968 then (if i < 964 then (if i < 962 then decide (6 ≤ count956 b) else (if i < 963 then decide (7 ≤ count956 b) else decide (8 ≤ count956 b))) else (if i < 966 then (if i < 965 then decide (9 ≤ count956 b) else decide (10 ≤ count956 b)) else (if i < 967 then decide (11 ≤ count956 b) else decide (12 ≤ count956 b)))) else (if i < 972 then (if i < 970 then (if i < 969 then decide (13 ≤ count956 b) else decide (14 ≤ count956 b)) else (if i < 971 then decide (15 ≤ count956 b) else decide (1 ≤ count971 b))) else (if i < 974 then (if i < 973 then decide (2 ≤ count971 b) else decide (3 ≤ count971 b)) else (if i < 975 then decide (4 ≤ count971 b) else decide (5 ≤ count971 b)))))) else (if i < 991 then (if i < 983 then (if i < 979 then (if i < 977 then decide (6 ≤ count971 b) else (if i < 978 then decide (7 ≤ count971 b) else decide (8 ≤ count971 b))) else (if i < 981 then (if i < 980 then decide (9 ≤ count971 b) else decide (10 ≤ count971 b)) else (if i < 982 then decide (11 ≤ count971 b) else decide (12 ≤ count971 b)))) else (if i < 987 then (if i < 985 then (if i < 984 then decide (13 ≤ count971 b) else decide (14 ≤ count971 b)) else (if i < 986 then decide (15 ≤ count971 b) else decide (16 ≤ count971 b))) else (if i < 989 then (if i < 988 then decide (17 ≤ count971 b) else decide (18 ≤ count971 b)) else (if i < 990 then decide (19 ≤ count971 b) else decide (20 ≤ count971 b))))) else (if i < 998 then (if i < 994 then (if i < 992 then decide (21 ≤ count971 b) else (if i < 993 then decide (1 ≤ count992 b) else decide (2 ≤ count992 b))) else (if i < 996 then (if i < 995 then decide (1 ≤ count994 b) else decide (2 ≤ count994 b)) else (if i < 997 then decide (3 ≤ count994 b) else decide (1 ≤ count997 b)))) else (if i < 1002 then (if i < 1000 then (if i < 999 then decide (2 ≤ count997 b) else decide (1 ≤ count999 b)) else (if i < 1001 then decide (2 ≤ count999 b) else decide (1 ≤ count1001 b))) else (if i < 1004 then (if i < 1003 then decide (2 ≤ count1001 b) else decide (3 ≤ count1001 b)) else (if i < 1005 then decide (4 ≤ count1001 b) else decide (1 ≤ count1005 b))))))) else (if i < 1035 then (if i < 1020 then (if i < 1013 then (if i < 1009 then (if i < 1007 then decide (2 ≤ count1005 b) else (if i < 1008 then decide (3 ≤ count1005 b) else decide (4 ≤ count1005 b))) else (if i < 1011 then (if i < 1010 then decide (5 ≤ count1005 b) else decide (6 ≤ count1005 b)) else (if i < 1012 then decide (7 ≤ count1005 b) else decide (1 ≤ count1012 b)))) else (if i < 1016 then (if i < 1014 then decide (2 ≤ count1012 b) else (if i < 1015 then decide (1 ≤ count1014 b) else decide (2 ≤ count1014 b))) else (if i < 1018 then (if i < 1017 then decide (1 ≤ count1016 b) else decide (2 ≤ count1016 b)) else (if i < 1019 then decide (3 ≤ count1016 b) else decide (4 ≤ count1016 b))))) else (if i < 1027 then (if i < 1023 then (if i < 1021 then decide (1 ≤ count1020 b) else (if i < 1022 then decide (2 ≤ count1020 b) else decide (1 ≤ count1022 b))) else (if i < 1025 then (if i < 1024 then decide (2 ≤ count1022 b) else decide (1 ≤ count1024 b)) else (if i < 1026 then decide (2 ≤ count1024 b) else decide (3 ≤ count1024 b)))) else (if i < 1031 then (if i < 1029 then (if i < 1028 then decide (4 ≤ count1024 b) else decide (1 ≤ count1028 b)) else (if i < 1030 then decide (2 ≤ count1028 b) else decide (3 ≤ count1028 b))) else (if i < 1033 then (if i < 1032 then decide (4 ≤ count1028 b) else decide (5 ≤ count1028 b)) else (if i < 1034 then decide (6 ≤ count1028 b) else decide (7 ≤ count1028 b)))))) else (if i < 1050 then (if i < 1042 then (if i < 1038 then (if i < 1036 then decide (8 ≤ count1028 b) else (if i < 1037 then decide (1 ≤ count1036 b) else decide (2 ≤ count1036 b))) else (if i < 1040 then (if i < 1039 then decide (3 ≤ count1036 b) else decide (4 ≤ count1036 b)) else (if i < 1041 then decide (5 ≤ count1036 b) else decide (6 ≤ count1036 b)))) else (if i < 1046 then (if i < 1044 then (if i < 1043 then decide (7 ≤ count1036 b) else decide (8 ≤ count1036 b)) else (if i < 1045 then decide (9 ≤ count1036 b) else decide (10 ≤ count1036 b))) else (if i < 1048 then (if i < 1047 then decide (11 ≤ count1036 b) else decide (12 ≤ count1036 b)) else (if i < 1049 then decide (13 ≤ count1036 b) else decide (14 ≤ count1036 b))))) else (if i < 1057 then (if i < 1053 then (if i < 1051 then decide (15 ≤ count1036 b) else (if i < 1052 then decide (1 ≤ count1051 b) else decide (2 ≤ count1051 b))) else (if i < 1055 then (if i < 1054 then decide (1 ≤ count1053 b) else decide (2 ≤ count1053 b)) else (if i < 1056 then decide (1 ≤ count1055 b) else decide (2 ≤ count1055 b)))) else (if i < 1061 then (if i < 1059 then (if i < 1058 then decide (3 ≤ count1055 b) else decide (4 ≤ count1055 b)) else (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b))) else (if i < 1063 then (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b)) else (if i < 1064 then decide (1 ≤ count1063 b) else decide (2 ≤ count1063 b)))))))) else (if i < 1124 then (if i < 1094 then (if i < 1079 then (if i < 1072 then (if i < 1068 then (if i < 1066 then decide (3 ≤ count1063 b) else (if i < 1067 then decide (4 ≤ count1063 b) else decide (1 ≤ count1067 b))) else (if i < 1070 then (if i < 1069 then decide (2 ≤ count1067 b) else decide (3 ≤ count1067 b)) else (if i < 1071 then decide (4 ≤ count1067 b) else decide (5 ≤ count1067 b)))) else (if i < 1075 then (if i < 1073 then decide (6 ≤ count1067 b) else (if i < 1074 then decide (7 ≤ count1067 b) else decide (8 ≤ count1067 b))) else (if i < 1077 then (if i < 1076 then decide (1 ≤ count1075 b) else decide (2 ≤ count1075 b)) else (if i < 1078 then decide (1 ≤ count1077 b) else decide (2 ≤ count1077 b))))) else (if i < 1086 then (if i < 1082 then (if i < 1080 then decide (1 ≤ count1079 b) else (if i < 1081 then decide (2 ≤ count1079 b) else decide (3 ≤ count1079 b))) else (if i < 1084 then (if i < 1083 then decide (4 ≤ count1079 b) else decide (1 ≤ count1083 b)) else (if i < 1085 then decide (2 ≤ count1083 b) else decide (1 ≤ count1085 b)))) else (if i < 1090 then (if i < 1088 then (if i < 1087 then decide (2 ≤ count1085 b) else decide (1 ≤ count1087 b)) else (if i < 1089 then decide (2 ≤ count1087 b) else decide (3 ≤ count1087 b))) else (if i < 1092 then (if i < 1091 then decide (4 ≤ count1087 b) else decide (1 ≤ count1091 b)) else (if i < 1093 then decide (2 ≤ count1091 b) else decide (3 ≤ count1091 b)))))) else (if i < 1109 then (if i < 1101 then (if i < 1097 then (if i < 1095 then decide (4 ≤ count1091 b) else (if i < 1096 then decide (5 ≤ count1091 b) else decide (6 ≤ count1091 b))) else (if i < 1099 then (if i < 1098 then decide (7 ≤ count1091 b) else decide (8 ≤ count1091 b)) else (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b)))) else (if i < 1105 then (if i < 1103 then (if i < 1102 then decide (3 ≤ count1099 b) else decide (4 ≤ count1099 b)) else (if i < 1104 then decide (5 ≤ count1099 b) else decide (6 ≤ count1099 b))) else (if i < 1107 then (if i < 1106 then decide (7 ≤ count1099 b) else decide (8 ≤ count1099 b)) else (if i < 1108 then decide (9 ≤ count1099 b) else decide (10 ≤ count1099 b))))) else (if i < 1116 then (if i < 1112 then (if i < 1110 then decide (11 ≤ count1099 b) else (if i < 1111 then decide (12 ≤ count1099 b) else decide (13 ≤ count1099 b))) else (if i < 1114 then (if i < 1113 then decide (14 ≤ count1099 b) else decide (15 ≤ count1099 b)) else (if i < 1115 then decide (16 ≤ count1099 b) else decide (1 ≤ count1115 b)))) else (if i < 1120 then (if i < 1118 then (if i < 1117 then decide (2 ≤ count1115 b) else decide (3 ≤ count1115 b)) else (if i < 1119 then decide (4 ≤ count1115 b) else decide (5 ≤ count1115 b))) else (if i < 1122 then (if i < 1121 then decide (6 ≤ count1115 b) else decide (7 ≤ count1115 b)) else (if i < 1123 then decide (8 ≤ count1115 b) else decide (9 ≤ count1115 b))))))) else (if i < 1154 then (if i < 1139 then (if i < 1131 then (if i < 1127 then (if i < 1125 then decide (10 ≤ count1115 b) else (if i < 1126 then decide (11 ≤ count1115 b) else decide (12 ≤ count1115 b))) else (if i < 1129 then (if i < 1128 then decide (13 ≤ count1115 b) else decide (14 ≤ count1115 b)) else (if i < 1130 then decide (15 ≤ count1115 b) else decide (16 ≤ count1115 b)))) else (if i < 1135 then (if i < 1133 then (if i < 1132 then decide (17 ≤ count1115 b) else decide (18 ≤ count1115 b)) else (if i < 1134 then decide (19 ≤ count1115 b) else decide (20 ≤ count1115 b))) else (if i < 1137 then (if i < 1136 then decide (21 ≤ count1115 b) else decide (1 ≤ count1136 b)) else (if i < 1138 then decide (2 ≤ count1136 b) else decide (3 ≤ count1136 b))))) else (if i < 1146 then (if i < 1142 then (if i < 1140 then decide (4 ≤ count1136 b) else (if i < 1141 then decide (5 ≤ count1136 b) else decide (6 ≤ count1136 b))) else (if i < 1144 then (if i < 1143 then decide (7 ≤ count1136 b) else decide (8 ≤ count1136 b)) else (if i < 1145 then decide (9 ≤ count1136 b) else decide (10 ≤ count1136 b)))) else (if i < 1150 then (if i < 1148 then (if i < 1147 then decide (11 ≤ count1136 b) else decide (12 ≤ count1136 b)) else (if i < 1149 then decide (13 ≤ count1136 b) else decide (14 ≤ count1136 b))) else (if i < 1152 then (if i < 1151 then decide (15 ≤ count1136 b) else decide (16 ≤ count1136 b)) else (if i < 1153 then decide (17 ≤ count1136 b) else decide (18 ≤ count1136 b)))))) else (if i < 1169 then (if i < 1161 then (if i < 1157 then (if i < 1155 then decide (19 ≤ count1136 b) else (if i < 1156 then decide (20 ≤ count1136 b) else decide (21 ≤ count1136 b))) else (if i < 1159 then (if i < 1158 then decide (1 ≤ count1157 b) else decide (2 ≤ count1157 b)) else (if i < 1160 then decide (1 ≤ count1159 b) else decide (2 ≤ count1159 b)))) else (if i < 1165 then (if i < 1163 then (if i < 1162 then decide (1 ≤ count1161 b) else decide (2 ≤ count1161 b)) else (if i < 1164 then decide (3 ≤ count1161 b) else decide (4 ≤ count1161 b))) else (if i < 1167 then (if i < 1166 then decide (1 ≤ count1165 b) else decide (2 ≤ count1165 b)) else (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b))))) else (if i < 1176 then (if i < 1172 then (if i < 1170 then decide (1 ≤ count1169 b) else (if i < 1171 then decide (2 ≤ count1169 b) else decide (3 ≤ count1169 b))) else (if i < 1174 then (if i < 1173 then decide (4 ≤ count1169 b) else decide (1 ≤ count1173 b)) else (if i < 1175 then decide (2 ≤ count1173 b) else decide (3 ≤ count1173 b)))) else (if i < 1180 then (if i < 1178 then (if i < 1177 then decide (4 ≤ count1173 b) else decide (5 ≤ count1173 b)) else (if i < 1179 then decide (6 ≤ count1173 b) else decide (7 ≤ count1173 b))) else (if i < 1182 then (if i < 1181 then decide (8 ≤ count1173 b) else decide (1 ≤ count1181 b)) else (if i < 1183 then decide (2 ≤ count1181 b) else decide (1 ≤ count1183 b))))))))) else (if i < 1302 then (if i < 1243 then (if i < 1213 then (if i < 1198 then (if i < 1191 then (if i < 1187 then (if i < 1185 then decide (2 ≤ count1183 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))) else (if i < 1189 then (if i < 1188 then decide (3 ≤ count1185 b) else decide (4 ≤ count1185 b)) else (if i < 1190 then decide (1 ≤ count1189 b) else decide (2 ≤ count1189 b)))) else (if i < 1194 then (if i < 1192 then decide (1 ≤ count1191 b) else (if i < 1193 then decide (2 ≤ count1191 b) else decide (1 ≤ count1193 b))) else (if i < 1196 then (if i < 1195 then decide (2 ≤ count1193 b) else decide (3 ≤ count1193 b)) else (if i < 1197 then decide (4 ≤ count1193 b) else decide (1 ≤ count1197 b))))) else (if i < 1205 then (if i < 1201 then (if i < 1199 then decide (2 ≤ count1197 b) else (if i < 1200 then decide (3 ≤ count1197 b) else decide (4 ≤ count1197 b))) else (if i < 1203 then (if i < 1202 then decide (5 ≤ count1197 b) else decide (6 ≤ count1197 b)) else (if i < 1204 then decide (7 ≤ count1197 b) else decide (8 ≤ count1197 b)))) else (if i < 1209 then (if i < 1207 then (if i < 1206 then decide (1 ≤ count1205 b) else decide (2 ≤ count1205 b)) else (if i < 1208 then decide (3 ≤ count1205 b) else decide (4 ≤ count1205 b))) else (if i < 1211 then (if i < 1210 then decide (5 ≤ count1205 b) else decide (6 ≤ count1205 b)) else (if i < 1212 then decide (7 ≤ count1205 b) else decide (8 ≤ count1205 b)))))) else (if i < 1228 then (if i < 1220 then (if i < 1216 then (if i < 1214 then decide (9 ≤ count1205 b) else (if i < 1215 then decide (10 ≤ count1205 b) else decide (11 ≤ count1205 b))) else (if i < 1218 then (if i < 1217 then decide (12 ≤ count1205 b) else decide (13 ≤ count1205 b)) else (if i < 1219 then decide (14 ≤ count1205 b) else decide (15 ≤ count1205 b)))) else (if i < 1224 then (if i < 1222 then (if i < 1221 then decide (16 ≤ count1205 b) else decide (1 ≤ count1221 b)) else (if i < 1223 then decide (2 ≤ count1221 b) else decide (1 ≤ count1223 b))) else (if i < 1226 then (if i < 1225 then decide (2 ≤ count1223 b) else decide (1 ≤ count1225 b)) else (if i < 1227 then decide (2 ≤ count1225 b) else decide (3 ≤ count1225 b))))) else (if i < 1235 then (if i < 1231 then (if i < 1229 then decide (4 ≤ count1225 b) else (if i < 1230 then decide (1 ≤ count1229 b) else decide (2 ≤ count1229 b))) else (if i < 1233 then (if i < 1232 then decide (1 ≤ count1231 b) else decide (2 ≤ count1231 b)) else (if i < 1234 then decide (1 ≤ count1233 b) else decide (2 ≤ count1233 b)))) else (if i < 1239 then (if i < 1237 then (if i < 1236 then decide (3 ≤ count1233 b) else decide (4 ≤ count1233 b)) else (if i < 1238 then decide (1 ≤ count1237 b) else decide (2 ≤ count1237 b))) else (if i < 1241 then (if i < 1240 then decide (3 ≤ count1237 b) else decide (4 ≤ count1237 b)) else (if i < 1242 then decide (5 ≤ count1237 b) else decide (6 ≤ count1237 b))))))) else (if i < 1272 then (if i < 1257 then (if i < 1250 then (if i < 1246 then (if i < 1244 then decide (7 ≤ count1237 b) else (if i < 1245 then decide (8 ≤ count1237 b) else decide (1 ≤ count1245 b))) else (if i < 1248 then (if i < 1247 then decide (2 ≤ count1245 b) else decide (1 ≤ count1247 b)) else (if i < 1249 then decide (2 ≤ count1247 b) else decide (1 ≤ count1249 b)))) else (if i < 1253 then (if i < 1251 then decide (2 ≤ count1249 b) else (if i < 1252 then decide (3 ≤ count1249 b) else decide (4 ≤ count1249 b))) else (if i < 1255 then (if i < 1254 then decide (1 ≤ count1253 b) else decide (2 ≤ count1253 b)) else (if i < 1256 then decide (1 ≤ count1255 b) else decide (2 ≤ count1255 b))))) else (if i < 1264 then (if i < 1260 then (if i < 1258 then decide (1 ≤ count1257 b) else (if i < 1259 then decide (2 ≤ count1257 b) else decide (3 ≤ count1257 b))) else (if i < 1262 then (if i < 1261 then decide (1 ≤ count1260 b) else decide (2 ≤ count1260 b)) else (if i < 1263 then decide (3 ≤ count1260 b) else decide (4 ≤ count1260 b)))) else (if i < 1268 then (if i < 1266 then (if i < 1265 then decide (5 ≤ count1260 b) else decide (1 ≤ count1265 b)) else (if i < 1267 then decide (2 ≤ count1265 b) else decide (3 ≤ count1265 b))) else (if i < 1270 then (if i < 1269 then decide (4 ≤ count1265 b) else decide (5 ≤ count1265 b)) else (if i < 1271 then decide (6 ≤ count1265 b) else decide (7 ≤ count1265 b)))))) else (if i < 1287 then (if i < 1279 then (if i < 1275 then (if i < 1273 then decide (8 ≤ count1265 b) else (if i < 1274 then decide (9 ≤ count1265 b) else decide (1 ≤ count1274 b))) else (if i < 1277 then (if i < 1276 then decide (2 ≤ count1274 b) else decide (3 ≤ count1274 b)) else (if i < 1278 then decide (4 ≤ count1274 b) else decide (5 ≤ count1274 b)))) else (if i < 1283 then (if i < 1281 then (if i < 1280 then decide (6 ≤ count1274 b) else decide (7 ≤ count1274 b)) else (if i < 1282 then decide (8 ≤ count1274 b) else decide (9 ≤ count1274 b))) else (if i < 1285 then (if i < 1284 then decide (10 ≤ count1274 b) else decide (11 ≤ count1274 b)) else (if i < 1286 then decide (12 ≤ count1274 b) else decide (13 ≤ count1274 b))))) else (if i < 1294 then (if i < 1290 then (if i < 1288 then decide (14 ≤ count1274 b) else (if i < 1289 then decide (15 ≤ count1274 b) else decide (16 ≤ count1274 b))) else (if i < 1292 then (if i < 1291 then decide (17 ≤ count1274 b) else decide (1 ≤ count1291 b)) else (if i < 1293 then decide (2 ≤ count1291 b) else decide (3 ≤ count1291 b)))) else (if i < 1298 then (if i < 1296 then (if i < 1295 then decide (4 ≤ count1291 b) else decide (5 ≤ count1291 b)) else (if i < 1297 then decide (6 ≤ count1291 b) else decide (7 ≤ count1291 b))) else (if i < 1300 then (if i < 1299 then decide (8 ≤ count1291 b) else decide (9 ≤ count1291 b)) else (if i < 1301 then decide (10 ≤ count1291 b) else decide (11 ≤ count1291 b)))))))) else (if i < 1361 then (if i < 1331 then (if i < 1316 then (if i < 1309 then (if i < 1305 then (if i < 1303 then decide (12 ≤ count1291 b) else (if i < 1304 then decide (13 ≤ count1291 b) else decide (14 ≤ count1291 b))) else (if i < 1307 then (if i < 1306 then decide (15 ≤ count1291 b) else decide (16 ≤ count1291 b)) else (if i < 1308 then decide (17 ≤ count1291 b) else decide (18 ≤ count1291 b)))) else (if i < 1312 then (if i < 1310 then decide (19 ≤ count1291 b) else (if i < 1311 then decide (20 ≤ count1291 b) else decide (21 ≤ count1291 b))) else (if i < 1314 then (if i < 1313 then decide (22 ≤ count1291 b) else decide (23 ≤ count1291 b)) else (if i < 1315 then decide (24 ≤ count1291 b) else decide (25 ≤ count1291 b))))) else (if i < 1323 then (if i < 1319 then (if i < 1317 then decide (26 ≤ count1291 b) else (if i < 1318 then decide (27 ≤ count1291 b) else decide (28 ≤ count1291 b))) else (if i < 1321 then (if i < 1320 then decide (29 ≤ count1291 b) else decide (30 ≤ count1291 b)) else (if i < 1322 then decide (31 ≤ count1291 b) else decide (32 ≤ count1291 b)))) else (if i < 1327 then (if i < 1325 then (if i < 1324 then decide (33 ≤ count1291 b) else decide (1 ≤ count1324 b)) else (if i < 1326 then decide (2 ≤ count1324 b) else decide (1 ≤ count1326 b))) else (if i < 1329 then (if i < 1328 then decide (2 ≤ count1326 b) else decide (1 ≤ count1328 b)) else (if i < 1330 then decide (2 ≤ count1328 b) else decide (3 ≤ count1328 b)))))) else (if i < 1346 then (if i < 1338 then (if i < 1334 then (if i < 1332 then decide (4 ≤ count1328 b) else (if i < 1333 then decide (1 ≤ count1332 b) else decide (2 ≤ count1332 b))) else (if i < 1336 then (if i < 1335 then decide (1 ≤ count1334 b) else decide (2 ≤ count1334 b)) else (if i < 1337 then decide (1 ≤ count1336 b) else decide (2 ≤ count1336 b)))) else (if i < 1342 then (if i < 1340 then (if i < 1339 then decide (3 ≤ count1336 b) else decide (4 ≤ count1336 b)) else (if i < 1341 then decide (1 ≤ count1340 b) else decide (2 ≤ count1340 b))) else (if i < 1344 then (if i < 1343 then decide (3 ≤ count1340 b) else decide (4 ≤ count1340 b)) else (if i < 1345 then decide (5 ≤ count1340 b) else decide (6 ≤ count1340 b))))) else (if i < 1353 then (if i < 1349 then (if i < 1347 then decide (7 ≤ count1340 b) else (if i < 1348 then decide (8 ≤ count1340 b) else decide (1 ≤ count1348 b))) else (if i < 1351 then (if i < 1350 then decide (2 ≤ count1348 b) else decide (1 ≤ count1350 b)) else (if i < 1352 then decide (2 ≤ count1350 b) else decide (1 ≤ count1352 b)))) else (if i < 1357 then (if i < 1355 then (if i < 1354 then decide (2 ≤ count1352 b) else decide (3 ≤ count1352 b)) else (if i < 1356 then decide (4 ≤ count1352 b) else decide (1 ≤ count1356 b))) else (if i < 1359 then (if i < 1358 then decide (2 ≤ count1356 b) else decide (1 ≤ count1358 b)) else (if i < 1360 then decide (2 ≤ count1358 b) else decide (1 ≤ count1360 b))))))) else (if i < 1391 then (if i < 1376 then (if i < 1368 then (if i < 1364 then (if i < 1362 then decide (2 ≤ count1360 b) else (if i < 1363 then decide (3 ≤ count1360 b) else decide (1 ≤ count1363 b))) else (if i < 1366 then (if i < 1365 then decide (2 ≤ count1363 b) else decide (3 ≤ count1363 b)) else (if i < 1367 then decide (4 ≤ count1363 b) else decide (5 ≤ count1363 b)))) else (if i < 1372 then (if i < 1370 then (if i < 1369 then decide (1 ≤ count1368 b) else decide (2 ≤ count1368 b)) else (if i < 1371 then decide (3 ≤ count1368 b) else decide (4 ≤ count1368 b))) else (if i < 1374 then (if i < 1373 then decide (5 ≤ count1368 b) else decide (6 ≤ count1368 b)) else (if i < 1375 then decide (7 ≤ count1368 b) else decide (8 ≤ count1368 b))))) else (if i < 1383 then (if i < 1379 then (if i < 1377 then decide (9 ≤ count1368 b) else (if i < 1378 then decide (1 ≤ count1377 b) else decide (2 ≤ count1377 b))) else (if i < 1381 then (if i < 1380 then decide (3 ≤ count1377 b) else decide (4 ≤ count1377 b)) else (if i < 1382 then decide (5 ≤ count1377 b) else decide (6 ≤ count1377 b)))) else (if i < 1387 then (if i < 1385 then (if i < 1384 then decide (7 ≤ count1377 b) else decide (8 ≤ count1377 b)) else (if i < 1386 then decide (9 ≤ count1377 b) else decide (10 ≤ count1377 b))) else (if i < 1389 then (if i < 1388 then decide (11 ≤ count1377 b) else decide (12 ≤ count1377 b)) else (if i < 1390 then decide (13 ≤ count1377 b) else decide (14 ≤ count1377 b)))))) else (if i < 1406 then (if i < 1398 then (if i < 1394 then (if i < 1392 then decide (15 ≤ count1377 b) else (if i < 1393 then decide (16 ≤ count1377 b) else decide (17 ≤ count1377 b))) else (if i < 1396 then (if i < 1395 then decide (1 ≤ count1394 b) else decide (2 ≤ count1394 b)) else (if i < 1397 then decide (1 ≤ count1396 b) else decide (2 ≤ count1396 b)))) else (if i < 1402 then (if i < 1400 then (if i < 1399 then decide (1 ≤ count1398 b) else decide (2 ≤ count1398 b)) else (if i < 1401 then decide (3 ≤ count1398 b) else decide (4 ≤ count1398 b))) else (if i < 1404 then (if i < 1403 then decide (1 ≤ count1402 b) else decide (2 ≤ count1402 b)) else (if i < 1405 then decide (1 ≤ count1404 b) else decide (2 ≤ count1404 b))))) else (if i < 1413 then (if i < 1409 then (if i < 1407 then decide (1 ≤ count1406 b) else (if i < 1408 then decide (2 ≤ count1406 b) else decide (3 ≤ count1406 b))) else (if i < 1411 then (if i < 1410 then decide (4 ≤ count1406 b) else decide (1 ≤ count1410 b)) else (if i < 1412 then decide (2 ≤ count1410 b) else decide (3 ≤ count1410 b)))) else (if i < 1417 then (if i < 1415 then (if i < 1414 then decide (4 ≤ count1410 b) else decide (5 ≤ count1410 b)) else (if i < 1416 then decide (6 ≤ count1410 b) else decide (7 ≤ count1410 b))) else (if i < 1419 then (if i < 1418 then decide (8 ≤ count1410 b) else decide (1 ≤ count1418 b)) else (if i < 1420 then decide (2 ≤ count1418 b) else decide (1 ≤ count1420 b)))))))))) else (if i < 1658 then (if i < 1539 then (if i < 1480 then (if i < 1450 then (if i < 1435 then (if i < 1428 then (if i < 1424 then (if i < 1422 then decide (2 ≤ count1420 b) else (if i < 1423 then decide (1 ≤ count1422 b) else decide (2 ≤ count1422 b))) else (if i < 1426 then (if i < 1425 then decide (3 ≤ count1422 b) else decide (4 ≤ count1422 b)) else (if i < 1427 then decide (1 ≤ count1426 b) else decide (2 ≤ count1426 b)))) else (if i < 1431 then (if i < 1429 then decide (1 ≤ count1428 b) else (if i < 1430 then decide (2 ≤ count1428 b) else decide (1 ≤ count1430 b))) else (if i < 1433 then (if i < 1432 then decide (2 ≤ count1430 b) else decide (3 ≤ count1430 b)) else (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b))))) else (if i < 1442 then (if i < 1438 then (if i < 1436 then decide (3 ≤ count1433 b) else (if i < 1437 then decide (4 ≤ count1433 b) else decide (5 ≤ count1433 b))) else (if i < 1440 then (if i < 1439 then decide (1 ≤ count1438 b) else decide (2 ≤ count1438 b)) else (if i < 1441 then decide (3 ≤ count1438 b) else decide (4 ≤ count1438 b)))) else (if i < 1446 then (if i < 1444 then (if i < 1443 then decide (5 ≤ count1438 b) else decide (6 ≤ count1438 b)) else (if i < 1445 then decide (7 ≤ count1438 b) else decide (8 ≤ count1438 b))) else (if i < 1448 then (if i < 1447 then decide (9 ≤ count1438 b) else decide (1 ≤ count1447 b)) else (if i < 1449 then decide (2 ≤ count1447 b) else decide (3 ≤ count1447 b)))))) else (if i < 1465 then (if i < 1457 then (if i < 1453 then (if i < 1451 then decide (4 ≤ count1447 b) else (if i < 1452 then decide (5 ≤ count1447 b) else decide (6 ≤ count1447 b))) else (if i < 1455 then (if i < 1454 then decide (7 ≤ count1447 b) else decide (8 ≤ count1447 b)) else (if i < 1456 then decide (9 ≤ count1447 b) else decide (10 ≤ count1447 b)))) else (if i < 1461 then (if i < 1459 then (if i < 1458 then decide (11 ≤ count1447 b) else decide (12 ≤ count1447 b)) else (if i < 1460 then decide (13 ≤ count1447 b) else decide (14 ≤ count1447 b))) else (if i < 1463 then (if i < 1462 then decide (15 ≤ count1447 b) else decide (16 ≤ count1447 b)) else (if i < 1464 then decide (17 ≤ count1447 b) else decide (1 ≤ count1464 b))))) else (if i < 1472 then (if i < 1468 then (if i < 1466 then decide (2 ≤ count1464 b) else (if i < 1467 then decide (3 ≤ count1464 b) else decide (4 ≤ count1464 b))) else (if i < 1470 then (if i < 1469 then decide (5 ≤ count1464 b) else decide (6 ≤ count1464 b)) else (if i < 1471 then decide (7 ≤ count1464 b) else decide (8 ≤ count1464 b)))) else (if i < 1476 then (if i < 1474 then (if i < 1473 then decide (9 ≤ count1464 b) else decide (10 ≤ count1464 b)) else (if i < 1475 then decide (11 ≤ count1464 b) else decide (12 ≤ count1464 b))) else (if i < 1478 then (if i < 1477 then decide (13 ≤ count1464 b) else decide (14 ≤ count1464 b)) else (if i < 1479 then decide (15 ≤ count1464 b) else decide (16 ≤ count1464 b))))))) else (if i < 1509 then (if i < 1494 then (if i < 1487 then (if i < 1483 then (if i < 1481 then decide (17 ≤ count1464 b) else (if i < 1482 then decide (18 ≤ count1464 b) else decide (19 ≤ count1464 b))) else (if i < 1485 then (if i < 1484 then decide (20 ≤ count1464 b) else decide (21 ≤ count1464 b)) else (if i < 1486 then decide (22 ≤ count1464 b) else decide (23 ≤ count1464 b)))) else (if i < 1490 then (if i < 1488 then decide (24 ≤ count1464 b) else (if i < 1489 then decide (25 ≤ count1464 b) else decide (26 ≤ count1464 b))) else (if i < 1492 then (if i < 1491 then decide (27 ≤ count1464 b) else decide (28 ≤ count1464 b)) else (if i < 1493 then decide (29 ≤ count1464 b) else decide (30 ≤ count1464 b))))) else (if i < 1501 then (if i < 1497 then (if i < 1495 then decide (31 ≤ count1464 b) else (if i < 1496 then decide (32 ≤ count1464 b) else decide (33 ≤ count1464 b))) else (if i < 1499 then (if i < 1498 then decide (34 ≤ count1464 b) else decide (1 ≤ count1498 b)) else (if i < 1500 then decide (2 ≤ count1498 b) else decide (3 ≤ count1498 b)))) else (if i < 1505 then (if i < 1503 then (if i < 1502 then decide (4 ≤ count1498 b) else decide (5 ≤ count1498 b)) else (if i < 1504 then decide (6 ≤ count1498 b) else decide (7 ≤ count1498 b))) else (if i < 1507 then (if i < 1506 then decide (8 ≤ count1498 b) else decide (9 ≤ count1498 b)) else (if i < 1508 then decide (10 ≤ count1498 b) else decide (11 ≤ count1498 b)))))) else (if i < 1524 then (if i < 1516 then (if i < 1512 then (if i < 1510 then decide (12 ≤ count1498 b) else (if i < 1511 then decide (13 ≤ count1498 b) else decide (14 ≤ count1498 b))) else (if i < 1514 then (if i < 1513 then decide (15 ≤ count1498 b) else decide (16 ≤ count1498 b)) else (if i < 1515 then decide (17 ≤ count1498 b) else decide (18 ≤ count1498 b)))) else (if i < 1520 then (if i < 1518 then (if i < 1517 then decide (19 ≤ count1498 b) else decide (20 ≤ count1498 b)) else (if i < 1519 then decide (21 ≤ count1498 b) else decide (22 ≤ count1498 b))) else (if i < 1522 then (if i < 1521 then decide (23 ≤ count1498 b) else decide (24 ≤ count1498 b)) else (if i < 1523 then decide (25 ≤ count1498 b) else decide (26 ≤ count1498 b))))) else (if i < 1531 then (if i < 1527 then (if i < 1525 then decide (27 ≤ count1498 b) else (if i < 1526 then decide (28 ≤ count1498 b) else decide (29 ≤ count1498 b))) else (if i < 1529 then (if i < 1528 then decide (30 ≤ count1498 b) else decide (31 ≤ count1498 b)) else (if i < 1530 then decide (32 ≤ count1498 b) else decide (33 ≤ count1498 b)))) else (if i < 1535 then (if i < 1533 then (if i < 1532 then decide (34 ≤ count1498 b) else decide (35 ≤ count1498 b)) else (if i < 1534 then decide (36 ≤ count1498 b) else decide (37 ≤ count1498 b))) else (if i < 1537 then (if i < 1536 then decide (38 ≤ count1498 b) else decide (39 ≤ count1498 b)) else (if i < 1538 then decide (40 ≤ count1498 b) else decide (41 ≤ count1498 b)))))))) else (if i < 1598 then (if i < 1568 then (if i < 1553 then (if i < 1546 then (if i < 1542 then (if i < 1540 then decide (42 ≤ count1498 b) else (if i < 1541 then decide (1 ≤ count1540 b) else decide (2 ≤ count1540 b))) else (if i < 1544 then (if i < 1543 then decide (1 ≤ count1542 b) else decide (2 ≤ count1542 b)) else (if i < 1545 then decide (1 ≤ count1544 b) else decide (2 ≤ count1544 b)))) else (if i < 1549 then (if i < 1547 then decide (3 ≤ count1544 b) else (if i < 1548 then decide (4 ≤ count1544 b) else decide (1 ≤ count1548 b))) else (if i < 1551 then (if i < 1550 then decide (2 ≤ count1548 b) else decide (1 ≤ count1550 b)) else (if i < 1552 then decide (2 ≤ count1550 b) else decide (1 ≤ count1552 b))))) else (if i < 1560 then (if i < 1556 then (if i < 1554 then decide (2 ≤ count1552 b) else (if i < 1555 then decide (3 ≤ count1552 b) else decide (4 ≤ count1552 b))) else (if i < 1558 then (if i < 1557 then decide (1 ≤ count1556 b) else decide (2 ≤ count1556 b)) else (if i < 1559 then decide (3 ≤ count1556 b) else decide (4 ≤ count1556 b)))) else (if i < 1564 then (if i < 1562 then (if i < 1561 then decide (5 ≤ count1556 b) else decide (6 ≤ count1556 b)) else (if i < 1563 then decide (7 ≤ count1556 b) else decide (8 ≤ count1556 b))) else (if i < 1566 then (if i < 1565 then decide (1 ≤ count1564 b) else decide (2 ≤ count1564 b)) else (if i < 1567 then decide (1 ≤ count1566 b) else decide (2 ≤ count1566 b)))))) else (if i < 1583 then (if i < 1575 then (if i < 1571 then (if i < 1569 then decide (1 ≤ count1568 b) else (if i < 1570 then decide (2 ≤ count1568 b) else decide (3 ≤ count1568 b))) else (if i < 1573 then (if i < 1572 then decide (4 ≤ count1568 b) else decide (1 ≤ count1572 b)) else (if i < 1574 then decide (2 ≤ count1572 b) else decide (1 ≤ count1574 b)))) else (if i < 1579 then (if i < 1577 then (if i < 1576 then decide (2 ≤ count1574 b) else decide (1 ≤ count1576 b)) else (if i < 1578 then decide (2 ≤ count1576 b) else decide (3 ≤ count1576 b))) else (if i < 1581 then (if i < 1580 then decide (4 ≤ count1576 b) else decide (1 ≤ count1580 b)) else (if i < 1582 then decide (2 ≤ count1580 b) else decide (3 ≤ count1580 b))))) else (if i < 1590 then (if i < 1586 then (if i < 1584 then decide (4 ≤ count1580 b) else (if i < 1585 then decide (5 ≤ count1580 b) else decide (6 ≤ count1580 b))) else (if i < 1588 then (if i < 1587 then decide (7 ≤ count1580 b) else decide (8 ≤ count1580 b)) else (if i < 1589 then decide (1 ≤ count1588 b) else decide (2 ≤ count1588 b)))) else (if i < 1594 then (if i < 1592 then (if i < 1591 then decide (3 ≤ count1588 b) else decide (4 ≤ count1588 b)) else (if i < 1593 then decide (5 ≤ count1588 b) else decide (6 ≤ count1588 b))) else (if i < 1596 then (if i < 1595 then decide (7 ≤ count1588 b) else decide (8 ≤ count1588 b)) else (if i < 1597 then decide (9 ≤ count1588 b) else decide (10 ≤ count1588 b))))))) else (if i < 1628 then (if i < 1613 then (if i < 1605 then (if i < 1601 then (if i < 1599 then decide (11 ≤ count1588 b) else (if i < 1600 then decide (12 ≤ count1588 b) else decide (13 ≤ count1588 b))) else (if i < 1603 then (if i < 1602 then decide (14 ≤ count1588 b) else decide (15 ≤ count1588 b)) else (if i < 1604 then decide (16 ≤ count1588 b) else decide (1 ≤ count1604 b)))) else (if i < 1609 then (if i < 1607 then (if i < 1606 then decide (2 ≤ count1604 b) else decide (1 ≤ count1606 b)) else (if i < 1608 then decide (2 ≤ count1606 b) else decide (1 ≤ count1608 b))) else (if i < 1611 then (if i < 1610 then decide (2 ≤ count1608 b) else decide (3 ≤ count1608 b)) else (if i < 1612 then decide (4 ≤ count1608 b) else decide (1 ≤ count1612 b))))) else (if i < 1620 then (if i < 1616 then (if i < 1614 then decide (2 ≤ count1612 b) else (if i < 1615 then decide (1 ≤ count1614 b) else decide (2 ≤ count1614 b))) else (if i < 1618 then (if i < 1617 then decide (1 ≤ count1616 b) else decide (2 ≤ count1616 b)) else (if i < 1619 then decide (3 ≤ count1616 b) else decide (4 ≤ count1616 b)))) else (if i < 1624 then (if i < 1622 then (if i < 1621 then decide (1 ≤ count1620 b) else decide (2 ≤ count1620 b)) else (if i < 1623 then decide (3 ≤ count1620 b) else decide (4 ≤ count1620 b))) else (if i < 1626 then (if i < 1625 then decide (5 ≤ count1620 b) else decide (6 ≤ count1620 b)) else (if i < 1627 then decide (7 ≤ count1620 b) else decide (8 ≤ count1620 b)))))) else (if i < 1643 then (if i < 1635 then (if i < 1631 then (if i < 1629 then decide (1 ≤ count1628 b) else (if i < 1630 then decide (2 ≤ count1628 b) else decide (1 ≤ count1630 b))) else (if i < 1633 then (if i < 1632 then decide (2 ≤ count1630 b) else decide (1 ≤ count1632 b)) else (if i < 1634 then decide (2 ≤ count1632 b) else decide (3 ≤ count1632 b)))) else (if i < 1639 then (if i < 1637 then (if i < 1636 then decide (4 ≤ count1632 b) else decide (1 ≤ count1636 b)) else (if i < 1638 then decide (2 ≤ count1636 b) else decide (1 ≤ count1638 b))) else (if i < 1641 then (if i < 1640 then decide (2 ≤ count1638 b) else decide (1 ≤ count1640 b)) else (if i < 1642 then decide (2 ≤ count1640 b) else decide (3 ≤ count1640 b))))) else (if i < 1650 then (if i < 1646 then (if i < 1644 then decide (1 ≤ count1643 b) else (if i < 1645 then decide (2 ≤ count1643 b) else decide (3 ≤ count1643 b))) else (if i < 1648 then (if i < 1647 then decide (4 ≤ count1643 b) else decide (5 ≤ count1643 b)) else (if i < 1649 then decide (1 ≤ count1648 b) else decide (2 ≤ count1648 b)))) else (if i < 1654 then (if i < 1652 then (if i < 1651 then decide (3 ≤ count1648 b) else decide (4 ≤ count1648 b)) else (if i < 1653 then decide (5 ≤ count1648 b) else decide (6 ≤ count1648 b))) else (if i < 1656 then (if i < 1655 then decide (7 ≤ count1648 b) else decide (8 ≤ count1648 b)) else (if i < 1657 then decide (9 ≤ count1648 b) else decide (1 ≤ count1657 b))))))))) else (if i < 1776 then (if i < 1717 then (if i < 1687 then (if i < 1672 then (if i < 1665 then (if i < 1661 then (if i < 1659 then decide (2 ≤ count1657 b) else (if i < 1660 then decide (3 ≤ count1657 b) else decide (4 ≤ count1657 b))) else (if i < 1663 then (if i < 1662 then decide (5 ≤ count1657 b) else decide (6 ≤ count1657 b)) else (if i < 1664 then decide (7 ≤ count1657 b) else decide (8 ≤ count1657 b)))) else (if i < 1668 then (if i < 1666 then decide (9 ≤ count1657 b) else (if i < 1667 then decide (10 ≤ count1657 b) else decide (11 ≤ count1657 b))) else (if i < 1670 then (if i < 1669 then decide (12 ≤ count1657 b) else decide (13 ≤ count1657 b)) else (if i < 1671 then decide (14 ≤ count1657 b) else decide (15 ≤ count1657 b))))) else (if i < 1679 then (if i < 1675 then (if i < 1673 then decide (16 ≤ count1657 b) else (if i < 1674 then decide (17 ≤ count1657 b) else decide (1 ≤ count1674 b))) else (if i < 1677 then (if i < 1676 then decide (2 ≤ count1674 b) else decide (3 ≤ count1674 b)) else (if i < 1678 then decide (4 ≤ count1674 b) else decide (5 ≤ count1674 b)))) else (if i < 1683 then (if i < 1681 then (if i < 1680 then decide (6 ≤ count1674 b) else decide (7 ≤ count1674 b)) else (if i < 1682 then decide (8 ≤ count1674 b) else decide (9 ≤ count1674 b))) else (if i < 1685 then (if i < 1684 then decide (10 ≤ count1674 b) else decide (11 ≤ count1674 b)) else (if i < 1686 then decide (12 ≤ count1674 b) else decide (13 ≤ count1674 b)))))) else (if i < 1702 then (if i < 1694 then (if i < 1690 then (if i < 1688 then decide (14 ≤ count1674 b) else (if i < 1689 then decide (15 ≤ count1674 b) else decide (16 ≤ count1674 b))) else (if i < 1692 then (if i < 1691 then decide (17 ≤ count1674 b) else decide (18 ≤ count1674 b)) else (if i < 1693 then decide (19 ≤ count1674 b) else decide (20 ≤ count1674 b)))) else (if i < 1698 then (if i < 1696 then (if i < 1695 then decide (21 ≤ count1674 b) else decide (22 ≤ count1674 b)) else (if i < 1697 then decide (23 ≤ count1674 b) else decide (24 ≤ count1674 b))) else (if i < 1700 then (if i < 1699 then decide (25 ≤ count1674 b) else decide (26 ≤ count1674 b)) else (if i < 1701 then decide (27 ≤ count1674 b) else decide (1 ≤ count1701 b))))) else (if i < 1709 then (if i < 1705 then (if i < 1703 then decide (2 ≤ count1701 b) else (if i < 1704 then decide (1 ≤ count1703 b) else decide (2 ≤ count1703 b))) else (if i < 1707 then (if i < 1706 then decide (1 ≤ count1705 b) else decide (2 ≤ count1705 b)) else (if i < 1708 then decide (3 ≤ count1705 b) else decide (4 ≤ count1705 b)))) else (if i < 1713 then (if i < 1711 then (if i < 1710 then decide (1 ≤ count1709 b) else decide (2 ≤ count1709 b)) else (if i < 1712 then decide (1 ≤ count1711 b) else decide (2 ≤ count1711 b))) else (if i < 1715 then (if i < 1714 then decide (1 ≤ count1713 b) else decide (2 ≤ count1713 b)) else (if i < 1716 then decide (3 ≤ count1713 b) else decide (4 ≤ count1713 b))))))) else (if i < 1746 then (if i < 1731 then (if i < 1724 then (if i < 1720 then (if i < 1718 then decide (1 ≤ count1717 b) else (if i < 1719 then decide (2 ≤ count1717 b) else decide (3 ≤ count1717 b))) else (if i < 1722 then (if i < 1721 then decide (4 ≤ count1717 b) else decide (5 ≤ count1717 b)) else (if i < 1723 then decide (6 ≤ count1717 b) else decide (7 ≤ count1717 b)))) else (if i < 1727 then (if i < 1725 then decide (8 ≤ count1717 b) else (if i < 1726 then decide (1 ≤ count1725 b) else decide (2 ≤ count1725 b))) else (if i < 1729 then (if i < 1728 then decide (1 ≤ count1727 b) else decide (2 ≤ count1727 b)) else (if i < 1730 then decide (1 ≤ count1729 b) else decide (2 ≤ count1729 b))))) else (if i < 1738 then (if i < 1734 then (if i < 1732 then decide (3 ≤ count1729 b) else (if i < 1733 then decide (4 ≤ count1729 b) else decide (1 ≤ count1733 b))) else (if i < 1736 then (if i < 1735 then decide (2 ≤ count1733 b) else decide (1 ≤ count1735 b)) else (if i < 1737 then decide (2 ≤ count1735 b) else decide (1 ≤ count1737 b)))) else (if i < 1742 then (if i < 1740 then (if i < 1739 then decide (2 ≤ count1737 b) else decide (3 ≤ count1737 b)) else (if i < 1741 then decide (1 ≤ count1740 b) else decide (2 ≤ count1740 b))) else (if i < 1744 then (if i < 1743 then decide (3 ≤ count1740 b) else decide (4 ≤ count1740 b)) else (if i < 1745 then decide (5 ≤ count1740 b) else decide (1 ≤ count1745 b)))))) else (if i < 1761 then (if i < 1753 then (if i < 1749 then (if i < 1747 then decide (2 ≤ count1745 b) else (if i < 1748 then decide (3 ≤ count1745 b) else decide (4 ≤ count1745 b))) else (if i < 1751 then (if i < 1750 then decide (5 ≤ count1745 b) else decide (6 ≤ count1745 b)) else (if i < 1752 then decide (7 ≤ count1745 b) else decide (8 ≤ count1745 b)))) else (if i < 1757 then (if i < 1755 then (if i < 1754 then decide (9 ≤ count1745 b) else decide (1 ≤ count1754 b)) else (if i < 1756 then decide (2 ≤ count1754 b) else decide (3 ≤ count1754 b))) else (if i < 1759 then (if i < 1758 then decide (4 ≤ count1754 b) else decide (5 ≤ count1754 b)) else (if i < 1760 then decide (6 ≤ count1754 b) else decide (7 ≤ count1754 b))))) else (if i < 1768 then (if i < 1764 then (if i < 1762 then decide (8 ≤ count1754 b) else (if i < 1763 then decide (9 ≤ count1754 b) else decide (10 ≤ count1754 b))) else (if i < 1766 then (if i < 1765 then decide (11 ≤ count1754 b) else decide (12 ≤ count1754 b)) else (if i < 1767 then decide (13 ≤ count1754 b) else decide (14 ≤ count1754 b)))) else (if i < 1772 then (if i < 1770 then (if i < 1769 then decide (15 ≤ count1754 b) else decide (16 ≤ count1754 b)) else (if i < 1771 then decide (17 ≤ count1754 b) else decide (1 ≤ count1771 b))) else (if i < 1774 then (if i < 1773 then decide (2 ≤ count1771 b) else decide (1 ≤ count1773 b)) else (if i < 1775 then decide (2 ≤ count1773 b) else decide (1 ≤ count1775 b)))))))) else (if i < 1835 then (if i < 1805 then (if i < 1790 then (if i < 1783 then (if i < 1779 then (if i < 1777 then decide (2 ≤ count1775 b) else (if i < 1778 then decide (3 ≤ count1775 b) else decide (4 ≤ count1775 b))) else (if i < 1781 then (if i < 1780 then decide (1 ≤ count1779 b) else decide (2 ≤ count1779 b)) else (if i < 1782 then decide (1 ≤ count1781 b) else decide (2 ≤ count1781 b)))) else (if i < 1786 then (if i < 1784 then decide (1 ≤ count1783 b) else (if i < 1785 then decide (2 ≤ count1783 b) else decide (3 ≤ count1783 b))) else (if i < 1788 then (if i < 1787 then decide (4 ≤ count1783 b) else decide (1 ≤ count1787 b)) else (if i < 1789 then decide (2 ≤ count1787 b) else decide (3 ≤ count1787 b))))) else (if i < 1797 then (if i < 1793 then (if i < 1791 then decide (4 ≤ count1787 b) else (if i < 1792 then decide (5 ≤ count1787 b) else decide (6 ≤ count1787 b))) else (if i < 1795 then (if i < 1794 then decide (7 ≤ count1787 b) else decide (8 ≤ count1787 b)) else (if i < 1796 then decide (1 ≤ count1795 b) else decide (2 ≤ count1795 b)))) else (if i < 1801 then (if i < 1799 then (if i < 1798 then decide (1 ≤ count1797 b) else decide (2 ≤ count1797 b)) else (if i < 1800 then decide (1 ≤ count1799 b) else decide (2 ≤ count1799 b))) else (if i < 1803 then (if i < 1802 then decide (3 ≤ count1799 b) else decide (4 ≤ count1799 b)) else (if i < 1804 then decide (1 ≤ count1803 b) else decide (2 ≤ count1803 b)))))) else (if i < 1820 then (if i < 1812 then (if i < 1808 then (if i < 1806 then decide (1 ≤ count1805 b) else (if i < 1807 then decide (2 ≤ count1805 b) else decide (1 ≤ count1807 b))) else (if i < 1810 then (if i < 1809 then decide (2 ≤ count1807 b) else decide (3 ≤ count1807 b)) else (if i < 1811 then decide (1 ≤ count1810 b) else decide (2 ≤ count1810 b)))) else (if i < 1816 then (if i < 1814 then (if i < 1813 then decide (3 ≤ count1810 b) else decide (4 ≤ count1810 b)) else (if i < 1815 then decide (5 ≤ count1810 b) else decide (1 ≤ count1815 b))) else (if i < 1818 then (if i < 1817 then decide (2 ≤ count1815 b) else decide (3 ≤ count1815 b)) else (if i < 1819 then decide (4 ≤ count1815 b) else decide (5 ≤ count1815 b))))) else (if i < 1827 then (if i < 1823 then (if i < 1821 then decide (6 ≤ count1815 b) else (if i < 1822 then decide (7 ≤ count1815 b) else decide (8 ≤ count1815 b))) else (if i < 1825 then (if i < 1824 then decide (9 ≤ count1815 b) else decide (1 ≤ count1824 b)) else (if i < 1826 then decide (2 ≤ count1824 b) else decide (3 ≤ count1824 b)))) else (if i < 1831 then (if i < 1829 then (if i < 1828 then decide (4 ≤ count1824 b) else decide (5 ≤ count1824 b)) else (if i < 1830 then decide (6 ≤ count1824 b) else decide (7 ≤ count1824 b))) else (if i < 1833 then (if i < 1832 then decide (8 ≤ count1824 b) else decide (9 ≤ count1824 b)) else (if i < 1834 then decide (10 ≤ count1824 b) else decide (11 ≤ count1824 b))))))) else (if i < 1865 then (if i < 1850 then (if i < 1842 then (if i < 1838 then (if i < 1836 then decide (12 ≤ count1824 b) else (if i < 1837 then decide (13 ≤ count1824 b) else decide (14 ≤ count1824 b))) else (if i < 1840 then (if i < 1839 then decide (15 ≤ count1824 b) else decide (16 ≤ count1824 b)) else (if i < 1841 then decide (17 ≤ count1824 b) else decide (1 ≤ count1841 b)))) else (if i < 1846 then (if i < 1844 then (if i < 1843 then decide (2 ≤ count1841 b) else decide (3 ≤ count1841 b)) else (if i < 1845 then decide (4 ≤ count1841 b) else decide (5 ≤ count1841 b))) else (if i < 1848 then (if i < 1847 then decide (6 ≤ count1841 b) else decide (7 ≤ count1841 b)) else (if i < 1849 then decide (8 ≤ count1841 b) else decide (9 ≤ count1841 b))))) else (if i < 1857 then (if i < 1853 then (if i < 1851 then decide (10 ≤ count1841 b) else (if i < 1852 then decide (11 ≤ count1841 b) else decide (12 ≤ count1841 b))) else (if i < 1855 then (if i < 1854 then decide (13 ≤ count1841 b) else decide (14 ≤ count1841 b)) else (if i < 1856 then decide (15 ≤ count1841 b) else decide (16 ≤ count1841 b)))) else (if i < 1861 then (if i < 1859 then (if i < 1858 then decide (17 ≤ count1841 b) else decide (18 ≤ count1841 b)) else (if i < 1860 then decide (19 ≤ count1841 b) else decide (20 ≤ count1841 b))) else (if i < 1863 then (if i < 1862 then decide (21 ≤ count1841 b) else decide (22 ≤ count1841 b)) else (if i < 1864 then decide (23 ≤ count1841 b) else decide (24 ≤ count1841 b)))))) else (if i < 1880 then (if i < 1872 then (if i < 1868 then (if i < 1866 then decide (25 ≤ count1841 b) else (if i < 1867 then decide (26 ≤ count1841 b) else decide (27 ≤ count1841 b))) else (if i < 1870 then (if i < 1869 then decide (1 ≤ count1868 b) else decide (2 ≤ count1868 b)) else (if i < 1871 then decide (3 ≤ count1868 b) else decide (4 ≤ count1868 b)))) else (if i < 1876 then (if i < 1874 then (if i < 1873 then decide (5 ≤ count1868 b) else decide (6 ≤ count1868 b)) else (if i < 1875 then decide (7 ≤ count1868 b) else decide (8 ≤ count1868 b))) else (if i < 1878 then (if i < 1877 then decide (9 ≤ count1868 b) else decide (10 ≤ count1868 b)) else (if i < 1879 then decide (11 ≤ count1868 b) else decide (12 ≤ count1868 b))))) else (if i < 1887 then (if i < 1883 then (if i < 1881 then decide (13 ≤ count1868 b) else (if i < 1882 then decide (14 ≤ count1868 b) else decide (15 ≤ count1868 b))) else (if i < 1885 then (if i < 1884 then decide (16 ≤ count1868 b) else decide (17 ≤ count1868 b)) else (if i < 1886 then decide (18 ≤ count1868 b) else decide (19 ≤ count1868 b)))) else (if i < 1891 then (if i < 1889 then (if i < 1888 then decide (20 ≤ count1868 b) else decide (21 ≤ count1868 b)) else (if i < 1890 then decide (22 ≤ count1868 b) else decide (23 ≤ count1868 b))) else (if i < 1893 then (if i < 1892 then decide (24 ≤ count1868 b) else decide (25 ≤ count1868 b)) else (if i < 1894 then decide (26 ≤ count1868 b) else decide (27 ≤ count1868 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (33 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (35 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (37 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (43 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (45 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (47 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (49 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (52 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (56 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (60 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (62 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (63 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (97 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (160 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (161 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (164 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (166 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (167 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (168 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (169 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (171 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (172 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (174 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (181 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (182 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (183 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (184 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (185 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (186 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (187 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (189 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (226 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (227 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (228 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (229 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (233 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (234 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (235 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (237 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (239 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (240 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (241 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (243 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (244 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (246 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (248 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (252 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (254 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (255 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (288 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (289 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (290 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (292 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (293 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (294 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (296 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (298 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (299 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (300 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (302 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (309 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (310 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (311 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (312 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (313 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (315 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (317 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (319 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (354 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (355 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (356 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (357 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (361 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (362 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (363 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (365 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (367 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (368 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (369 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (371 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (372 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (376 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (380 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (382 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (383 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (416 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (417 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (418 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (419 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (420 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (423 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (425 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (426 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (429 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (431 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (432 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (433 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (434 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (435 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (436 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (442 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (444 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (445 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (446 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (447 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (480 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (482 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (483 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (484 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (485 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (486 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (487 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (488 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (489 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (490 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (492 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (493 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (494 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (497 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (499 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (501 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (502 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (503 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (504 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (InPath q (505 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (InPath q (506 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (InPath q (507 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (InPath q (509 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (35 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (37 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (45 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (47 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (49 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (52 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (56 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (60 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (62 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (63 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (164 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (168 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (169 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (172 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (174 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (181 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (183 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (185 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (187 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (226 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (235 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (237 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (239 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (241 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (243 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (252 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (290 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (294 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (299 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (300 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (302 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (309 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (311 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (313 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (315 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (354 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (365 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (367 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (369 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (371 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (372 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (380 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (382 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (383 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (416 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (429 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (431 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (433 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (434 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (442 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (444 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (485 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (489 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (490 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (494 : Vertex)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (BallClauseLogic.Endpoint q (501 : Vertex)) := rfl
theorem value250 (q : Snake 81) : valuation q 250 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (BallClauseLogic.Endpoint q (503 : Vertex)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (BallClauseLogic.Endpoint q (504 : Vertex)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (BallClauseLogic.Endpoint q (505 : Vertex)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (BallClauseLogic.Endpoint q (507 : Vertex)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value284 (q : Snake 81) : valuation q 284 = decide (2 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value298 (q : Snake 81) : valuation q 298 = decide (2 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value310 (q : Snake 81) : valuation q 310 = decide (2 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value316 (q : Snake 81) : valuation q 316 = decide (2 ≤ count315 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value336 (q : Snake 81) : valuation q 336 = decide (2 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value440 (q : Snake 81) : valuation q 440 = decide (2 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value442 (q : Snake 81) : valuation q 442 = decide (2 ≤ count441 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value456 (q : Snake 81) : valuation q 456 = decide (2 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value470 (q : Snake 81) : valuation q 470 = decide (2 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value472 (q : Snake 81) : valuation q 472 = decide (2 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value478 (q : Snake 81) : valuation q 478 = decide (2 ≤ count477 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value486 (q : Snake 81) : valuation q 486 = decide (2 ≤ count485 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value491 (q : Snake 81) : valuation q 491 = decide (1 ≤ count491 (baseVal q)) := rfl
theorem value495 (q : Snake 81) : valuation q 495 = decide (1 ≤ count495 (baseVal q)) := rfl
theorem value496 (q : Snake 81) : valuation q 496 = decide (2 ≤ count495 (baseVal q)) := rfl
theorem value497 (q : Snake 81) : valuation q 497 = decide (1 ≤ count497 (baseVal q)) := rfl
theorem value498 (q : Snake 81) : valuation q 498 = decide (2 ≤ count497 (baseVal q)) := rfl
theorem value499 (q : Snake 81) : valuation q 499 = decide (1 ≤ count499 (baseVal q)) := rfl
theorem value500 (q : Snake 81) : valuation q 500 = decide (2 ≤ count499 (baseVal q)) := rfl
theorem value501 (q : Snake 81) : valuation q 501 = decide (1 ≤ count501 (baseVal q)) := rfl
theorem value502 (q : Snake 81) : valuation q 502 = decide (2 ≤ count501 (baseVal q)) := rfl
theorem value503 (q : Snake 81) : valuation q 503 = decide (1 ≤ count503 (baseVal q)) := rfl
theorem value504 (q : Snake 81) : valuation q 504 = decide (2 ≤ count503 (baseVal q)) := rfl
theorem value505 (q : Snake 81) : valuation q 505 = decide (1 ≤ count505 (baseVal q)) := rfl
theorem value506 (q : Snake 81) : valuation q 506 = decide (2 ≤ count505 (baseVal q)) := rfl
theorem value508 (q : Snake 81) : valuation q 508 = decide (2 ≤ count507 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (1 ≤ count1540 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (2 ≤ count1540 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (1 ≤ count1542 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (2 ≤ count1542 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (1 ≤ count1544 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (2 ≤ count1544 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (3 ≤ count1544 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (4 ≤ count1544 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (1 ≤ count1548 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (2 ≤ count1548 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (1 ≤ count1550 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (1 ≤ count1552 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (2 ≤ count1552 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (3 ≤ count1552 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (3 ≤ count1556 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (4 ≤ count1556 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (5 ≤ count1556 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (6 ≤ count1556 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (7 ≤ count1556 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (1 ≤ count1566 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (2 ≤ count1566 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (1 ≤ count1568 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (2 ≤ count1568 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (3 ≤ count1568 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (4 ≤ count1568 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (1 ≤ count1572 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (2 ≤ count1572 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (1 ≤ count1574 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (2 ≤ count1574 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (1 ≤ count1576 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (2 ≤ count1576 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (3 ≤ count1576 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (4 ≤ count1576 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (3 ≤ count1580 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (4 ≤ count1580 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (5 ≤ count1580 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (6 ≤ count1580 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (7 ≤ count1580 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (8 ≤ count1580 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (5 ≤ count1588 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (6 ≤ count1588 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (7 ≤ count1588 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (8 ≤ count1588 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (9 ≤ count1588 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (10 ≤ count1588 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (11 ≤ count1588 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (12 ≤ count1588 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (13 ≤ count1588 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (1 ≤ count1604 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (2 ≤ count1604 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (1 ≤ count1606 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (2 ≤ count1606 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (1 ≤ count1608 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (2 ≤ count1608 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (3 ≤ count1608 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (4 ≤ count1608 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (1 ≤ count1612 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (2 ≤ count1612 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (1 ≤ count1614 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (2 ≤ count1614 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (1 ≤ count1616 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (2 ≤ count1616 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (3 ≤ count1616 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (4 ≤ count1616 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (1 ≤ count1620 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (2 ≤ count1620 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (3 ≤ count1620 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (4 ≤ count1620 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (5 ≤ count1620 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (6 ≤ count1620 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (1 ≤ count1628 (baseVal q)) := rfl
theorem value1629 (q : Snake 81) : valuation q 1629 = decide (2 ≤ count1628 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (1 ≤ count1630 (baseVal q)) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (2 ≤ count1630 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (1 ≤ count1632 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (2 ≤ count1632 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (3 ≤ count1632 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (4 ≤ count1632 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (1 ≤ count1636 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (2 ≤ count1636 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (1 ≤ count1638 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (2 ≤ count1638 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (1 ≤ count1640 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (2 ≤ count1640 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (3 ≤ count1640 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (1 ≤ count1643 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (2 ≤ count1643 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (3 ≤ count1643 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (4 ≤ count1643 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (5 ≤ count1643 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (1 ≤ count1648 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (2 ≤ count1648 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (3 ≤ count1648 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (4 ≤ count1648 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (5 ≤ count1648 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (6 ≤ count1648 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (7 ≤ count1648 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (2 ≤ count1657 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (3 ≤ count1657 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (4 ≤ count1657 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (5 ≤ count1657 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (6 ≤ count1657 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (7 ≤ count1657 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (8 ≤ count1657 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (9 ≤ count1657 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (10 ≤ count1657 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (9 ≤ count1674 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (10 ≤ count1674 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (11 ≤ count1674 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (12 ≤ count1674 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (13 ≤ count1674 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (14 ≤ count1674 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (15 ≤ count1674 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (16 ≤ count1674 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (17 ≤ count1674 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (18 ≤ count1674 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (1 ≤ count1701 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (2 ≤ count1701 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (1 ≤ count1703 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (2 ≤ count1703 (baseVal q)) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (1 ≤ count1705 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (2 ≤ count1705 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (3 ≤ count1705 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (4 ≤ count1705 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (1 ≤ count1709 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (2 ≤ count1709 (baseVal q)) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (1 ≤ count1711 (baseVal q)) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (2 ≤ count1711 (baseVal q)) := rfl
theorem value1713 (q : Snake 81) : valuation q 1713 = decide (1 ≤ count1713 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (2 ≤ count1713 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (3 ≤ count1713 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (4 ≤ count1713 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (1 ≤ count1717 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (2 ≤ count1717 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (3 ≤ count1717 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (4 ≤ count1717 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (5 ≤ count1717 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (6 ≤ count1717 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (1 ≤ count1725 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (2 ≤ count1725 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (1 ≤ count1727 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (2 ≤ count1727 (baseVal q)) := rfl
theorem value1729 (q : Snake 81) : valuation q 1729 = decide (1 ≤ count1729 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (2 ≤ count1729 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (3 ≤ count1729 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (1 ≤ count1733 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (2 ≤ count1733 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (1 ≤ count1735 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (2 ≤ count1735 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (1 ≤ count1737 (baseVal q)) := rfl
theorem value1738 (q : Snake 81) : valuation q 1738 = decide (2 ≤ count1737 (baseVal q)) := rfl
theorem value1739 (q : Snake 81) : valuation q 1739 = decide (3 ≤ count1737 (baseVal q)) := rfl
theorem value1740 (q : Snake 81) : valuation q 1740 = decide (1 ≤ count1740 (baseVal q)) := rfl
theorem value1741 (q : Snake 81) : valuation q 1741 = decide (2 ≤ count1740 (baseVal q)) := rfl
theorem value1742 (q : Snake 81) : valuation q 1742 = decide (3 ≤ count1740 (baseVal q)) := rfl
theorem value1743 (q : Snake 81) : valuation q 1743 = decide (4 ≤ count1740 (baseVal q)) := rfl
theorem value1744 (q : Snake 81) : valuation q 1744 = decide (5 ≤ count1740 (baseVal q)) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (1 ≤ count1745 (baseVal q)) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (2 ≤ count1745 (baseVal q)) := rfl
theorem value1747 (q : Snake 81) : valuation q 1747 = decide (3 ≤ count1745 (baseVal q)) := rfl
theorem value1748 (q : Snake 81) : valuation q 1748 = decide (4 ≤ count1745 (baseVal q)) := rfl
theorem value1749 (q : Snake 81) : valuation q 1749 = decide (5 ≤ count1745 (baseVal q)) := rfl
theorem value1750 (q : Snake 81) : valuation q 1750 = decide (6 ≤ count1745 (baseVal q)) := rfl
theorem value1755 (q : Snake 81) : valuation q 1755 = decide (2 ≤ count1754 (baseVal q)) := rfl
theorem value1756 (q : Snake 81) : valuation q 1756 = decide (3 ≤ count1754 (baseVal q)) := rfl
theorem value1757 (q : Snake 81) : valuation q 1757 = decide (4 ≤ count1754 (baseVal q)) := rfl
theorem value1758 (q : Snake 81) : valuation q 1758 = decide (5 ≤ count1754 (baseVal q)) := rfl
theorem value1759 (q : Snake 81) : valuation q 1759 = decide (6 ≤ count1754 (baseVal q)) := rfl
theorem value1760 (q : Snake 81) : valuation q 1760 = decide (7 ≤ count1754 (baseVal q)) := rfl
theorem value1761 (q : Snake 81) : valuation q 1761 = decide (8 ≤ count1754 (baseVal q)) := rfl
theorem value1762 (q : Snake 81) : valuation q 1762 = decide (9 ≤ count1754 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (10 ≤ count1754 (baseVal q)) := rfl
theorem value1771 (q : Snake 81) : valuation q 1771 = decide (1 ≤ count1771 (baseVal q)) := rfl
theorem value1772 (q : Snake 81) : valuation q 1772 = decide (2 ≤ count1771 (baseVal q)) := rfl
theorem value1773 (q : Snake 81) : valuation q 1773 = decide (1 ≤ count1773 (baseVal q)) := rfl
theorem value1774 (q : Snake 81) : valuation q 1774 = decide (2 ≤ count1773 (baseVal q)) := rfl
theorem value1775 (q : Snake 81) : valuation q 1775 = decide (1 ≤ count1775 (baseVal q)) := rfl
theorem value1776 (q : Snake 81) : valuation q 1776 = decide (2 ≤ count1775 (baseVal q)) := rfl
theorem value1777 (q : Snake 81) : valuation q 1777 = decide (3 ≤ count1775 (baseVal q)) := rfl
theorem value1778 (q : Snake 81) : valuation q 1778 = decide (4 ≤ count1775 (baseVal q)) := rfl
theorem value1779 (q : Snake 81) : valuation q 1779 = decide (1 ≤ count1779 (baseVal q)) := rfl
theorem value1780 (q : Snake 81) : valuation q 1780 = decide (2 ≤ count1779 (baseVal q)) := rfl
theorem value1781 (q : Snake 81) : valuation q 1781 = decide (1 ≤ count1781 (baseVal q)) := rfl
theorem value1782 (q : Snake 81) : valuation q 1782 = decide (2 ≤ count1781 (baseVal q)) := rfl
theorem value1783 (q : Snake 81) : valuation q 1783 = decide (1 ≤ count1783 (baseVal q)) := rfl
theorem value1784 (q : Snake 81) : valuation q 1784 = decide (2 ≤ count1783 (baseVal q)) := rfl
theorem value1785 (q : Snake 81) : valuation q 1785 = decide (3 ≤ count1783 (baseVal q)) := rfl
theorem value1786 (q : Snake 81) : valuation q 1786 = decide (4 ≤ count1783 (baseVal q)) := rfl
theorem value1787 (q : Snake 81) : valuation q 1787 = decide (1 ≤ count1787 (baseVal q)) := rfl
theorem value1788 (q : Snake 81) : valuation q 1788 = decide (2 ≤ count1787 (baseVal q)) := rfl
theorem value1789 (q : Snake 81) : valuation q 1789 = decide (3 ≤ count1787 (baseVal q)) := rfl
theorem value1790 (q : Snake 81) : valuation q 1790 = decide (4 ≤ count1787 (baseVal q)) := rfl
theorem value1791 (q : Snake 81) : valuation q 1791 = decide (5 ≤ count1787 (baseVal q)) := rfl
theorem value1792 (q : Snake 81) : valuation q 1792 = decide (6 ≤ count1787 (baseVal q)) := rfl
theorem value1793 (q : Snake 81) : valuation q 1793 = decide (7 ≤ count1787 (baseVal q)) := rfl
theorem value1795 (q : Snake 81) : valuation q 1795 = decide (1 ≤ count1795 (baseVal q)) := rfl
theorem value1796 (q : Snake 81) : valuation q 1796 = decide (2 ≤ count1795 (baseVal q)) := rfl
theorem value1797 (q : Snake 81) : valuation q 1797 = decide (1 ≤ count1797 (baseVal q)) := rfl
theorem value1798 (q : Snake 81) : valuation q 1798 = decide (2 ≤ count1797 (baseVal q)) := rfl
theorem value1799 (q : Snake 81) : valuation q 1799 = decide (1 ≤ count1799 (baseVal q)) := rfl
theorem value1800 (q : Snake 81) : valuation q 1800 = decide (2 ≤ count1799 (baseVal q)) := rfl
theorem value1801 (q : Snake 81) : valuation q 1801 = decide (3 ≤ count1799 (baseVal q)) := rfl
theorem value1802 (q : Snake 81) : valuation q 1802 = decide (4 ≤ count1799 (baseVal q)) := rfl
theorem value1803 (q : Snake 81) : valuation q 1803 = decide (1 ≤ count1803 (baseVal q)) := rfl
theorem value1804 (q : Snake 81) : valuation q 1804 = decide (2 ≤ count1803 (baseVal q)) := rfl
theorem value1805 (q : Snake 81) : valuation q 1805 = decide (1 ≤ count1805 (baseVal q)) := rfl
theorem value1806 (q : Snake 81) : valuation q 1806 = decide (2 ≤ count1805 (baseVal q)) := rfl
theorem value1807 (q : Snake 81) : valuation q 1807 = decide (1 ≤ count1807 (baseVal q)) := rfl
theorem value1808 (q : Snake 81) : valuation q 1808 = decide (2 ≤ count1807 (baseVal q)) := rfl
theorem value1809 (q : Snake 81) : valuation q 1809 = decide (3 ≤ count1807 (baseVal q)) := rfl
theorem value1810 (q : Snake 81) : valuation q 1810 = decide (1 ≤ count1810 (baseVal q)) := rfl
theorem value1811 (q : Snake 81) : valuation q 1811 = decide (2 ≤ count1810 (baseVal q)) := rfl
theorem value1812 (q : Snake 81) : valuation q 1812 = decide (3 ≤ count1810 (baseVal q)) := rfl
theorem value1813 (q : Snake 81) : valuation q 1813 = decide (4 ≤ count1810 (baseVal q)) := rfl
theorem value1814 (q : Snake 81) : valuation q 1814 = decide (5 ≤ count1810 (baseVal q)) := rfl
theorem value1815 (q : Snake 81) : valuation q 1815 = decide (1 ≤ count1815 (baseVal q)) := rfl
theorem value1816 (q : Snake 81) : valuation q 1816 = decide (2 ≤ count1815 (baseVal q)) := rfl
theorem value1817 (q : Snake 81) : valuation q 1817 = decide (3 ≤ count1815 (baseVal q)) := rfl
theorem value1818 (q : Snake 81) : valuation q 1818 = decide (4 ≤ count1815 (baseVal q)) := rfl
theorem value1819 (q : Snake 81) : valuation q 1819 = decide (5 ≤ count1815 (baseVal q)) := rfl
theorem value1820 (q : Snake 81) : valuation q 1820 = decide (6 ≤ count1815 (baseVal q)) := rfl
theorem value1821 (q : Snake 81) : valuation q 1821 = decide (7 ≤ count1815 (baseVal q)) := rfl
theorem value1822 (q : Snake 81) : valuation q 1822 = decide (8 ≤ count1815 (baseVal q)) := rfl
theorem value1827 (q : Snake 81) : valuation q 1827 = decide (4 ≤ count1824 (baseVal q)) := rfl
theorem value1828 (q : Snake 81) : valuation q 1828 = decide (5 ≤ count1824 (baseVal q)) := rfl
theorem value1829 (q : Snake 81) : valuation q 1829 = decide (6 ≤ count1824 (baseVal q)) := rfl
theorem value1830 (q : Snake 81) : valuation q 1830 = decide (7 ≤ count1824 (baseVal q)) := rfl
theorem value1831 (q : Snake 81) : valuation q 1831 = decide (8 ≤ count1824 (baseVal q)) := rfl
theorem value1832 (q : Snake 81) : valuation q 1832 = decide (9 ≤ count1824 (baseVal q)) := rfl
theorem value1833 (q : Snake 81) : valuation q 1833 = decide (10 ≤ count1824 (baseVal q)) := rfl
theorem value1834 (q : Snake 81) : valuation q 1834 = decide (11 ≤ count1824 (baseVal q)) := rfl
theorem value1835 (q : Snake 81) : valuation q 1835 = decide (12 ≤ count1824 (baseVal q)) := rfl
theorem value1836 (q : Snake 81) : valuation q 1836 = decide (13 ≤ count1824 (baseVal q)) := rfl
theorem value1849 (q : Snake 81) : valuation q 1849 = decide (9 ≤ count1841 (baseVal q)) := rfl
theorem value1850 (q : Snake 81) : valuation q 1850 = decide (10 ≤ count1841 (baseVal q)) := rfl
theorem value1851 (q : Snake 81) : valuation q 1851 = decide (11 ≤ count1841 (baseVal q)) := rfl
theorem value1852 (q : Snake 81) : valuation q 1852 = decide (12 ≤ count1841 (baseVal q)) := rfl
theorem value1853 (q : Snake 81) : valuation q 1853 = decide (13 ≤ count1841 (baseVal q)) := rfl
theorem value1854 (q : Snake 81) : valuation q 1854 = decide (14 ≤ count1841 (baseVal q)) := rfl
theorem value1855 (q : Snake 81) : valuation q 1855 = decide (15 ≤ count1841 (baseVal q)) := rfl
theorem value1856 (q : Snake 81) : valuation q 1856 = decide (16 ≤ count1841 (baseVal q)) := rfl
theorem value1857 (q : Snake 81) : valuation q 1857 = decide (17 ≤ count1841 (baseVal q)) := rfl
theorem value1858 (q : Snake 81) : valuation q 1858 = decide (18 ≤ count1841 (baseVal q)) := rfl
theorem value1894 (q : Snake 81) : valuation q 1894 = decide (27 ≤ count1868 (baseVal q)) := rfl
theorem meaningNeg126 (b : Nat → Bool) : literal (valuationOf b) (-126) = decide (1 ≤ countLit b [-126]) := by
  change literal b (-126) = decide (1 ≤ countLit b [-126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-126) <;> decide
theorem meaningNeg125 (b : Nat → Bool) : literal (valuationOf b) (-125) = decide (1 ≤ countLit b [-125]) := by
  change literal b (-125) = decide (1 ≤ countLit b [-125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-125) <;> decide
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
theorem meaningNeg120 (b : Nat → Bool) : literal (valuationOf b) (-120) = decide (1 ≤ countLit b [-120]) := by
  change literal b (-120) = decide (1 ≤ countLit b [-120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-120) <;> decide
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
theorem meaningNeg109 (b : Nat → Bool) : literal (valuationOf b) (-109) = decide (1 ≤ countLit b [-109]) := by
  change literal b (-109) = decide (1 ≤ countLit b [-109])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-109) <;> decide
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
theorem meaningNeg103 (b : Nat → Bool) : literal (valuationOf b) (-103) = decide (1 ≤ countLit b [-103]) := by
  change literal b (-103) = decide (1 ≤ countLit b [-103])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-103) <;> decide
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
theorem meaningNeg93 (b : Nat → Bool) : literal (valuationOf b) (-93) = decide (1 ≤ countLit b [-93]) := by
  change literal b (-93) = decide (1 ≤ countLit b [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-93) <;> decide
theorem meaningNeg92 (b : Nat → Bool) : literal (valuationOf b) (-92) = decide (1 ≤ countLit b [-92]) := by
  change literal b (-92) = decide (1 ≤ countLit b [-92])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-92) <;> decide
theorem meaningNeg89 (b : Nat → Bool) : literal (valuationOf b) (-89) = decide (1 ≤ countLit b [-89]) := by
  change literal b (-89) = decide (1 ≤ countLit b [-89])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-89) <;> decide
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
theorem meaningNeg77 (b : Nat → Bool) : literal (valuationOf b) (-77) = decide (1 ≤ countLit b [-77]) := by
  change literal b (-77) = decide (1 ≤ countLit b [-77])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-77) <;> decide
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
theorem meaningNeg68 (b : Nat → Bool) : literal (valuationOf b) (-68) = decide (1 ≤ countLit b [-68]) := by
  change literal b (-68) = decide (1 ≤ countLit b [-68])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-68) <;> decide
theorem meaningNeg65 (b : Nat → Bool) : literal (valuationOf b) (-65) = decide (1 ≤ countLit b [-65]) := by
  change literal b (-65) = decide (1 ≤ countLit b [-65])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-65) <;> decide
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
theorem meaningNeg58 (b : Nat → Bool) : literal (valuationOf b) (-58) = decide (1 ≤ countLit b [-58]) := by
  change literal b (-58) = decide (1 ≤ countLit b [-58])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-58) <;> decide
theorem meaningNeg56 (b : Nat → Bool) : literal (valuationOf b) (-56) = decide (1 ≤ countLit b [-56]) := by
  change literal b (-56) = decide (1 ≤ countLit b [-56])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-56) <;> decide
theorem meaningNeg53 (b : Nat → Bool) : literal (valuationOf b) (-53) = decide (1 ≤ countLit b [-53]) := by
  change literal b (-53) = decide (1 ≤ countLit b [-53])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-53) <;> decide
theorem meaningNeg52 (b : Nat → Bool) : literal (valuationOf b) (-52) = decide (1 ≤ countLit b [-52]) := by
  change literal b (-52) = decide (1 ≤ countLit b [-52])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-52) <;> decide
theorem meaningNeg51 (b : Nat → Bool) : literal (valuationOf b) (-51) = decide (1 ≤ countLit b [-51]) := by
  change literal b (-51) = decide (1 ≤ countLit b [-51])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-51) <;> decide
theorem meaningNeg48 (b : Nat → Bool) : literal (valuationOf b) (-48) = decide (1 ≤ countLit b [-48]) := by
  change literal b (-48) = decide (1 ≤ countLit b [-48])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-48) <;> decide
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
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
theorem meaningNeg40 (b : Nat → Bool) : literal (valuationOf b) (-40) = decide (1 ≤ countLit b [-40]) := by
  change literal b (-40) = decide (1 ≤ countLit b [-40])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-40) <;> decide
theorem meaningNeg37 (b : Nat → Bool) : literal (valuationOf b) (-37) = decide (1 ≤ countLit b [-37]) := by
  change literal b (-37) = decide (1 ≤ countLit b [-37])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-37) <;> decide
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
theorem meaningNeg11 (b : Nat → Bool) : literal (valuationOf b) (-11) = decide (1 ≤ countLit b [-11]) := by
  change literal b (-11) = decide (1 ≤ countLit b [-11])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-11) <;> decide
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
theorem meaning133 (b : Nat → Bool) : literal (valuationOf b) (133) = decide (1 ≤ countLit b [133]) := by
  change literal b (133) = decide (1 ≤ countLit b [133])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (133) <;> decide
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
theorem meaning148 (b : Nat → Bool) : literal (valuationOf b) (148) = decide (1 ≤ countLit b [148]) := by
  change literal b (148) = decide (1 ≤ countLit b [148])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (148) <;> decide
theorem meaning150 (b : Nat → Bool) : literal (valuationOf b) (150) = decide (1 ≤ countLit b [150]) := by
  change literal b (150) = decide (1 ≤ countLit b [150])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (150) <;> decide
theorem meaning154 (b : Nat → Bool) : literal (valuationOf b) (154) = decide (1 ≤ countLit b [154]) := by
  change literal b (154) = decide (1 ≤ countLit b [154])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (154) <;> decide
theorem meaning158 (b : Nat → Bool) : literal (valuationOf b) (158) = decide (1 ≤ countLit b [158]) := by
  change literal b (158) = decide (1 ≤ countLit b [158])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (158) <;> decide
theorem meaning159 (b : Nat → Bool) : literal (valuationOf b) (159) = decide (1 ≤ countLit b [159]) := by
  change literal b (159) = decide (1 ≤ countLit b [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (159) <;> decide
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
theorem meaning166 (b : Nat → Bool) : literal (valuationOf b) (166) = decide (1 ≤ countLit b [166]) := by
  change literal b (166) = decide (1 ≤ countLit b [166])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (166) <;> decide
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
theorem meaning171 (b : Nat → Bool) : literal (valuationOf b) (171) = decide (1 ≤ countLit b [171]) := by
  change literal b (171) = decide (1 ≤ countLit b [171])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (171) <;> decide
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
theorem meaning183 (b : Nat → Bool) : literal (valuationOf b) (183) = decide (1 ≤ countLit b [183]) := by
  change literal b (183) = decide (1 ≤ countLit b [183])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (183) <;> decide
theorem meaning187 (b : Nat → Bool) : literal (valuationOf b) (187) = decide (1 ≤ countLit b [187]) := by
  change literal b (187) = decide (1 ≤ countLit b [187])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (187) <;> decide
theorem meaning191 (b : Nat → Bool) : literal (valuationOf b) (191) = decide (1 ≤ countLit b [191]) := by
  change literal b (191) = decide (1 ≤ countLit b [191])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (191) <;> decide
theorem meaning194 (b : Nat → Bool) : literal (valuationOf b) (194) = decide (1 ≤ countLit b [194]) := by
  change literal b (194) = decide (1 ≤ countLit b [194])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (194) <;> decide
theorem meaning197 (b : Nat → Bool) : literal (valuationOf b) (197) = decide (1 ≤ countLit b [197]) := by
  change literal b (197) = decide (1 ≤ countLit b [197])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (197) <;> decide
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) (203) = decide (1 ≤ countLit b [203]) := by
  change literal b (203) = decide (1 ≤ countLit b [203])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (203) <;> decide
theorem meaning204 (b : Nat → Bool) : literal (valuationOf b) (204) = decide (1 ≤ countLit b [204]) := by
  change literal b (204) = decide (1 ≤ countLit b [204])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (204) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning208 (b : Nat → Bool) : literal (valuationOf b) (208) = decide (1 ≤ countLit b [208]) := by
  change literal b (208) = decide (1 ≤ countLit b [208])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (208) <;> decide
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) (211) = decide (1 ≤ countLit b [211]) := by
  change literal b (211) = decide (1 ≤ countLit b [211])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (211) <;> decide
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
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) (222) = decide (1 ≤ countLit b [222]) := by
  change literal b (222) = decide (1 ≤ countLit b [222])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (222) <;> decide
theorem meaning224 (b : Nat → Bool) : literal (valuationOf b) (224) = decide (1 ≤ countLit b [224]) := by
  change literal b (224) = decide (1 ≤ countLit b [224])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (224) <;> decide
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) (227) = decide (1 ≤ countLit b [227]) := by
  change literal b (227) = decide (1 ≤ countLit b [227])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (227) <;> decide
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) (229) = decide (1 ≤ countLit b [229]) := by
  change literal b (229) = decide (1 ≤ countLit b [229])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (229) <;> decide
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
theorem meaning234 (b : Nat → Bool) : literal (valuationOf b) (234) = decide (1 ≤ countLit b [234]) := by
  change literal b (234) = decide (1 ≤ countLit b [234])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (234) <;> decide
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) (238) = decide (1 ≤ countLit b [238]) := by
  change literal b (238) = decide (1 ≤ countLit b [238])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (238) <;> decide
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) (239) = decide (1 ≤ countLit b [239]) := by
  change literal b (239) = decide (1 ≤ countLit b [239])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (239) <;> decide
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
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) (244) = decide (1 ≤ countLit b [244]) := by
  change literal b (244) = decide (1 ≤ countLit b [244])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (244) <;> decide
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) (251) = decide (1 ≤ countLit b [251]) := by
  change literal b (251) = decide (1 ≤ countLit b [251])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (251) <;> decide
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) (252) = decide (1 ≤ countLit b [252]) := by
  change literal b (252) = decide (1 ≤ countLit b [252])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (252) <;> decide
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) (255) = decide (1 ≤ countLit b [255]) := by
  change literal b (255) = decide (1 ≤ countLit b [255])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (255) <;> decide
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) (256) = decide (1 ≤ countLit b [256]) := by
  change literal b (256) = decide (1 ≤ countLit b [256])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (256) <;> decide
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning284 (b : Nat → Bool) : literal (valuationOf b) 284 = decide (2 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning298 (b : Nat → Bool) : literal (valuationOf b) 298 = decide (2 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning310 (b : Nat → Bool) : literal (valuationOf b) 310 = decide (2 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning316 (b : Nat → Bool) : literal (valuationOf b) 316 = decide (2 ≤ count315 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning336 (b : Nat → Bool) : literal (valuationOf b) 336 = decide (2 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning380 (b : Nat → Bool) : literal (valuationOf b) 380 = decide (2 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning440 (b : Nat → Bool) : literal (valuationOf b) 440 = decide (2 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning442 (b : Nat → Bool) : literal (valuationOf b) 442 = decide (2 ≤ count441 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning456 (b : Nat → Bool) : literal (valuationOf b) 456 = decide (2 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning470 (b : Nat → Bool) : literal (valuationOf b) 470 = decide (2 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning472 (b : Nat → Bool) : literal (valuationOf b) 472 = decide (2 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning478 (b : Nat → Bool) : literal (valuationOf b) 478 = decide (2 ≤ count477 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning486 (b : Nat → Bool) : literal (valuationOf b) 486 = decide (2 ≤ count485 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning491 (b : Nat → Bool) : literal (valuationOf b) 491 = decide (1 ≤ count491 b) := rfl
theorem meaning495 (b : Nat → Bool) : literal (valuationOf b) 495 = decide (1 ≤ count495 b) := rfl
theorem meaning496 (b : Nat → Bool) : literal (valuationOf b) 496 = decide (2 ≤ count495 b) := rfl
theorem meaning497 (b : Nat → Bool) : literal (valuationOf b) 497 = decide (1 ≤ count497 b) := rfl
theorem meaning498 (b : Nat → Bool) : literal (valuationOf b) 498 = decide (2 ≤ count497 b) := rfl
theorem meaning499 (b : Nat → Bool) : literal (valuationOf b) 499 = decide (1 ≤ count499 b) := rfl
theorem meaning500 (b : Nat → Bool) : literal (valuationOf b) 500 = decide (2 ≤ count499 b) := rfl
theorem meaning501 (b : Nat → Bool) : literal (valuationOf b) 501 = decide (1 ≤ count501 b) := rfl
theorem meaning502 (b : Nat → Bool) : literal (valuationOf b) 502 = decide (2 ≤ count501 b) := rfl
theorem meaning503 (b : Nat → Bool) : literal (valuationOf b) 503 = decide (1 ≤ count503 b) := rfl
theorem meaning504 (b : Nat → Bool) : literal (valuationOf b) 504 = decide (2 ≤ count503 b) := rfl
theorem meaning505 (b : Nat → Bool) : literal (valuationOf b) 505 = decide (1 ≤ count505 b) := rfl
theorem meaning506 (b : Nat → Bool) : literal (valuationOf b) 506 = decide (2 ≤ count505 b) := rfl
theorem meaning508 (b : Nat → Bool) : literal (valuationOf b) 508 = decide (2 ≤ count507 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (1 ≤ count1540 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (2 ≤ count1540 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (1 ≤ count1542 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (2 ≤ count1542 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (1 ≤ count1544 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (2 ≤ count1544 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (3 ≤ count1544 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (4 ≤ count1544 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (1 ≤ count1548 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (2 ≤ count1548 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (1 ≤ count1550 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (1 ≤ count1552 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (2 ≤ count1552 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (3 ≤ count1552 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (3 ≤ count1556 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (4 ≤ count1556 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (5 ≤ count1556 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (6 ≤ count1556 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (7 ≤ count1556 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (1 ≤ count1566 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (2 ≤ count1566 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (1 ≤ count1568 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (2 ≤ count1568 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (3 ≤ count1568 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (4 ≤ count1568 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (1 ≤ count1572 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (2 ≤ count1572 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (1 ≤ count1574 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (2 ≤ count1574 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (1 ≤ count1576 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (2 ≤ count1576 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (3 ≤ count1576 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (4 ≤ count1576 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (3 ≤ count1580 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (4 ≤ count1580 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (5 ≤ count1580 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (6 ≤ count1580 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (7 ≤ count1580 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (8 ≤ count1580 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (5 ≤ count1588 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (6 ≤ count1588 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (7 ≤ count1588 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (8 ≤ count1588 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (9 ≤ count1588 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (10 ≤ count1588 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (11 ≤ count1588 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (12 ≤ count1588 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (13 ≤ count1588 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (1 ≤ count1604 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (2 ≤ count1604 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (1 ≤ count1606 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (2 ≤ count1606 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (1 ≤ count1608 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (2 ≤ count1608 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (3 ≤ count1608 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (4 ≤ count1608 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (1 ≤ count1612 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (2 ≤ count1612 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (1 ≤ count1614 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (2 ≤ count1614 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (1 ≤ count1616 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (2 ≤ count1616 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (3 ≤ count1616 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (4 ≤ count1616 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (1 ≤ count1620 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (2 ≤ count1620 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (3 ≤ count1620 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (4 ≤ count1620 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (5 ≤ count1620 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (6 ≤ count1620 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (1 ≤ count1628 b) := rfl
theorem meaning1629 (b : Nat → Bool) : literal (valuationOf b) 1629 = decide (2 ≤ count1628 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (1 ≤ count1630 b) := rfl
theorem meaning1631 (b : Nat → Bool) : literal (valuationOf b) 1631 = decide (2 ≤ count1630 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (1 ≤ count1632 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (2 ≤ count1632 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (3 ≤ count1632 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (4 ≤ count1632 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (1 ≤ count1636 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (2 ≤ count1636 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (1 ≤ count1638 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (2 ≤ count1638 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (1 ≤ count1640 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (2 ≤ count1640 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (3 ≤ count1640 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (1 ≤ count1643 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (2 ≤ count1643 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (3 ≤ count1643 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (4 ≤ count1643 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (5 ≤ count1643 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (1 ≤ count1648 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (2 ≤ count1648 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (3 ≤ count1648 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (4 ≤ count1648 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (5 ≤ count1648 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (6 ≤ count1648 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (7 ≤ count1648 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (2 ≤ count1657 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (3 ≤ count1657 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (4 ≤ count1657 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (5 ≤ count1657 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (6 ≤ count1657 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (7 ≤ count1657 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (8 ≤ count1657 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (9 ≤ count1657 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (10 ≤ count1657 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (9 ≤ count1674 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (10 ≤ count1674 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (11 ≤ count1674 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (12 ≤ count1674 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (13 ≤ count1674 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (14 ≤ count1674 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (15 ≤ count1674 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (16 ≤ count1674 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (17 ≤ count1674 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (18 ≤ count1674 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (1 ≤ count1701 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (2 ≤ count1701 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (1 ≤ count1703 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (2 ≤ count1703 b) := rfl
theorem meaning1705 (b : Nat → Bool) : literal (valuationOf b) 1705 = decide (1 ≤ count1705 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (2 ≤ count1705 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (3 ≤ count1705 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (4 ≤ count1705 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (1 ≤ count1709 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (2 ≤ count1709 b) := rfl
theorem meaning1711 (b : Nat → Bool) : literal (valuationOf b) 1711 = decide (1 ≤ count1711 b) := rfl
theorem meaning1712 (b : Nat → Bool) : literal (valuationOf b) 1712 = decide (2 ≤ count1711 b) := rfl
theorem meaning1713 (b : Nat → Bool) : literal (valuationOf b) 1713 = decide (1 ≤ count1713 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (2 ≤ count1713 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (3 ≤ count1713 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (4 ≤ count1713 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (1 ≤ count1717 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (2 ≤ count1717 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (3 ≤ count1717 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (4 ≤ count1717 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (5 ≤ count1717 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (6 ≤ count1717 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (1 ≤ count1725 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (2 ≤ count1725 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (1 ≤ count1727 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (2 ≤ count1727 b) := rfl
theorem meaning1729 (b : Nat → Bool) : literal (valuationOf b) 1729 = decide (1 ≤ count1729 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (2 ≤ count1729 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (3 ≤ count1729 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (1 ≤ count1733 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (2 ≤ count1733 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (1 ≤ count1735 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (2 ≤ count1735 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (1 ≤ count1737 b) := rfl
theorem meaning1738 (b : Nat → Bool) : literal (valuationOf b) 1738 = decide (2 ≤ count1737 b) := rfl
theorem meaning1739 (b : Nat → Bool) : literal (valuationOf b) 1739 = decide (3 ≤ count1737 b) := rfl
theorem meaning1740 (b : Nat → Bool) : literal (valuationOf b) 1740 = decide (1 ≤ count1740 b) := rfl
theorem meaning1741 (b : Nat → Bool) : literal (valuationOf b) 1741 = decide (2 ≤ count1740 b) := rfl
theorem meaning1742 (b : Nat → Bool) : literal (valuationOf b) 1742 = decide (3 ≤ count1740 b) := rfl
theorem meaning1743 (b : Nat → Bool) : literal (valuationOf b) 1743 = decide (4 ≤ count1740 b) := rfl
theorem meaning1744 (b : Nat → Bool) : literal (valuationOf b) 1744 = decide (5 ≤ count1740 b) := rfl
theorem meaning1745 (b : Nat → Bool) : literal (valuationOf b) 1745 = decide (1 ≤ count1745 b) := rfl
theorem meaning1746 (b : Nat → Bool) : literal (valuationOf b) 1746 = decide (2 ≤ count1745 b) := rfl
theorem meaning1747 (b : Nat → Bool) : literal (valuationOf b) 1747 = decide (3 ≤ count1745 b) := rfl
theorem meaning1748 (b : Nat → Bool) : literal (valuationOf b) 1748 = decide (4 ≤ count1745 b) := rfl
theorem meaning1749 (b : Nat → Bool) : literal (valuationOf b) 1749 = decide (5 ≤ count1745 b) := rfl
theorem meaning1750 (b : Nat → Bool) : literal (valuationOf b) 1750 = decide (6 ≤ count1745 b) := rfl
theorem meaning1755 (b : Nat → Bool) : literal (valuationOf b) 1755 = decide (2 ≤ count1754 b) := rfl
theorem meaning1756 (b : Nat → Bool) : literal (valuationOf b) 1756 = decide (3 ≤ count1754 b) := rfl
theorem meaning1757 (b : Nat → Bool) : literal (valuationOf b) 1757 = decide (4 ≤ count1754 b) := rfl
theorem meaning1758 (b : Nat → Bool) : literal (valuationOf b) 1758 = decide (5 ≤ count1754 b) := rfl
theorem meaning1759 (b : Nat → Bool) : literal (valuationOf b) 1759 = decide (6 ≤ count1754 b) := rfl
theorem meaning1760 (b : Nat → Bool) : literal (valuationOf b) 1760 = decide (7 ≤ count1754 b) := rfl
theorem meaning1761 (b : Nat → Bool) : literal (valuationOf b) 1761 = decide (8 ≤ count1754 b) := rfl
theorem meaning1762 (b : Nat → Bool) : literal (valuationOf b) 1762 = decide (9 ≤ count1754 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (10 ≤ count1754 b) := rfl
theorem meaning1771 (b : Nat → Bool) : literal (valuationOf b) 1771 = decide (1 ≤ count1771 b) := rfl
theorem meaning1772 (b : Nat → Bool) : literal (valuationOf b) 1772 = decide (2 ≤ count1771 b) := rfl
theorem meaning1773 (b : Nat → Bool) : literal (valuationOf b) 1773 = decide (1 ≤ count1773 b) := rfl
theorem meaning1774 (b : Nat → Bool) : literal (valuationOf b) 1774 = decide (2 ≤ count1773 b) := rfl
theorem meaning1775 (b : Nat → Bool) : literal (valuationOf b) 1775 = decide (1 ≤ count1775 b) := rfl
theorem meaning1776 (b : Nat → Bool) : literal (valuationOf b) 1776 = decide (2 ≤ count1775 b) := rfl
theorem meaning1777 (b : Nat → Bool) : literal (valuationOf b) 1777 = decide (3 ≤ count1775 b) := rfl
theorem meaning1778 (b : Nat → Bool) : literal (valuationOf b) 1778 = decide (4 ≤ count1775 b) := rfl
theorem meaning1779 (b : Nat → Bool) : literal (valuationOf b) 1779 = decide (1 ≤ count1779 b) := rfl
theorem meaning1780 (b : Nat → Bool) : literal (valuationOf b) 1780 = decide (2 ≤ count1779 b) := rfl
theorem meaning1781 (b : Nat → Bool) : literal (valuationOf b) 1781 = decide (1 ≤ count1781 b) := rfl
theorem meaning1782 (b : Nat → Bool) : literal (valuationOf b) 1782 = decide (2 ≤ count1781 b) := rfl
theorem meaning1783 (b : Nat → Bool) : literal (valuationOf b) 1783 = decide (1 ≤ count1783 b) := rfl
theorem meaning1784 (b : Nat → Bool) : literal (valuationOf b) 1784 = decide (2 ≤ count1783 b) := rfl
theorem meaning1785 (b : Nat → Bool) : literal (valuationOf b) 1785 = decide (3 ≤ count1783 b) := rfl
theorem meaning1786 (b : Nat → Bool) : literal (valuationOf b) 1786 = decide (4 ≤ count1783 b) := rfl
theorem meaning1787 (b : Nat → Bool) : literal (valuationOf b) 1787 = decide (1 ≤ count1787 b) := rfl
theorem meaning1788 (b : Nat → Bool) : literal (valuationOf b) 1788 = decide (2 ≤ count1787 b) := rfl
theorem meaning1789 (b : Nat → Bool) : literal (valuationOf b) 1789 = decide (3 ≤ count1787 b) := rfl
theorem meaning1790 (b : Nat → Bool) : literal (valuationOf b) 1790 = decide (4 ≤ count1787 b) := rfl
theorem meaning1791 (b : Nat → Bool) : literal (valuationOf b) 1791 = decide (5 ≤ count1787 b) := rfl
theorem meaning1792 (b : Nat → Bool) : literal (valuationOf b) 1792 = decide (6 ≤ count1787 b) := rfl
theorem meaning1793 (b : Nat → Bool) : literal (valuationOf b) 1793 = decide (7 ≤ count1787 b) := rfl
theorem meaning1795 (b : Nat → Bool) : literal (valuationOf b) 1795 = decide (1 ≤ count1795 b) := rfl
theorem meaning1796 (b : Nat → Bool) : literal (valuationOf b) 1796 = decide (2 ≤ count1795 b) := rfl
theorem meaning1797 (b : Nat → Bool) : literal (valuationOf b) 1797 = decide (1 ≤ count1797 b) := rfl
theorem meaning1798 (b : Nat → Bool) : literal (valuationOf b) 1798 = decide (2 ≤ count1797 b) := rfl
theorem meaning1799 (b : Nat → Bool) : literal (valuationOf b) 1799 = decide (1 ≤ count1799 b) := rfl
theorem meaning1800 (b : Nat → Bool) : literal (valuationOf b) 1800 = decide (2 ≤ count1799 b) := rfl
theorem meaning1801 (b : Nat → Bool) : literal (valuationOf b) 1801 = decide (3 ≤ count1799 b) := rfl
theorem meaning1802 (b : Nat → Bool) : literal (valuationOf b) 1802 = decide (4 ≤ count1799 b) := rfl
theorem meaning1803 (b : Nat → Bool) : literal (valuationOf b) 1803 = decide (1 ≤ count1803 b) := rfl
theorem meaning1804 (b : Nat → Bool) : literal (valuationOf b) 1804 = decide (2 ≤ count1803 b) := rfl
theorem meaning1805 (b : Nat → Bool) : literal (valuationOf b) 1805 = decide (1 ≤ count1805 b) := rfl
theorem meaning1806 (b : Nat → Bool) : literal (valuationOf b) 1806 = decide (2 ≤ count1805 b) := rfl
theorem meaning1807 (b : Nat → Bool) : literal (valuationOf b) 1807 = decide (1 ≤ count1807 b) := rfl
theorem meaning1808 (b : Nat → Bool) : literal (valuationOf b) 1808 = decide (2 ≤ count1807 b) := rfl
theorem meaning1809 (b : Nat → Bool) : literal (valuationOf b) 1809 = decide (3 ≤ count1807 b) := rfl
theorem meaning1810 (b : Nat → Bool) : literal (valuationOf b) 1810 = decide (1 ≤ count1810 b) := rfl
theorem meaning1811 (b : Nat → Bool) : literal (valuationOf b) 1811 = decide (2 ≤ count1810 b) := rfl
theorem meaning1812 (b : Nat → Bool) : literal (valuationOf b) 1812 = decide (3 ≤ count1810 b) := rfl
theorem meaning1813 (b : Nat → Bool) : literal (valuationOf b) 1813 = decide (4 ≤ count1810 b) := rfl
theorem meaning1814 (b : Nat → Bool) : literal (valuationOf b) 1814 = decide (5 ≤ count1810 b) := rfl
theorem meaning1815 (b : Nat → Bool) : literal (valuationOf b) 1815 = decide (1 ≤ count1815 b) := rfl
theorem meaning1816 (b : Nat → Bool) : literal (valuationOf b) 1816 = decide (2 ≤ count1815 b) := rfl
theorem meaning1817 (b : Nat → Bool) : literal (valuationOf b) 1817 = decide (3 ≤ count1815 b) := rfl
theorem meaning1818 (b : Nat → Bool) : literal (valuationOf b) 1818 = decide (4 ≤ count1815 b) := rfl
theorem meaning1819 (b : Nat → Bool) : literal (valuationOf b) 1819 = decide (5 ≤ count1815 b) := rfl
theorem meaning1820 (b : Nat → Bool) : literal (valuationOf b) 1820 = decide (6 ≤ count1815 b) := rfl
theorem meaning1821 (b : Nat → Bool) : literal (valuationOf b) 1821 = decide (7 ≤ count1815 b) := rfl
theorem meaning1822 (b : Nat → Bool) : literal (valuationOf b) 1822 = decide (8 ≤ count1815 b) := rfl
theorem meaning1827 (b : Nat → Bool) : literal (valuationOf b) 1827 = decide (4 ≤ count1824 b) := rfl
theorem meaning1828 (b : Nat → Bool) : literal (valuationOf b) 1828 = decide (5 ≤ count1824 b) := rfl
theorem meaning1829 (b : Nat → Bool) : literal (valuationOf b) 1829 = decide (6 ≤ count1824 b) := rfl
theorem meaning1830 (b : Nat → Bool) : literal (valuationOf b) 1830 = decide (7 ≤ count1824 b) := rfl
theorem meaning1831 (b : Nat → Bool) : literal (valuationOf b) 1831 = decide (8 ≤ count1824 b) := rfl
theorem meaning1832 (b : Nat → Bool) : literal (valuationOf b) 1832 = decide (9 ≤ count1824 b) := rfl
theorem meaning1833 (b : Nat → Bool) : literal (valuationOf b) 1833 = decide (10 ≤ count1824 b) := rfl
theorem meaning1834 (b : Nat → Bool) : literal (valuationOf b) 1834 = decide (11 ≤ count1824 b) := rfl
theorem meaning1835 (b : Nat → Bool) : literal (valuationOf b) 1835 = decide (12 ≤ count1824 b) := rfl
theorem meaning1836 (b : Nat → Bool) : literal (valuationOf b) 1836 = decide (13 ≤ count1824 b) := rfl
theorem meaning1849 (b : Nat → Bool) : literal (valuationOf b) 1849 = decide (9 ≤ count1841 b) := rfl
theorem meaning1850 (b : Nat → Bool) : literal (valuationOf b) 1850 = decide (10 ≤ count1841 b) := rfl
theorem meaning1851 (b : Nat → Bool) : literal (valuationOf b) 1851 = decide (11 ≤ count1841 b) := rfl
theorem meaning1852 (b : Nat → Bool) : literal (valuationOf b) 1852 = decide (12 ≤ count1841 b) := rfl
theorem meaning1853 (b : Nat → Bool) : literal (valuationOf b) 1853 = decide (13 ≤ count1841 b) := rfl
theorem meaning1854 (b : Nat → Bool) : literal (valuationOf b) 1854 = decide (14 ≤ count1841 b) := rfl
theorem meaning1855 (b : Nat → Bool) : literal (valuationOf b) 1855 = decide (15 ≤ count1841 b) := rfl
theorem meaning1856 (b : Nat → Bool) : literal (valuationOf b) 1856 = decide (16 ≤ count1841 b) := rfl
theorem meaning1857 (b : Nat → Bool) : literal (valuationOf b) 1857 = decide (17 ≤ count1841 b) := rfl
theorem meaning1858 (b : Nat → Bool) : literal (valuationOf b) 1858 = decide (18 ≤ count1841 b) := rfl
theorem meaning1894 (b : Nat → Bool) : literal (valuationOf b) 1894 = decide (27 ≤ count1868 b) := rfl
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
end Snake9.Regrowth.E112034
