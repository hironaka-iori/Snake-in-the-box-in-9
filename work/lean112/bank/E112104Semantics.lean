import E112104Data
namespace Snake9.Regrowth.E112104
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 118 then (if i < 59 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (10 : Vertex)) else decide (InPath q (14 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (33 : Vertex)) else decide (InPath q (35 : Vertex))) else (if i < 6 then decide (InPath q (37 : Vertex)) else decide (InPath q (42 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (48 : Vertex)) else (if i < 9 then decide (InPath q (49 : Vertex)) else decide (InPath q (50 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (54 : Vertex)) else decide (InPath q (58 : Vertex))) else (if i < 13 then decide (InPath q (96 : Vertex)) else decide (InPath q (98 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (100 : Vertex)) else (if i < 16 then decide (InPath q (101 : Vertex)) else decide (InPath q (102 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (104 : Vertex)) else decide (InPath q (106 : Vertex))) else (if i < 20 then decide (InPath q (107 : Vertex)) else decide (InPath q (108 : Vertex))))) else (if i < 25 then (if i < 23 then (if i < 22 then decide (InPath q (110 : Vertex)) else decide (InPath q (113 : Vertex))) else (if i < 24 then decide (InPath q (115 : Vertex)) else decide (InPath q (117 : Vertex)))) else (if i < 27 then (if i < 26 then decide (InPath q (118 : Vertex)) else decide (InPath q (119 : Vertex))) else (if i < 28 then decide (InPath q (120 : Vertex)) else decide (InPath q (121 : Vertex))))))) else (if i < 44 then (if i < 36 then (if i < 32 then (if i < 30 then decide (InPath q (123 : Vertex)) else (if i < 31 then decide (InPath q (225 : Vertex)) else decide (InPath q (227 : Vertex)))) else (if i < 34 then (if i < 33 then decide (InPath q (228 : Vertex)) else decide (InPath q (231 : Vertex))) else (if i < 35 then decide (InPath q (233 : Vertex)) else decide (InPath q (234 : Vertex))))) else (if i < 40 then (if i < 38 then (if i < 37 then decide (InPath q (236 : Vertex)) else decide (InPath q (237 : Vertex))) else (if i < 39 then decide (InPath q (240 : Vertex)) else decide (InPath q (241 : Vertex)))) else (if i < 42 then (if i < 41 then decide (InPath q (242 : Vertex)) else decide (InPath q (244 : Vertex))) else (if i < 43 then decide (InPath q (250 : Vertex)) else decide (InPath q (252 : Vertex)))))) else (if i < 51 then (if i < 47 then (if i < 45 then decide (InPath q (253 : Vertex)) else (if i < 46 then decide (InPath q (254 : Vertex)) else decide (InPath q (255 : Vertex)))) else (if i < 49 then (if i < 48 then decide (InPath q (257 : Vertex)) else decide (InPath q (259 : Vertex))) else (if i < 50 then decide (InPath q (261 : Vertex)) else decide (InPath q (266 : Vertex))))) else (if i < 55 then (if i < 53 then (if i < 52 then decide (InPath q (267 : Vertex)) else decide (InPath q (268 : Vertex))) else (if i < 54 then decide (InPath q (269 : Vertex)) else decide (InPath q (272 : Vertex)))) else (if i < 57 then (if i < 56 then decide (InPath q (273 : Vertex)) else decide (InPath q (274 : Vertex))) else (if i < 58 then decide (InPath q (278 : Vertex)) else decide (InPath q (282 : Vertex)))))))) else (if i < 88 then (if i < 73 then (if i < 66 then (if i < 62 then (if i < 60 then decide (InPath q (285 : Vertex)) else (if i < 61 then decide (InPath q (286 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 64 then (if i < 63 then decide (InPath q (353 : Vertex)) else decide (InPath q (355 : Vertex))) else (if i < 65 then decide (InPath q (356 : Vertex)) else decide (InPath q (357 : Vertex))))) else (if i < 69 then (if i < 67 then decide (InPath q (359 : Vertex)) else (if i < 68 then decide (InPath q (362 : Vertex)) else decide (InPath q (363 : Vertex)))) else (if i < 71 then (if i < 70 then decide (InPath q (364 : Vertex)) else decide (InPath q (365 : Vertex))) else (if i < 72 then decide (InPath q (368 : Vertex)) else decide (InPath q (369 : Vertex)))))) else (if i < 80 then (if i < 76 then (if i < 74 then decide (InPath q (370 : Vertex)) else (if i < 75 then decide (InPath q (374 : Vertex)) else decide (InPath q (378 : Vertex)))) else (if i < 78 then (if i < 77 then decide (InPath q (381 : Vertex)) else decide (InPath q (382 : Vertex))) else (if i < 79 then decide (InPath q (383 : Vertex)) else decide (InPath q (417 : Vertex))))) else (if i < 84 then (if i < 82 then (if i < 81 then decide (InPath q (419 : Vertex)) else decide (InPath q (420 : Vertex))) else (if i < 83 then decide (InPath q (421 : Vertex)) else decide (InPath q (423 : Vertex)))) else (if i < 86 then (if i < 85 then decide (InPath q (426 : Vertex)) else decide (InPath q (427 : Vertex))) else (if i < 87 then decide (InPath q (428 : Vertex)) else decide (InPath q (429 : Vertex))))))) else (if i < 103 then (if i < 95 then (if i < 91 then (if i < 89 then decide (InPath q (432 : Vertex)) else (if i < 90 then decide (InPath q (433 : Vertex)) else decide (InPath q (434 : Vertex)))) else (if i < 93 then (if i < 92 then decide (InPath q (438 : Vertex)) else decide (InPath q (442 : Vertex))) else (if i < 94 then decide (InPath q (445 : Vertex)) else decide (InPath q (446 : Vertex))))) else (if i < 99 then (if i < 97 then (if i < 96 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex))) else (if i < 98 then decide (InPath q (482 : Vertex)) else decide (InPath q (483 : Vertex)))) else (if i < 101 then (if i < 100 then decide (InPath q (484 : Vertex)) else decide (InPath q (486 : Vertex))) else (if i < 102 then decide (InPath q (487 : Vertex)) else decide (InPath q (488 : Vertex)))))) else (if i < 110 then (if i < 106 then (if i < 104 then decide (InPath q (489 : Vertex)) else (if i < 105 then decide (InPath q (490 : Vertex)) else decide (InPath q (491 : Vertex)))) else (if i < 108 then (if i < 107 then decide (InPath q (492 : Vertex)) else decide (InPath q (493 : Vertex))) else (if i < 109 then decide (InPath q (494 : Vertex)) else decide (InPath q (499 : Vertex))))) else (if i < 114 then (if i < 112 then (if i < 111 then decide (InPath q (500 : Vertex)) else decide (InPath q (501 : Vertex))) else (if i < 113 then decide (InPath q (502 : Vertex)) else decide (InPath q (503 : Vertex)))) else (if i < 116 then (if i < 115 then decide (InPath q (504 : Vertex)) else decide (InPath q (505 : Vertex))) else (if i < 117 then decide (InPath q (507 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 177 then (if i < 147 then (if i < 132 then (if i < 125 then (if i < 121 then (if i < 119 then decide (InPath q (511 : Vertex)) else (if i < 120 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else decide (BallClauseLogic.Endpoint q (14 : Vertex)))) else (if i < 123 then (if i < 122 then decide (BallClauseLogic.Endpoint q (33 : Vertex)) else decide (BallClauseLogic.Endpoint q (35 : Vertex))) else (if i < 124 then decide (BallClauseLogic.Endpoint q (37 : Vertex)) else decide (BallClauseLogic.Endpoint q (42 : Vertex))))) else (if i < 128 then (if i < 126 then decide (BallClauseLogic.Endpoint q (48 : Vertex)) else (if i < 127 then decide (BallClauseLogic.Endpoint q (49 : Vertex)) else decide (BallClauseLogic.Endpoint q (50 : Vertex)))) else (if i < 130 then (if i < 129 then decide (BallClauseLogic.Endpoint q (54 : Vertex)) else decide (BallClauseLogic.Endpoint q (58 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (96 : Vertex)) else decide (BallClauseLogic.Endpoint q (98 : Vertex)))))) else (if i < 139 then (if i < 135 then (if i < 133 then decide (BallClauseLogic.Endpoint q (100 : Vertex)) else (if i < 134 then decide (BallClauseLogic.Endpoint q (101 : Vertex)) else decide (BallClauseLogic.Endpoint q (102 : Vertex)))) else (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (104 : Vertex)) else decide (BallClauseLogic.Endpoint q (106 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (107 : Vertex)) else decide (BallClauseLogic.Endpoint q (108 : Vertex))))) else (if i < 143 then (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (110 : Vertex)) else decide (BallClauseLogic.Endpoint q (113 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (115 : Vertex)) else decide (BallClauseLogic.Endpoint q (117 : Vertex)))) else (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (118 : Vertex)) else decide (BallClauseLogic.Endpoint q (119 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (120 : Vertex)) else decide (BallClauseLogic.Endpoint q (121 : Vertex))))))) else (if i < 162 then (if i < 154 then (if i < 150 then (if i < 148 then decide (BallClauseLogic.Endpoint q (123 : Vertex)) else (if i < 149 then decide (BallClauseLogic.Endpoint q (225 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex)))) else (if i < 152 then (if i < 151 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else decide (BallClauseLogic.Endpoint q (231 : Vertex))) else (if i < 153 then decide (BallClauseLogic.Endpoint q (233 : Vertex)) else decide (BallClauseLogic.Endpoint q (234 : Vertex))))) else (if i < 158 then (if i < 156 then (if i < 155 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else decide (BallClauseLogic.Endpoint q (237 : Vertex))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (241 : Vertex)))) else (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (242 : Vertex)) else decide (BallClauseLogic.Endpoint q (244 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (250 : Vertex)) else decide (BallClauseLogic.Endpoint q (252 : Vertex)))))) else (if i < 169 then (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (253 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (254 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex)))) else (if i < 167 then (if i < 166 then decide (BallClauseLogic.Endpoint q (257 : Vertex)) else decide (BallClauseLogic.Endpoint q (259 : Vertex))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (266 : Vertex))))) else (if i < 173 then (if i < 171 then (if i < 170 then decide (BallClauseLogic.Endpoint q (267 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex))) else (if i < 172 then decide (BallClauseLogic.Endpoint q (269 : Vertex)) else decide (BallClauseLogic.Endpoint q (272 : Vertex)))) else (if i < 175 then (if i < 174 then decide (BallClauseLogic.Endpoint q (273 : Vertex)) else decide (BallClauseLogic.Endpoint q (274 : Vertex))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (278 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex)))))))) else (if i < 207 then (if i < 192 then (if i < 184 then (if i < 180 then (if i < 178 then decide (BallClauseLogic.Endpoint q (285 : Vertex)) else (if i < 179 then decide (BallClauseLogic.Endpoint q (286 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex)))) else (if i < 182 then (if i < 181 then decide (BallClauseLogic.Endpoint q (353 : Vertex)) else decide (BallClauseLogic.Endpoint q (355 : Vertex))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (356 : Vertex)) else decide (BallClauseLogic.Endpoint q (357 : Vertex))))) else (if i < 188 then (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (362 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (363 : Vertex)) else decide (BallClauseLogic.Endpoint q (364 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (365 : Vertex)) else decide (BallClauseLogic.Endpoint q (368 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (369 : Vertex)) else decide (BallClauseLogic.Endpoint q (370 : Vertex)))))) else (if i < 199 then (if i < 195 then (if i < 193 then decide (BallClauseLogic.Endpoint q (374 : Vertex)) else (if i < 194 then decide (BallClauseLogic.Endpoint q (378 : Vertex)) else decide (BallClauseLogic.Endpoint q (381 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (382 : Vertex)) else decide (BallClauseLogic.Endpoint q (383 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (417 : Vertex)) else decide (BallClauseLogic.Endpoint q (419 : Vertex))))) else (if i < 203 then (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (420 : Vertex)) else decide (BallClauseLogic.Endpoint q (421 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (426 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (427 : Vertex)) else decide (BallClauseLogic.Endpoint q (428 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (429 : Vertex)) else decide (BallClauseLogic.Endpoint q (432 : Vertex))))))) else (if i < 222 then (if i < 214 then (if i < 210 then (if i < 208 then decide (BallClauseLogic.Endpoint q (433 : Vertex)) else (if i < 209 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else decide (BallClauseLogic.Endpoint q (438 : Vertex)))) else (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (442 : Vertex)) else decide (BallClauseLogic.Endpoint q (445 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (446 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))))) else (if i < 218 then (if i < 216 then (if i < 215 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (482 : Vertex))) else (if i < 217 then decide (BallClauseLogic.Endpoint q (483 : Vertex)) else decide (BallClauseLogic.Endpoint q (484 : Vertex)))) else (if i < 220 then (if i < 219 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (487 : Vertex))) else (if i < 221 then decide (BallClauseLogic.Endpoint q (488 : Vertex)) else decide (BallClauseLogic.Endpoint q (489 : Vertex)))))) else (if i < 229 then (if i < 225 then (if i < 223 then decide (BallClauseLogic.Endpoint q (490 : Vertex)) else (if i < 224 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (492 : Vertex)))) else (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (494 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (500 : Vertex))))) else (if i < 233 then (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (503 : Vertex)) else decide (BallClauseLogic.Endpoint q (504 : Vertex)))) else (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (505 : Vertex)) else decide (BallClauseLogic.Endpoint q (507 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count237 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count239 (b : Nat → Bool) : Nat := countLit b [119, 120, 121]
def count241 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count245 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125]
def count247 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124, 125]
def count249 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [126, 127, 128]
def count253 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [126, 127, 128, 129, 130, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count271 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143, 144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
def count291 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [148, 149, 150]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [155, 156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 160]
def count311 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count313 (b : Nat → Bool) : Nat := countLit b [158, 160, 161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158, 160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count335 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count341 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177]
def count343 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [178, 179, 180]
def count355 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184]
def count363 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [185, 186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count377 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count393 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count399 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206]
def count401 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]
def count405 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]
def count407 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [207, 208, 209]
def count411 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213]
def count419 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count421 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count423 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [218, 219]
def count427 (b : Nat → Bool) : Nat := countLit b [220, 221]
def count429 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221]
def count431 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220, 221]
def count433 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]
def count435 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [222, 223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count441 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count443 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [222, 223, 224, 225, 226, 227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count451 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count455 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count457 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236]
def count459 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232, 233, 234, 235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]
def count463 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]
def count465 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]
def count467 (b : Nat → Bool) : Nat := countLit b [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236]
def count469 (b : Nat → Bool) : Nat := countLit b [3, 7]
def count471 (b : Nat → Bool) : Nat := countLit b [1, 3, 7]
def count474 (b : Nat → Bool) : Nat := countLit b [10, 11]
def count476 (b : Nat → Bool) : Nat := countLit b [12, 15]
def count478 (b : Nat → Bool) : Nat := countLit b [10, 11, 12, 15]
def count482 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 10, 11, 12, 15]
def count489 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count491 (b : Nat → Bool) : Nat := countLit b [16, 18, 20]
def count494 (b : Nat → Bool) : Nat := countLit b [22, 26]
def count496 (b : Nat → Bool) : Nat := countLit b [27, 29]
def count498 (b : Nat → Bool) : Nat := countLit b [22, 26, 27, 29]
def count502 (b : Nat → Bool) : Nat := countLit b [16, 18, 20, 22, 26, 27, 29]
def count509 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 10, 11, 12, 15, 16, 18, 20, 22, 26, 27, 29]
def count523 (b : Nat → Bool) : Nat := countLit b [32, 33]
def count525 (b : Nat → Bool) : Nat := countLit b [30, 32, 33]
def count528 (b : Nat → Bool) : Nat := countLit b [37, 38]
def count530 (b : Nat → Bool) : Nat := countLit b [42, 43]
def count532 (b : Nat → Bool) : Nat := countLit b [37, 38, 42, 43]
def count536 (b : Nat → Bool) : Nat := countLit b [30, 32, 33, 37, 38, 42, 43]
def count543 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count545 (b : Nat → Bool) : Nat := countLit b [51, 53]
def count547 (b : Nat → Bool) : Nat := countLit b [46, 47, 51, 53]
def count551 (b : Nat → Bool) : Nat := countLit b [54, 57]
def count553 (b : Nat → Bool) : Nat := countLit b [58, 61]
def count555 (b : Nat → Bool) : Nat := countLit b [54, 57, 58, 61]
def count559 (b : Nat → Bool) : Nat := countLit b [46, 47, 51, 53, 54, 57, 58, 61]
def count567 (b : Nat → Bool) : Nat := countLit b [30, 32, 33, 37, 38, 42, 43, 46, 47, 51, 53, 54, 57, 58, 61]
def count582 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 10, 11, 12, 15, 16, 18, 20, 22, 26, 27, 29, 30, 32, 33, 37, 38, 42, 43, 46, 47, 51, 53, 54, 57, 58, 61]
def count611 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count613 (b : Nat → Bool) : Nat := countLit b [62, 64, 66]
def count616 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count618 (b : Nat → Bool) : Nat := countLit b [71, 74]
def count620 (b : Nat → Bool) : Nat := countLit b [68, 70, 71, 74]
def count624 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 68, 70, 71, 74]
def count631 (b : Nat → Bool) : Nat := countLit b [78, 79]
def count633 (b : Nat → Bool) : Nat := countLit b [75, 78, 79]
def count636 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count638 (b : Nat → Bool) : Nat := countLit b [85, 87]
def count640 (b : Nat → Bool) : Nat := countLit b [81, 83, 85, 87]
def count644 (b : Nat → Bool) : Nat := countLit b [75, 78, 79, 81, 83, 85, 87]
def count651 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 68, 70, 71, 74, 75, 78, 79, 81, 83, 85, 87]
def count665 (b : Nat → Bool) : Nat := countLit b [91, 92]
def count667 (b : Nat → Bool) : Nat := countLit b [88, 91, 92]
def count670 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count672 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count674 (b : Nat → Bool) : Nat := countLit b [95, 96, 98, 100]
def count678 (b : Nat → Bool) : Nat := countLit b [88, 91, 92, 95, 96, 98, 100]
def count685 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count687 (b : Nat → Bool) : Nat := countLit b [106, 110]
def count689 (b : Nat → Bool) : Nat := countLit b [103, 104, 106, 110]
def count693 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count695 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count697 (b : Nat → Bool) : Nat := countLit b [113, 114, 116, 117]
def count701 (b : Nat → Bool) : Nat := countLit b [103, 104, 106, 110, 113, 114, 116, 117]
def count709 (b : Nat → Bool) : Nat := countLit b [88, 91, 92, 95, 96, 98, 100, 103, 104, 106, 110, 113, 114, 116, 117]
def count724 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 68, 70, 71, 74, 75, 78, 79, 81, 83, 85, 87, 88, 91, 92, 95, 96, 98, 100, 103, 104, 106, 110, 113, 114, 116, 117]
def count753 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 10, 11, 12, 15, 16, 18, 20, 22, 26, 27, 29, 30, 32, 33, 37, 38, 42, 43, 46, 47, 51, 53, 54, 57, 58, 61, 62, 64, 66, 68, 70, 71, 74, 75, 78, 79, 81, 83, 85, 87, 88, 91, 92, 95, 96, 98, 100, 103, 104, 106, 110, 113, 114, 116, 117]
def count795 (b : Nat → Bool) : Nat := countLit b [-3, -7]
def count797 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7]
def count800 (b : Nat → Bool) : Nat := countLit b [-10, -11]
def count802 (b : Nat → Bool) : Nat := countLit b [-12, -15]
def count804 (b : Nat → Bool) : Nat := countLit b [-10, -11, -12, -15]
def count808 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -10, -11, -12, -15]
def count815 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count817 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20]
def count820 (b : Nat → Bool) : Nat := countLit b [-22, -26]
def count822 (b : Nat → Bool) : Nat := countLit b [-27, -29]
def count824 (b : Nat → Bool) : Nat := countLit b [-22, -26, -27, -29]
def count828 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20, -22, -26, -27, -29]
def count835 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -10, -11, -12, -15, -16, -18, -20, -22, -26, -27, -29]
def count849 (b : Nat → Bool) : Nat := countLit b [-32, -33]
def count851 (b : Nat → Bool) : Nat := countLit b [-30, -32, -33]
def count854 (b : Nat → Bool) : Nat := countLit b [-37, -38]
def count856 (b : Nat → Bool) : Nat := countLit b [-42, -43]
def count858 (b : Nat → Bool) : Nat := countLit b [-37, -38, -42, -43]
def count862 (b : Nat → Bool) : Nat := countLit b [-30, -32, -33, -37, -38, -42, -43]
def count869 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count871 (b : Nat → Bool) : Nat := countLit b [-51, -53]
def count873 (b : Nat → Bool) : Nat := countLit b [-46, -47, -51, -53]
def count877 (b : Nat → Bool) : Nat := countLit b [-54, -57]
def count879 (b : Nat → Bool) : Nat := countLit b [-58, -61]
def count881 (b : Nat → Bool) : Nat := countLit b [-54, -57, -58, -61]
def count885 (b : Nat → Bool) : Nat := countLit b [-46, -47, -51, -53, -54, -57, -58, -61]
def count893 (b : Nat → Bool) : Nat := countLit b [-30, -32, -33, -37, -38, -42, -43, -46, -47, -51, -53, -54, -57, -58, -61]
def count908 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -10, -11, -12, -15, -16, -18, -20, -22, -26, -27, -29, -30, -32, -33, -37, -38, -42, -43, -46, -47, -51, -53, -54, -57, -58, -61]
def count926 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count928 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66]
def count931 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count933 (b : Nat → Bool) : Nat := countLit b [-71, -74]
def count935 (b : Nat → Bool) : Nat := countLit b [-68, -70, -71, -74]
def count939 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -68, -70, -71, -74]
def count946 (b : Nat → Bool) : Nat := countLit b [-78, -79]
def count948 (b : Nat → Bool) : Nat := countLit b [-75, -78, -79]
def count951 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count953 (b : Nat → Bool) : Nat := countLit b [-85, -87]
def count955 (b : Nat → Bool) : Nat := countLit b [-81, -83, -85, -87]
def count959 (b : Nat → Bool) : Nat := countLit b [-75, -78, -79, -81, -83, -85, -87]
def count966 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -68, -70, -71, -74, -75, -78, -79, -81, -83, -85, -87]
def count980 (b : Nat → Bool) : Nat := countLit b [-91, -92]
def count982 (b : Nat → Bool) : Nat := countLit b [-88, -91, -92]
def count985 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count987 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count989 (b : Nat → Bool) : Nat := countLit b [-95, -96, -98, -100]
def count993 (b : Nat → Bool) : Nat := countLit b [-88, -91, -92, -95, -96, -98, -100]
def count1000 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1002 (b : Nat → Bool) : Nat := countLit b [-106, -110]
def count1004 (b : Nat → Bool) : Nat := countLit b [-103, -104, -106, -110]
def count1008 (b : Nat → Bool) : Nat := countLit b [-113, -114]
def count1010 (b : Nat → Bool) : Nat := countLit b [-116, -117]
def count1012 (b : Nat → Bool) : Nat := countLit b [-113, -114, -116, -117]
def count1016 (b : Nat → Bool) : Nat := countLit b [-103, -104, -106, -110, -113, -114, -116, -117]
def count1024 (b : Nat → Bool) : Nat := countLit b [-88, -91, -92, -95, -96, -98, -100, -103, -104, -106, -110, -113, -114, -116, -117]
def count1039 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -68, -70, -71, -74, -75, -78, -79, -81, -83, -85, -87, -88, -91, -92, -95, -96, -98, -100, -103, -104, -106, -110, -113, -114, -116, -117]
def count1057 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -10, -11, -12, -15, -16, -18, -20, -22, -26, -27, -29, -30, -32, -33, -37, -38, -42, -43, -46, -47, -51, -53, -54, -57, -58, -61, -62, -64, -66, -68, -70, -71, -74, -75, -78, -79, -81, -83, -85, -87, -88, -91, -92, -95, -96, -98, -100, -103, -104, -106, -110, -113, -114, -116, -117]
def count1075 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count1077 (b : Nat → Bool) : Nat := countLit b [2, 4, 5]
def count1080 (b : Nat → Bool) : Nat := countLit b [6, 8]
def count1082 (b : Nat → Bool) : Nat := countLit b [9, 13]
def count1084 (b : Nat → Bool) : Nat := countLit b [6, 8, 9, 13]
def count1088 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 8, 9, 13]
def count1095 (b : Nat → Bool) : Nat := countLit b [14, 17]
def count1097 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count1099 (b : Nat → Bool) : Nat := countLit b [14, 17, 19, 21]
def count1103 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count1105 (b : Nat → Bool) : Nat := countLit b [25, 28]
def count1107 (b : Nat → Bool) : Nat := countLit b [23, 24, 25, 28]
def count1111 (b : Nat → Bool) : Nat := countLit b [14, 17, 19, 21, 23, 24, 25, 28]
def count1119 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 8, 9, 13, 14, 17, 19, 21, 23, 24, 25, 28]
def count1134 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count1136 (b : Nat → Bool) : Nat := countLit b [31, 34, 35]
def count1139 (b : Nat → Bool) : Nat := countLit b [36, 39]
def count1141 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count1143 (b : Nat → Bool) : Nat := countLit b [36, 39, 40, 41]
def count1147 (b : Nat → Bool) : Nat := countLit b [31, 34, 35, 36, 39, 40, 41]
def count1154 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count1156 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count1158 (b : Nat → Bool) : Nat := countLit b [44, 45, 48, 49]
def count1162 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count1164 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count1166 (b : Nat → Bool) : Nat := countLit b [50, 52, 55, 56]
def count1170 (b : Nat → Bool) : Nat := countLit b [44, 45, 48, 49, 50, 52, 55, 56]
def count1178 (b : Nat → Bool) : Nat := countLit b [31, 34, 35, 36, 39, 40, 41, 44, 45, 48, 49, 50, 52, 55, 56]
def count1193 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 8, 9, 13, 14, 17, 19, 21, 23, 24, 25, 28, 31, 34, 35, 36, 39, 40, 41, 44, 45, 48, 49, 50, 52, 55, 56]
def count1223 (b : Nat → Bool) : Nat := countLit b [60, 63]
def count1225 (b : Nat → Bool) : Nat := countLit b [59, 60, 63]
def count1228 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count1230 (b : Nat → Bool) : Nat := countLit b [69, 72]
def count1232 (b : Nat → Bool) : Nat := countLit b [65, 67, 69, 72]
def count1236 (b : Nat → Bool) : Nat := countLit b [59, 60, 63, 65, 67, 69, 72]
def count1243 (b : Nat → Bool) : Nat := countLit b [73, 76]
def count1245 (b : Nat → Bool) : Nat := countLit b [77, 80]
def count1247 (b : Nat → Bool) : Nat := countLit b [73, 76, 77, 80]
def count1251 (b : Nat → Bool) : Nat := countLit b [82, 84]
def count1253 (b : Nat → Bool) : Nat := countLit b [86, 89]
def count1255 (b : Nat → Bool) : Nat := countLit b [82, 84, 86, 89]
def count1259 (b : Nat → Bool) : Nat := countLit b [73, 76, 77, 80, 82, 84, 86, 89]
def count1267 (b : Nat → Bool) : Nat := countLit b [59, 60, 63, 65, 67, 69, 72, 73, 76, 77, 80, 82, 84, 86, 89]
def count1282 (b : Nat → Bool) : Nat := countLit b [93, 94]
def count1284 (b : Nat → Bool) : Nat := countLit b [90, 93, 94]
def count1287 (b : Nat → Bool) : Nat := countLit b [97, 99]
def count1289 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count1291 (b : Nat → Bool) : Nat := countLit b [97, 99, 101, 102]
def count1295 (b : Nat → Bool) : Nat := countLit b [90, 93, 94, 97, 99, 101, 102]
def count1302 (b : Nat → Bool) : Nat := countLit b [105, 107]
def count1304 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count1306 (b : Nat → Bool) : Nat := countLit b [105, 107, 108, 109]
def count1310 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count1312 (b : Nat → Bool) : Nat := countLit b [115, 118]
def count1314 (b : Nat → Bool) : Nat := countLit b [111, 112, 115, 118]
def count1318 (b : Nat → Bool) : Nat := countLit b [105, 107, 108, 109, 111, 112, 115, 118]
def count1326 (b : Nat → Bool) : Nat := countLit b [90, 93, 94, 97, 99, 101, 102, 105, 107, 108, 109, 111, 112, 115, 118]
def count1341 (b : Nat → Bool) : Nat := countLit b [59, 60, 63, 65, 67, 69, 72, 73, 76, 77, 80, 82, 84, 86, 89, 90, 93, 94, 97, 99, 101, 102, 105, 107, 108, 109, 111, 112, 115, 118]
def count1371 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 8, 9, 13, 14, 17, 19, 21, 23, 24, 25, 28, 31, 34, 35, 36, 39, 40, 41, 44, 45, 48, 49, 50, 52, 55, 56, 59, 60, 63, 65, 67, 69, 72, 73, 76, 77, 80, 82, 84, 86, 89, 90, 93, 94, 97, 99, 101, 102, 105, 107, 108, 109, 111, 112, 115, 118]
def count1413 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1415 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5]
def count1418 (b : Nat → Bool) : Nat := countLit b [-6, -8]
def count1420 (b : Nat → Bool) : Nat := countLit b [-9, -13]
def count1422 (b : Nat → Bool) : Nat := countLit b [-6, -8, -9, -13]
def count1426 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -8, -9, -13]
def count1433 (b : Nat → Bool) : Nat := countLit b [-14, -17]
def count1435 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count1437 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19, -21]
def count1441 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count1443 (b : Nat → Bool) : Nat := countLit b [-25, -28]
def count1445 (b : Nat → Bool) : Nat := countLit b [-23, -24, -25, -28]
def count1449 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19, -21, -23, -24, -25, -28]
def count1457 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28]
def count1472 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count1474 (b : Nat → Bool) : Nat := countLit b [-31, -34, -35]
def count1477 (b : Nat → Bool) : Nat := countLit b [-36, -39]
def count1479 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count1481 (b : Nat → Bool) : Nat := countLit b [-36, -39, -40, -41]
def count1485 (b : Nat → Bool) : Nat := countLit b [-31, -34, -35, -36, -39, -40, -41]
def count1492 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count1494 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count1496 (b : Nat → Bool) : Nat := countLit b [-44, -45, -48, -49]
def count1500 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count1502 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count1504 (b : Nat → Bool) : Nat := countLit b [-50, -52, -55, -56]
def count1508 (b : Nat → Bool) : Nat := countLit b [-44, -45, -48, -49, -50, -52, -55, -56]
def count1516 (b : Nat → Bool) : Nat := countLit b [-31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]
def count1531 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56]
def count1551 (b : Nat → Bool) : Nat := countLit b [-60, -63]
def count1553 (b : Nat → Bool) : Nat := countLit b [-59, -60, -63]
def count1556 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count1558 (b : Nat → Bool) : Nat := countLit b [-69, -72]
def count1560 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69, -72]
def count1564 (b : Nat → Bool) : Nat := countLit b [-59, -60, -63, -65, -67, -69, -72]
def count1571 (b : Nat → Bool) : Nat := countLit b [-73, -76]
def count1573 (b : Nat → Bool) : Nat := countLit b [-77, -80]
def count1575 (b : Nat → Bool) : Nat := countLit b [-73, -76, -77, -80]
def count1579 (b : Nat → Bool) : Nat := countLit b [-82, -84]
def count1581 (b : Nat → Bool) : Nat := countLit b [-86, -89]
def count1583 (b : Nat → Bool) : Nat := countLit b [-82, -84, -86, -89]
def count1587 (b : Nat → Bool) : Nat := countLit b [-73, -76, -77, -80, -82, -84, -86, -89]
def count1595 (b : Nat → Bool) : Nat := countLit b [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]
def count1610 (b : Nat → Bool) : Nat := countLit b [-93, -94]
def count1612 (b : Nat → Bool) : Nat := countLit b [-90, -93, -94]
def count1615 (b : Nat → Bool) : Nat := countLit b [-97, -99]
def count1617 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count1619 (b : Nat → Bool) : Nat := countLit b [-97, -99, -101, -102]
def count1623 (b : Nat → Bool) : Nat := countLit b [-90, -93, -94, -97, -99, -101, -102]
def count1630 (b : Nat → Bool) : Nat := countLit b [-105, -107]
def count1632 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count1634 (b : Nat → Bool) : Nat := countLit b [-105, -107, -108, -109]
def count1638 (b : Nat → Bool) : Nat := countLit b [-111, -112]
def count1640 (b : Nat → Bool) : Nat := countLit b [-115, -118]
def count1642 (b : Nat → Bool) : Nat := countLit b [-111, -112, -115, -118]
def count1646 (b : Nat → Bool) : Nat := countLit b [-105, -107, -108, -109, -111, -112, -115, -118]
def count1654 (b : Nat → Bool) : Nat := countLit b [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]
def count1669 (b : Nat → Bool) : Nat := countLit b [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]
def count1689 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -8, -9, -13, -14, -17, -19, -21, -23, -24, -25, -28, -31, -34, -35, -36, -39, -40, -41, -44, -45, -48, -49, -50, -52, -55, -56, -59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89, -90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 854 then (if i < 427 then (if i < 213 then (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 19 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 17 then b 16 else (if i < 18 then b 17 else b 18))) else (if i < 22 then (if i < 20 then b 19 else (if i < 21 then b 20 else b 21)) else (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else b 25))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31))) else (if i < 35 then (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)) else (if i < 37 then (if i < 36 then b 35 else b 36) else (if i < 38 then b 37 else b 38)))) else (if i < 46 then (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 44 then (if i < 43 then b 42 else b 43) else (if i < 45 then b 44 else b 45))) else (if i < 49 then (if i < 47 then b 46 else (if i < 48 then b 47 else b 48)) else (if i < 51 then (if i < 50 then b 49 else b 50) else (if i < 52 then b 51 else b 52)))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)) else (if i < 57 then b 56 else (if i < 58 then b 57 else b 58))) else (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 64 then (if i < 63 then b 62 else b 63) else (if i < 65 then b 64 else b 65)))) else (if i < 72 then (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))) else (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 77 then (if i < 76 then b 75 else b 76) else (if i < 78 then b 77 else b 78))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then b 79 else (if i < 81 then b 80 else b 81)) else (if i < 83 then b 82 else (if i < 84 then b 83 else b 84))) else (if i < 88 then (if i < 86 then b 85 else (if i < 87 then b 86 else b 87)) else (if i < 90 then (if i < 89 then b 88 else b 89) else (if i < 91 then b 90 else b 91)))) else (if i < 99 then (if i < 95 then (if i < 93 then b 92 else (if i < 94 then b 93 else b 94)) else (if i < 97 then (if i < 96 then b 95 else b 96) else (if i < 98 then b 97 else b 98))) else (if i < 102 then (if i < 100 then b 99 else (if i < 101 then b 100 else b 101)) else (if i < 104 then (if i < 103 then b 102 else b 103) else (if i < 105 then b 104 else b 105))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111))) else (if i < 115 then (if i < 113 then b 112 else (if i < 114 then b 113 else b 114)) else (if i < 117 then (if i < 116 then b 115 else b 116) else (if i < 118 then b 117 else b 118)))) else (if i < 125 then (if i < 122 then (if i < 120 then b 119 else (if i < 121 then b 120 else b 121)) else (if i < 123 then b 122 else (if i < 124 then b 123 else b 124))) else (if i < 128 then (if i < 126 then b 125 else (if i < 127 then b 126 else b 127)) else (if i < 130 then (if i < 129 then b 128 else b 129) else (if i < 131 then b 130 else b 131))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)) else (if i < 136 then b 135 else (if i < 137 then b 136 else b 137))) else (if i < 141 then (if i < 139 then b 138 else (if i < 140 then b 139 else b 140)) else (if i < 143 then (if i < 142 then b 141 else b 142) else (if i < 144 then b 143 else b 144)))) else (if i < 152 then (if i < 148 then (if i < 146 then b 145 else (if i < 147 then b 146 else b 147)) else (if i < 150 then (if i < 149 then b 148 else b 149) else (if i < 151 then b 150 else b 151))) else (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 157 then (if i < 156 then b 155 else b 156) else (if i < 158 then b 157 else b 158)))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 163 then b 162 else (if i < 164 then b 163 else b 164))) else (if i < 168 then (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)) else (if i < 170 then (if i < 169 then b 168 else b 169) else (if i < 171 then b 170 else b 171)))) else (if i < 179 then (if i < 175 then (if i < 173 then b 172 else (if i < 174 then b 173 else b 174)) else (if i < 177 then (if i < 176 then b 175 else b 176) else (if i < 178 then b 177 else b 178))) else (if i < 182 then (if i < 180 then b 179 else (if i < 181 then b 180 else b 181)) else (if i < 184 then (if i < 183 then b 182 else b 183) else (if i < 185 then b 184 else b 185))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then b 186 else (if i < 188 then b 187 else b 188)) else (if i < 190 then b 189 else (if i < 191 then b 190 else b 191))) else (if i < 195 then (if i < 193 then b 192 else (if i < 194 then b 193 else b 194)) else (if i < 197 then (if i < 196 then b 195 else b 196) else (if i < 198 then b 197 else b 198)))) else (if i < 206 then (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 204 then (if i < 203 then b 202 else b 203) else (if i < 205 then b 204 else b 205))) else (if i < 209 then (if i < 207 then b 206 else (if i < 208 then b 207 else b 208)) else (if i < 211 then (if i < 210 then b 209 else b 210) else (if i < 212 then b 211 else b 212)))))))) else (if i < 320 then (if i < 266 then (if i < 239 then (if i < 226 then (if i < 219 then (if i < 216 then (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)) else (if i < 217 then b 216 else (if i < 218 then b 217 else b 218))) else (if i < 222 then (if i < 220 then b 219 else (if i < 221 then b 220 else b 221)) else (if i < 224 then (if i < 223 then b 222 else b 223) else (if i < 225 then b 224 else b 225)))) else (if i < 232 then (if i < 229 then (if i < 227 then b 226 else (if i < 228 then b 227 else b 228)) else (if i < 230 then b 229 else (if i < 231 then b 230 else b 231))) else (if i < 235 then (if i < 233 then b 232 else (if i < 234 then b 233 else b 234)) else (if i < 237 then (if i < 236 then b 235 else b 236) else (if i < 238 then decide (1 ≤ count237 b) else decide (2 ≤ count237 b)))))) else (if i < 252 then (if i < 245 then (if i < 242 then (if i < 240 then decide (1 ≤ count239 b) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b))) else (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b)))) else (if i < 248 then (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))) else (if i < 250 then (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b)) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))))) else (if i < 259 then (if i < 255 then (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))) else (if i < 257 then (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b)) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)))) else (if i < 262 then (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))) else (if i < 264 then (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)) else (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b))))))) else (if i < 293 then (if i < 279 then (if i < 272 then (if i < 269 then (if i < 267 then decide (2 ≤ count265 b) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b))) else (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)))) else (if i < 275 then (if i < 273 then decide (2 ≤ count271 b) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b))) else (if i < 277 then (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b)) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))))) else (if i < 286 then (if i < 282 then (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))) else (if i < 284 then (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)))) else (if i < 289 then (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))) else (if i < 291 then (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b)) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))))) else (if i < 306 then (if i < 299 then (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))) else (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b))))) else (if i < 313 then (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))) else (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))))))) else (if i < 373 then (if i < 346 then (if i < 333 then (if i < 326 then (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b)))) else (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 331 then (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))))) else (if i < 339 then (if i < 336 then (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))) else (if i < 342 then (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))) else (if i < 344 then (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b)) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b)))))) else (if i < 359 then (if i < 352 then (if i < 349 then (if i < 347 then decide (2 ≤ count345 b) else (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b))) else (if i < 350 then decide (1 ≤ count349 b) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)))) else (if i < 355 then (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b))) else (if i < 357 then (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b))))) else (if i < 366 then (if i < 362 then (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b))) else (if i < 364 then (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))) else (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 371 then (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))))))) else (if i < 400 then (if i < 386 then (if i < 379 then (if i < 376 then (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b))) else (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)))) else (if i < 382 then (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))) else (if i < 384 then (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))))) else (if i < 393 then (if i < 389 then (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))) else (if i < 391 then (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b)))) else (if i < 396 then (if i < 394 then decide (1 ≤ count393 b) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))) else (if i < 398 then (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b)) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))))) else (if i < 413 then (if i < 406 then (if i < 403 then (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))) else (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b)))) else (if i < 409 then (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 411 then (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))))) else (if i < 420 then (if i < 416 then (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b))) else (if i < 418 then (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)))) else (if i < 423 then (if i < 421 then decide (2 ≤ count419 b) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b))) else (if i < 425 then (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b)) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)))))))))) else (if i < 640 then (if i < 533 then (if i < 480 then (if i < 453 then (if i < 440 then (if i < 433 then (if i < 430 then (if i < 428 then decide (1 ≤ count427 b) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 431 then decide (2 ≤ count429 b) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)))) else (if i < 436 then (if i < 434 then decide (1 ≤ count433 b) else (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b))) else (if i < 438 then (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b)) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))))) else (if i < 446 then (if i < 443 then (if i < 441 then decide (2 ≤ count439 b) else (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b))) else (if i < 444 then decide (1 ≤ count443 b) else (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)))) else (if i < 449 then (if i < 447 then decide (2 ≤ count445 b) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b))) else (if i < 451 then (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b)))))) else (if i < 466 then (if i < 459 then (if i < 456 then (if i < 454 then decide (1 ≤ count453 b) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b))) else (if i < 457 then decide (2 ≤ count455 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)))) else (if i < 462 then (if i < 460 then decide (1 ≤ count459 b) else (if i < 461 then decide (2 ≤ count459 b) else decide (1 ≤ count461 b))) else (if i < 464 then (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b)) else (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b))))) else (if i < 473 then (if i < 469 then (if i < 467 then decide (2 ≤ count465 b) else (if i < 468 then decide (1 ≤ count467 b) else decide (2 ≤ count467 b))) else (if i < 471 then (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b)) else (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b)))) else (if i < 476 then (if i < 474 then decide (3 ≤ count471 b) else (if i < 475 then decide (1 ≤ count474 b) else decide (2 ≤ count474 b))) else (if i < 478 then (if i < 477 then decide (1 ≤ count476 b) else decide (2 ≤ count476 b)) else (if i < 479 then decide (1 ≤ count478 b) else decide (2 ≤ count478 b))))))) else (if i < 506 then (if i < 493 then (if i < 486 then (if i < 483 then (if i < 481 then decide (3 ≤ count478 b) else (if i < 482 then decide (4 ≤ count478 b) else decide (1 ≤ count482 b))) else (if i < 484 then decide (2 ≤ count482 b) else (if i < 485 then decide (3 ≤ count482 b) else decide (4 ≤ count482 b)))) else (if i < 489 then (if i < 487 then decide (5 ≤ count482 b) else (if i < 488 then decide (6 ≤ count482 b) else decide (7 ≤ count482 b))) else (if i < 491 then (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b)) else (if i < 492 then decide (1 ≤ count491 b) else decide (2 ≤ count491 b))))) else (if i < 499 then (if i < 496 then (if i < 494 then decide (3 ≤ count491 b) else (if i < 495 then decide (1 ≤ count494 b) else decide (2 ≤ count494 b))) else (if i < 497 then decide (1 ≤ count496 b) else (if i < 498 then decide (2 ≤ count496 b) else decide (1 ≤ count498 b)))) else (if i < 502 then (if i < 500 then decide (2 ≤ count498 b) else (if i < 501 then decide (3 ≤ count498 b) else decide (4 ≤ count498 b))) else (if i < 504 then (if i < 503 then decide (1 ≤ count502 b) else decide (2 ≤ count502 b)) else (if i < 505 then decide (3 ≤ count502 b) else decide (4 ≤ count502 b)))))) else (if i < 519 then (if i < 512 then (if i < 509 then (if i < 507 then decide (5 ≤ count502 b) else (if i < 508 then decide (6 ≤ count502 b) else decide (7 ≤ count502 b))) else (if i < 510 then decide (1 ≤ count509 b) else (if i < 511 then decide (2 ≤ count509 b) else decide (3 ≤ count509 b)))) else (if i < 515 then (if i < 513 then decide (4 ≤ count509 b) else (if i < 514 then decide (5 ≤ count509 b) else decide (6 ≤ count509 b))) else (if i < 517 then (if i < 516 then decide (7 ≤ count509 b) else decide (8 ≤ count509 b)) else (if i < 518 then decide (9 ≤ count509 b) else decide (10 ≤ count509 b))))) else (if i < 526 then (if i < 522 then (if i < 520 then decide (11 ≤ count509 b) else (if i < 521 then decide (12 ≤ count509 b) else decide (13 ≤ count509 b))) else (if i < 524 then (if i < 523 then decide (14 ≤ count509 b) else decide (1 ≤ count523 b)) else (if i < 525 then decide (2 ≤ count523 b) else decide (1 ≤ count525 b)))) else (if i < 529 then (if i < 527 then decide (2 ≤ count525 b) else (if i < 528 then decide (3 ≤ count525 b) else decide (1 ≤ count528 b))) else (if i < 531 then (if i < 530 then decide (2 ≤ count528 b) else decide (1 ≤ count530 b)) else (if i < 532 then decide (2 ≤ count530 b) else decide (1 ≤ count532 b)))))))) else (if i < 586 then (if i < 559 then (if i < 546 then (if i < 539 then (if i < 536 then (if i < 534 then decide (2 ≤ count532 b) else (if i < 535 then decide (3 ≤ count532 b) else decide (4 ≤ count532 b))) else (if i < 537 then decide (1 ≤ count536 b) else (if i < 538 then decide (2 ≤ count536 b) else decide (3 ≤ count536 b)))) else (if i < 542 then (if i < 540 then decide (4 ≤ count536 b) else (if i < 541 then decide (5 ≤ count536 b) else decide (6 ≤ count536 b))) else (if i < 544 then (if i < 543 then decide (7 ≤ count536 b) else decide (1 ≤ count543 b)) else (if i < 545 then decide (2 ≤ count543 b) else decide (1 ≤ count545 b))))) else (if i < 552 then (if i < 549 then (if i < 547 then decide (2 ≤ count545 b) else (if i < 548 then decide (1 ≤ count547 b) else decide (2 ≤ count547 b))) else (if i < 550 then decide (3 ≤ count547 b) else (if i < 551 then decide (4 ≤ count547 b) else decide (1 ≤ count551 b)))) else (if i < 555 then (if i < 553 then decide (2 ≤ count551 b) else (if i < 554 then decide (1 ≤ count553 b) else decide (2 ≤ count553 b))) else (if i < 557 then (if i < 556 then decide (1 ≤ count555 b) else decide (2 ≤ count555 b)) else (if i < 558 then decide (3 ≤ count555 b) else decide (4 ≤ count555 b)))))) else (if i < 572 then (if i < 565 then (if i < 562 then (if i < 560 then decide (1 ≤ count559 b) else (if i < 561 then decide (2 ≤ count559 b) else decide (3 ≤ count559 b))) else (if i < 563 then decide (4 ≤ count559 b) else (if i < 564 then decide (5 ≤ count559 b) else decide (6 ≤ count559 b)))) else (if i < 568 then (if i < 566 then decide (7 ≤ count559 b) else (if i < 567 then decide (8 ≤ count559 b) else decide (1 ≤ count567 b))) else (if i < 570 then (if i < 569 then decide (2 ≤ count567 b) else decide (3 ≤ count567 b)) else (if i < 571 then decide (4 ≤ count567 b) else decide (5 ≤ count567 b))))) else (if i < 579 then (if i < 575 then (if i < 573 then decide (6 ≤ count567 b) else (if i < 574 then decide (7 ≤ count567 b) else decide (8 ≤ count567 b))) else (if i < 577 then (if i < 576 then decide (9 ≤ count567 b) else decide (10 ≤ count567 b)) else (if i < 578 then decide (11 ≤ count567 b) else decide (12 ≤ count567 b)))) else (if i < 582 then (if i < 580 then decide (13 ≤ count567 b) else (if i < 581 then decide (14 ≤ count567 b) else decide (15 ≤ count567 b))) else (if i < 584 then (if i < 583 then decide (1 ≤ count582 b) else decide (2 ≤ count582 b)) else (if i < 585 then decide (3 ≤ count582 b) else decide (4 ≤ count582 b))))))) else (if i < 613 then (if i < 599 then (if i < 592 then (if i < 589 then (if i < 587 then decide (5 ≤ count582 b) else (if i < 588 then decide (6 ≤ count582 b) else decide (7 ≤ count582 b))) else (if i < 590 then decide (8 ≤ count582 b) else (if i < 591 then decide (9 ≤ count582 b) else decide (10 ≤ count582 b)))) else (if i < 595 then (if i < 593 then decide (11 ≤ count582 b) else (if i < 594 then decide (12 ≤ count582 b) else decide (13 ≤ count582 b))) else (if i < 597 then (if i < 596 then decide (14 ≤ count582 b) else decide (15 ≤ count582 b)) else (if i < 598 then decide (16 ≤ count582 b) else decide (17 ≤ count582 b))))) else (if i < 606 then (if i < 602 then (if i < 600 then decide (18 ≤ count582 b) else (if i < 601 then decide (19 ≤ count582 b) else decide (20 ≤ count582 b))) else (if i < 604 then (if i < 603 then decide (21 ≤ count582 b) else decide (22 ≤ count582 b)) else (if i < 605 then decide (23 ≤ count582 b) else decide (24 ≤ count582 b)))) else (if i < 609 then (if i < 607 then decide (25 ≤ count582 b) else (if i < 608 then decide (26 ≤ count582 b) else decide (27 ≤ count582 b))) else (if i < 611 then (if i < 610 then decide (28 ≤ count582 b) else decide (29 ≤ count582 b)) else (if i < 612 then decide (1 ≤ count611 b) else decide (2 ≤ count611 b)))))) else (if i < 626 then (if i < 619 then (if i < 616 then (if i < 614 then decide (1 ≤ count613 b) else (if i < 615 then decide (2 ≤ count613 b) else decide (3 ≤ count613 b))) else (if i < 617 then decide (1 ≤ count616 b) else (if i < 618 then decide (2 ≤ count616 b) else decide (1 ≤ count618 b)))) else (if i < 622 then (if i < 620 then decide (2 ≤ count618 b) else (if i < 621 then decide (1 ≤ count620 b) else decide (2 ≤ count620 b))) else (if i < 624 then (if i < 623 then decide (3 ≤ count620 b) else decide (4 ≤ count620 b)) else (if i < 625 then decide (1 ≤ count624 b) else decide (2 ≤ count624 b))))) else (if i < 633 then (if i < 629 then (if i < 627 then decide (3 ≤ count624 b) else (if i < 628 then decide (4 ≤ count624 b) else decide (5 ≤ count624 b))) else (if i < 631 then (if i < 630 then decide (6 ≤ count624 b) else decide (7 ≤ count624 b)) else (if i < 632 then decide (1 ≤ count631 b) else decide (2 ≤ count631 b)))) else (if i < 636 then (if i < 634 then decide (1 ≤ count633 b) else (if i < 635 then decide (2 ≤ count633 b) else decide (3 ≤ count633 b))) else (if i < 638 then (if i < 637 then decide (1 ≤ count636 b) else decide (2 ≤ count636 b)) else (if i < 639 then decide (1 ≤ count638 b) else decide (2 ≤ count638 b))))))))) else (if i < 747 then (if i < 693 then (if i < 666 then (if i < 653 then (if i < 646 then (if i < 643 then (if i < 641 then decide (1 ≤ count640 b) else (if i < 642 then decide (2 ≤ count640 b) else decide (3 ≤ count640 b))) else (if i < 644 then decide (4 ≤ count640 b) else (if i < 645 then decide (1 ≤ count644 b) else decide (2 ≤ count644 b)))) else (if i < 649 then (if i < 647 then decide (3 ≤ count644 b) else (if i < 648 then decide (4 ≤ count644 b) else decide (5 ≤ count644 b))) else (if i < 651 then (if i < 650 then decide (6 ≤ count644 b) else decide (7 ≤ count644 b)) else (if i < 652 then decide (1 ≤ count651 b) else decide (2 ≤ count651 b))))) else (if i < 659 then (if i < 656 then (if i < 654 then decide (3 ≤ count651 b) else (if i < 655 then decide (4 ≤ count651 b) else decide (5 ≤ count651 b))) else (if i < 657 then decide (6 ≤ count651 b) else (if i < 658 then decide (7 ≤ count651 b) else decide (8 ≤ count651 b)))) else (if i < 662 then (if i < 660 then decide (9 ≤ count651 b) else (if i < 661 then decide (10 ≤ count651 b) else decide (11 ≤ count651 b))) else (if i < 664 then (if i < 663 then decide (12 ≤ count651 b) else decide (13 ≤ count651 b)) else (if i < 665 then decide (14 ≤ count651 b) else decide (1 ≤ count665 b)))))) else (if i < 679 then (if i < 672 then (if i < 669 then (if i < 667 then decide (2 ≤ count665 b) else (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b))) else (if i < 670 then decide (3 ≤ count667 b) else (if i < 671 then decide (1 ≤ count670 b) else decide (2 ≤ count670 b)))) else (if i < 675 then (if i < 673 then decide (1 ≤ count672 b) else (if i < 674 then decide (2 ≤ count672 b) else decide (1 ≤ count674 b))) else (if i < 677 then (if i < 676 then decide (2 ≤ count674 b) else decide (3 ≤ count674 b)) else (if i < 678 then decide (4 ≤ count674 b) else decide (1 ≤ count678 b))))) else (if i < 686 then (if i < 682 then (if i < 680 then decide (2 ≤ count678 b) else (if i < 681 then decide (3 ≤ count678 b) else decide (4 ≤ count678 b))) else (if i < 684 then (if i < 683 then decide (5 ≤ count678 b) else decide (6 ≤ count678 b)) else (if i < 685 then decide (7 ≤ count678 b) else decide (1 ≤ count685 b)))) else (if i < 689 then (if i < 687 then decide (2 ≤ count685 b) else (if i < 688 then decide (1 ≤ count687 b) else decide (2 ≤ count687 b))) else (if i < 691 then (if i < 690 then decide (1 ≤ count689 b) else decide (2 ≤ count689 b)) else (if i < 692 then decide (3 ≤ count689 b) else decide (4 ≤ count689 b))))))) else (if i < 720 then (if i < 706 then (if i < 699 then (if i < 696 then (if i < 694 then decide (1 ≤ count693 b) else (if i < 695 then decide (2 ≤ count693 b) else decide (1 ≤ count695 b))) else (if i < 697 then decide (2 ≤ count695 b) else (if i < 698 then decide (1 ≤ count697 b) else decide (2 ≤ count697 b)))) else (if i < 702 then (if i < 700 then decide (3 ≤ count697 b) else (if i < 701 then decide (4 ≤ count697 b) else decide (1 ≤ count701 b))) else (if i < 704 then (if i < 703 then decide (2 ≤ count701 b) else decide (3 ≤ count701 b)) else (if i < 705 then decide (4 ≤ count701 b) else decide (5 ≤ count701 b))))) else (if i < 713 then (if i < 709 then (if i < 707 then decide (6 ≤ count701 b) else (if i < 708 then decide (7 ≤ count701 b) else decide (8 ≤ count701 b))) else (if i < 711 then (if i < 710 then decide (1 ≤ count709 b) else decide (2 ≤ count709 b)) else (if i < 712 then decide (3 ≤ count709 b) else decide (4 ≤ count709 b)))) else (if i < 716 then (if i < 714 then decide (5 ≤ count709 b) else (if i < 715 then decide (6 ≤ count709 b) else decide (7 ≤ count709 b))) else (if i < 718 then (if i < 717 then decide (8 ≤ count709 b) else decide (9 ≤ count709 b)) else (if i < 719 then decide (10 ≤ count709 b) else decide (11 ≤ count709 b)))))) else (if i < 733 then (if i < 726 then (if i < 723 then (if i < 721 then decide (12 ≤ count709 b) else (if i < 722 then decide (13 ≤ count709 b) else decide (14 ≤ count709 b))) else (if i < 724 then decide (15 ≤ count709 b) else (if i < 725 then decide (1 ≤ count724 b) else decide (2 ≤ count724 b)))) else (if i < 729 then (if i < 727 then decide (3 ≤ count724 b) else (if i < 728 then decide (4 ≤ count724 b) else decide (5 ≤ count724 b))) else (if i < 731 then (if i < 730 then decide (6 ≤ count724 b) else decide (7 ≤ count724 b)) else (if i < 732 then decide (8 ≤ count724 b) else decide (9 ≤ count724 b))))) else (if i < 740 then (if i < 736 then (if i < 734 then decide (10 ≤ count724 b) else (if i < 735 then decide (11 ≤ count724 b) else decide (12 ≤ count724 b))) else (if i < 738 then (if i < 737 then decide (13 ≤ count724 b) else decide (14 ≤ count724 b)) else (if i < 739 then decide (15 ≤ count724 b) else decide (16 ≤ count724 b)))) else (if i < 743 then (if i < 741 then decide (17 ≤ count724 b) else (if i < 742 then decide (18 ≤ count724 b) else decide (19 ≤ count724 b))) else (if i < 745 then (if i < 744 then decide (20 ≤ count724 b) else decide (21 ≤ count724 b)) else (if i < 746 then decide (22 ≤ count724 b) else decide (23 ≤ count724 b)))))))) else (if i < 800 then (if i < 773 then (if i < 760 then (if i < 753 then (if i < 750 then (if i < 748 then decide (24 ≤ count724 b) else (if i < 749 then decide (25 ≤ count724 b) else decide (26 ≤ count724 b))) else (if i < 751 then decide (27 ≤ count724 b) else (if i < 752 then decide (28 ≤ count724 b) else decide (29 ≤ count724 b)))) else (if i < 756 then (if i < 754 then decide (1 ≤ count753 b) else (if i < 755 then decide (2 ≤ count753 b) else decide (3 ≤ count753 b))) else (if i < 758 then (if i < 757 then decide (4 ≤ count753 b) else decide (5 ≤ count753 b)) else (if i < 759 then decide (6 ≤ count753 b) else decide (7 ≤ count753 b))))) else (if i < 766 then (if i < 763 then (if i < 761 then decide (8 ≤ count753 b) else (if i < 762 then decide (9 ≤ count753 b) else decide (10 ≤ count753 b))) else (if i < 764 then decide (11 ≤ count753 b) else (if i < 765 then decide (12 ≤ count753 b) else decide (13 ≤ count753 b)))) else (if i < 769 then (if i < 767 then decide (14 ≤ count753 b) else (if i < 768 then decide (15 ≤ count753 b) else decide (16 ≤ count753 b))) else (if i < 771 then (if i < 770 then decide (17 ≤ count753 b) else decide (18 ≤ count753 b)) else (if i < 772 then decide (19 ≤ count753 b) else decide (20 ≤ count753 b)))))) else (if i < 786 then (if i < 779 then (if i < 776 then (if i < 774 then decide (21 ≤ count753 b) else (if i < 775 then decide (22 ≤ count753 b) else decide (23 ≤ count753 b))) else (if i < 777 then decide (24 ≤ count753 b) else (if i < 778 then decide (25 ≤ count753 b) else decide (26 ≤ count753 b)))) else (if i < 782 then (if i < 780 then decide (27 ≤ count753 b) else (if i < 781 then decide (28 ≤ count753 b) else decide (29 ≤ count753 b))) else (if i < 784 then (if i < 783 then decide (30 ≤ count753 b) else decide (31 ≤ count753 b)) else (if i < 785 then decide (32 ≤ count753 b) else decide (33 ≤ count753 b))))) else (if i < 793 then (if i < 789 then (if i < 787 then decide (34 ≤ count753 b) else (if i < 788 then decide (35 ≤ count753 b) else decide (36 ≤ count753 b))) else (if i < 791 then (if i < 790 then decide (37 ≤ count753 b) else decide (38 ≤ count753 b)) else (if i < 792 then decide (39 ≤ count753 b) else decide (40 ≤ count753 b)))) else (if i < 796 then (if i < 794 then decide (41 ≤ count753 b) else (if i < 795 then decide (42 ≤ count753 b) else decide (1 ≤ count795 b))) else (if i < 798 then (if i < 797 then decide (2 ≤ count795 b) else decide (1 ≤ count797 b)) else (if i < 799 then decide (2 ≤ count797 b) else decide (3 ≤ count797 b))))))) else (if i < 827 then (if i < 813 then (if i < 806 then (if i < 803 then (if i < 801 then decide (1 ≤ count800 b) else (if i < 802 then decide (2 ≤ count800 b) else decide (1 ≤ count802 b))) else (if i < 804 then decide (2 ≤ count802 b) else (if i < 805 then decide (1 ≤ count804 b) else decide (2 ≤ count804 b)))) else (if i < 809 then (if i < 807 then decide (3 ≤ count804 b) else (if i < 808 then decide (4 ≤ count804 b) else decide (1 ≤ count808 b))) else (if i < 811 then (if i < 810 then decide (2 ≤ count808 b) else decide (3 ≤ count808 b)) else (if i < 812 then decide (4 ≤ count808 b) else decide (5 ≤ count808 b))))) else (if i < 820 then (if i < 816 then (if i < 814 then decide (6 ≤ count808 b) else (if i < 815 then decide (7 ≤ count808 b) else decide (1 ≤ count815 b))) else (if i < 818 then (if i < 817 then decide (2 ≤ count815 b) else decide (1 ≤ count817 b)) else (if i < 819 then decide (2 ≤ count817 b) else decide (3 ≤ count817 b)))) else (if i < 823 then (if i < 821 then decide (1 ≤ count820 b) else (if i < 822 then decide (2 ≤ count820 b) else decide (1 ≤ count822 b))) else (if i < 825 then (if i < 824 then decide (2 ≤ count822 b) else decide (1 ≤ count824 b)) else (if i < 826 then decide (2 ≤ count824 b) else decide (3 ≤ count824 b)))))) else (if i < 840 then (if i < 833 then (if i < 830 then (if i < 828 then decide (4 ≤ count824 b) else (if i < 829 then decide (1 ≤ count828 b) else decide (2 ≤ count828 b))) else (if i < 831 then decide (3 ≤ count828 b) else (if i < 832 then decide (4 ≤ count828 b) else decide (5 ≤ count828 b)))) else (if i < 836 then (if i < 834 then decide (6 ≤ count828 b) else (if i < 835 then decide (7 ≤ count828 b) else decide (1 ≤ count835 b))) else (if i < 838 then (if i < 837 then decide (2 ≤ count835 b) else decide (3 ≤ count835 b)) else (if i < 839 then decide (4 ≤ count835 b) else decide (5 ≤ count835 b))))) else (if i < 847 then (if i < 843 then (if i < 841 then decide (6 ≤ count835 b) else (if i < 842 then decide (7 ≤ count835 b) else decide (8 ≤ count835 b))) else (if i < 845 then (if i < 844 then decide (9 ≤ count835 b) else decide (10 ≤ count835 b)) else (if i < 846 then decide (11 ≤ count835 b) else decide (12 ≤ count835 b)))) else (if i < 850 then (if i < 848 then decide (13 ≤ count835 b) else (if i < 849 then decide (14 ≤ count835 b) else decide (1 ≤ count849 b))) else (if i < 852 then (if i < 851 then decide (2 ≤ count849 b) else decide (1 ≤ count851 b)) else (if i < 853 then decide (2 ≤ count851 b) else decide (3 ≤ count851 b))))))))))) else (if i < 1281 then (if i < 1067 then (if i < 960 then (if i < 907 then (if i < 880 then (if i < 867 then (if i < 860 then (if i < 857 then (if i < 855 then decide (1 ≤ count854 b) else (if i < 856 then decide (2 ≤ count854 b) else decide (1 ≤ count856 b))) else (if i < 858 then decide (2 ≤ count856 b) else (if i < 859 then decide (1 ≤ count858 b) else decide (2 ≤ count858 b)))) else (if i < 863 then (if i < 861 then decide (3 ≤ count858 b) else (if i < 862 then decide (4 ≤ count858 b) else decide (1 ≤ count862 b))) else (if i < 865 then (if i < 864 then decide (2 ≤ count862 b) else decide (3 ≤ count862 b)) else (if i < 866 then decide (4 ≤ count862 b) else decide (5 ≤ count862 b))))) else (if i < 873 then (if i < 870 then (if i < 868 then decide (6 ≤ count862 b) else (if i < 869 then decide (7 ≤ count862 b) else decide (1 ≤ count869 b))) else (if i < 871 then decide (2 ≤ count869 b) else (if i < 872 then decide (1 ≤ count871 b) else decide (2 ≤ count871 b)))) else (if i < 876 then (if i < 874 then decide (1 ≤ count873 b) else (if i < 875 then decide (2 ≤ count873 b) else decide (3 ≤ count873 b))) else (if i < 878 then (if i < 877 then decide (4 ≤ count873 b) else decide (1 ≤ count877 b)) else (if i < 879 then decide (2 ≤ count877 b) else decide (1 ≤ count879 b)))))) else (if i < 893 then (if i < 886 then (if i < 883 then (if i < 881 then decide (2 ≤ count879 b) else (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b))) else (if i < 884 then decide (3 ≤ count881 b) else (if i < 885 then decide (4 ≤ count881 b) else decide (1 ≤ count885 b)))) else (if i < 889 then (if i < 887 then decide (2 ≤ count885 b) else (if i < 888 then decide (3 ≤ count885 b) else decide (4 ≤ count885 b))) else (if i < 891 then (if i < 890 then decide (5 ≤ count885 b) else decide (6 ≤ count885 b)) else (if i < 892 then decide (7 ≤ count885 b) else decide (8 ≤ count885 b))))) else (if i < 900 then (if i < 896 then (if i < 894 then decide (1 ≤ count893 b) else (if i < 895 then decide (2 ≤ count893 b) else decide (3 ≤ count893 b))) else (if i < 898 then (if i < 897 then decide (4 ≤ count893 b) else decide (5 ≤ count893 b)) else (if i < 899 then decide (6 ≤ count893 b) else decide (7 ≤ count893 b)))) else (if i < 903 then (if i < 901 then decide (8 ≤ count893 b) else (if i < 902 then decide (9 ≤ count893 b) else decide (10 ≤ count893 b))) else (if i < 905 then (if i < 904 then decide (11 ≤ count893 b) else decide (12 ≤ count893 b)) else (if i < 906 then decide (13 ≤ count893 b) else decide (14 ≤ count893 b))))))) else (if i < 933 then (if i < 920 then (if i < 913 then (if i < 910 then (if i < 908 then decide (15 ≤ count893 b) else (if i < 909 then decide (1 ≤ count908 b) else decide (2 ≤ count908 b))) else (if i < 911 then decide (3 ≤ count908 b) else (if i < 912 then decide (4 ≤ count908 b) else decide (5 ≤ count908 b)))) else (if i < 916 then (if i < 914 then decide (6 ≤ count908 b) else (if i < 915 then decide (7 ≤ count908 b) else decide (8 ≤ count908 b))) else (if i < 918 then (if i < 917 then decide (9 ≤ count908 b) else decide (10 ≤ count908 b)) else (if i < 919 then decide (11 ≤ count908 b) else decide (12 ≤ count908 b))))) else (if i < 926 then (if i < 923 then (if i < 921 then decide (13 ≤ count908 b) else (if i < 922 then decide (14 ≤ count908 b) else decide (15 ≤ count908 b))) else (if i < 924 then decide (16 ≤ count908 b) else (if i < 925 then decide (17 ≤ count908 b) else decide (18 ≤ count908 b)))) else (if i < 929 then (if i < 927 then decide (1 ≤ count926 b) else (if i < 928 then decide (2 ≤ count926 b) else decide (1 ≤ count928 b))) else (if i < 931 then (if i < 930 then decide (2 ≤ count928 b) else decide (3 ≤ count928 b)) else (if i < 932 then decide (1 ≤ count931 b) else decide (2 ≤ count931 b)))))) else (if i < 946 then (if i < 939 then (if i < 936 then (if i < 934 then decide (1 ≤ count933 b) else (if i < 935 then decide (2 ≤ count933 b) else decide (1 ≤ count935 b))) else (if i < 937 then decide (2 ≤ count935 b) else (if i < 938 then decide (3 ≤ count935 b) else decide (4 ≤ count935 b)))) else (if i < 942 then (if i < 940 then decide (1 ≤ count939 b) else (if i < 941 then decide (2 ≤ count939 b) else decide (3 ≤ count939 b))) else (if i < 944 then (if i < 943 then decide (4 ≤ count939 b) else decide (5 ≤ count939 b)) else (if i < 945 then decide (6 ≤ count939 b) else decide (7 ≤ count939 b))))) else (if i < 953 then (if i < 949 then (if i < 947 then decide (1 ≤ count946 b) else (if i < 948 then decide (2 ≤ count946 b) else decide (1 ≤ count948 b))) else (if i < 951 then (if i < 950 then decide (2 ≤ count948 b) else decide (3 ≤ count948 b)) else (if i < 952 then decide (1 ≤ count951 b) else decide (2 ≤ count951 b)))) else (if i < 956 then (if i < 954 then decide (1 ≤ count953 b) else (if i < 955 then decide (2 ≤ count953 b) else decide (1 ≤ count955 b))) else (if i < 958 then (if i < 957 then decide (2 ≤ count955 b) else decide (3 ≤ count955 b)) else (if i < 959 then decide (4 ≤ count955 b) else decide (1 ≤ count959 b)))))))) else (if i < 1013 then (if i < 986 then (if i < 973 then (if i < 966 then (if i < 963 then (if i < 961 then decide (2 ≤ count959 b) else (if i < 962 then decide (3 ≤ count959 b) else decide (4 ≤ count959 b))) else (if i < 964 then decide (5 ≤ count959 b) else (if i < 965 then decide (6 ≤ count959 b) else decide (7 ≤ count959 b)))) else (if i < 969 then (if i < 967 then decide (1 ≤ count966 b) else (if i < 968 then decide (2 ≤ count966 b) else decide (3 ≤ count966 b))) else (if i < 971 then (if i < 970 then decide (4 ≤ count966 b) else decide (5 ≤ count966 b)) else (if i < 972 then decide (6 ≤ count966 b) else decide (7 ≤ count966 b))))) else (if i < 979 then (if i < 976 then (if i < 974 then decide (8 ≤ count966 b) else (if i < 975 then decide (9 ≤ count966 b) else decide (10 ≤ count966 b))) else (if i < 977 then decide (11 ≤ count966 b) else (if i < 978 then decide (12 ≤ count966 b) else decide (13 ≤ count966 b)))) else (if i < 982 then (if i < 980 then decide (14 ≤ count966 b) else (if i < 981 then decide (1 ≤ count980 b) else decide (2 ≤ count980 b))) else (if i < 984 then (if i < 983 then decide (1 ≤ count982 b) else decide (2 ≤ count982 b)) else (if i < 985 then decide (3 ≤ count982 b) else decide (1 ≤ count985 b)))))) else (if i < 999 then (if i < 992 then (if i < 989 then (if i < 987 then decide (2 ≤ count985 b) else (if i < 988 then decide (1 ≤ count987 b) else decide (2 ≤ count987 b))) else (if i < 990 then decide (1 ≤ count989 b) else (if i < 991 then decide (2 ≤ count989 b) else decide (3 ≤ count989 b)))) else (if i < 995 then (if i < 993 then decide (4 ≤ count989 b) else (if i < 994 then decide (1 ≤ count993 b) else decide (2 ≤ count993 b))) else (if i < 997 then (if i < 996 then decide (3 ≤ count993 b) else decide (4 ≤ count993 b)) else (if i < 998 then decide (5 ≤ count993 b) else decide (6 ≤ count993 b))))) else (if i < 1006 then (if i < 1002 then (if i < 1000 then decide (7 ≤ count993 b) else (if i < 1001 then decide (1 ≤ count1000 b) else decide (2 ≤ count1000 b))) else (if i < 1004 then (if i < 1003 then decide (1 ≤ count1002 b) else decide (2 ≤ count1002 b)) else (if i < 1005 then decide (1 ≤ count1004 b) else decide (2 ≤ count1004 b)))) else (if i < 1009 then (if i < 1007 then decide (3 ≤ count1004 b) else (if i < 1008 then decide (4 ≤ count1004 b) else decide (1 ≤ count1008 b))) else (if i < 1011 then (if i < 1010 then decide (2 ≤ count1008 b) else decide (1 ≤ count1010 b)) else (if i < 1012 then decide (2 ≤ count1010 b) else decide (1 ≤ count1012 b))))))) else (if i < 1040 then (if i < 1026 then (if i < 1019 then (if i < 1016 then (if i < 1014 then decide (2 ≤ count1012 b) else (if i < 1015 then decide (3 ≤ count1012 b) else decide (4 ≤ count1012 b))) else (if i < 1017 then decide (1 ≤ count1016 b) else (if i < 1018 then decide (2 ≤ count1016 b) else decide (3 ≤ count1016 b)))) else (if i < 1022 then (if i < 1020 then decide (4 ≤ count1016 b) else (if i < 1021 then decide (5 ≤ count1016 b) else decide (6 ≤ count1016 b))) else (if i < 1024 then (if i < 1023 then decide (7 ≤ count1016 b) else decide (8 ≤ count1016 b)) else (if i < 1025 then decide (1 ≤ count1024 b) else decide (2 ≤ count1024 b))))) else (if i < 1033 then (if i < 1029 then (if i < 1027 then decide (3 ≤ count1024 b) else (if i < 1028 then decide (4 ≤ count1024 b) else decide (5 ≤ count1024 b))) else (if i < 1031 then (if i < 1030 then decide (6 ≤ count1024 b) else decide (7 ≤ count1024 b)) else (if i < 1032 then decide (8 ≤ count1024 b) else decide (9 ≤ count1024 b)))) else (if i < 1036 then (if i < 1034 then decide (10 ≤ count1024 b) else (if i < 1035 then decide (11 ≤ count1024 b) else decide (12 ≤ count1024 b))) else (if i < 1038 then (if i < 1037 then decide (13 ≤ count1024 b) else decide (14 ≤ count1024 b)) else (if i < 1039 then decide (15 ≤ count1024 b) else decide (1 ≤ count1039 b)))))) else (if i < 1053 then (if i < 1046 then (if i < 1043 then (if i < 1041 then decide (2 ≤ count1039 b) else (if i < 1042 then decide (3 ≤ count1039 b) else decide (4 ≤ count1039 b))) else (if i < 1044 then decide (5 ≤ count1039 b) else (if i < 1045 then decide (6 ≤ count1039 b) else decide (7 ≤ count1039 b)))) else (if i < 1049 then (if i < 1047 then decide (8 ≤ count1039 b) else (if i < 1048 then decide (9 ≤ count1039 b) else decide (10 ≤ count1039 b))) else (if i < 1051 then (if i < 1050 then decide (11 ≤ count1039 b) else decide (12 ≤ count1039 b)) else (if i < 1052 then decide (13 ≤ count1039 b) else decide (14 ≤ count1039 b))))) else (if i < 1060 then (if i < 1056 then (if i < 1054 then decide (15 ≤ count1039 b) else (if i < 1055 then decide (16 ≤ count1039 b) else decide (17 ≤ count1039 b))) else (if i < 1058 then (if i < 1057 then decide (18 ≤ count1039 b) else decide (1 ≤ count1057 b)) else (if i < 1059 then decide (2 ≤ count1057 b) else decide (3 ≤ count1057 b)))) else (if i < 1063 then (if i < 1061 then decide (4 ≤ count1057 b) else (if i < 1062 then decide (5 ≤ count1057 b) else decide (6 ≤ count1057 b))) else (if i < 1065 then (if i < 1064 then decide (7 ≤ count1057 b) else decide (8 ≤ count1057 b)) else (if i < 1066 then decide (9 ≤ count1057 b) else decide (10 ≤ count1057 b))))))))) else (if i < 1174 then (if i < 1120 then (if i < 1093 then (if i < 1080 then (if i < 1073 then (if i < 1070 then (if i < 1068 then decide (11 ≤ count1057 b) else (if i < 1069 then decide (12 ≤ count1057 b) else decide (13 ≤ count1057 b))) else (if i < 1071 then decide (14 ≤ count1057 b) else (if i < 1072 then decide (15 ≤ count1057 b) else decide (16 ≤ count1057 b)))) else (if i < 1076 then (if i < 1074 then decide (17 ≤ count1057 b) else (if i < 1075 then decide (18 ≤ count1057 b) else decide (1 ≤ count1075 b))) else (if i < 1078 then (if i < 1077 then decide (2 ≤ count1075 b) else decide (1 ≤ count1077 b)) else (if i < 1079 then decide (2 ≤ count1077 b) else decide (3 ≤ count1077 b))))) else (if i < 1086 then (if i < 1083 then (if i < 1081 then decide (1 ≤ count1080 b) else (if i < 1082 then decide (2 ≤ count1080 b) else decide (1 ≤ count1082 b))) else (if i < 1084 then decide (2 ≤ count1082 b) else (if i < 1085 then decide (1 ≤ count1084 b) else decide (2 ≤ count1084 b)))) else (if i < 1089 then (if i < 1087 then decide (3 ≤ count1084 b) else (if i < 1088 then decide (4 ≤ count1084 b) else decide (1 ≤ count1088 b))) else (if i < 1091 then (if i < 1090 then decide (2 ≤ count1088 b) else decide (3 ≤ count1088 b)) else (if i < 1092 then decide (4 ≤ count1088 b) else decide (5 ≤ count1088 b)))))) else (if i < 1106 then (if i < 1099 then (if i < 1096 then (if i < 1094 then decide (6 ≤ count1088 b) else (if i < 1095 then decide (7 ≤ count1088 b) else decide (1 ≤ count1095 b))) else (if i < 1097 then decide (2 ≤ count1095 b) else (if i < 1098 then decide (1 ≤ count1097 b) else decide (2 ≤ count1097 b)))) else (if i < 1102 then (if i < 1100 then decide (1 ≤ count1099 b) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (3 ≤ count1099 b))) else (if i < 1104 then (if i < 1103 then decide (4 ≤ count1099 b) else decide (1 ≤ count1103 b)) else (if i < 1105 then decide (2 ≤ count1103 b) else decide (1 ≤ count1105 b))))) else (if i < 1113 then (if i < 1109 then (if i < 1107 then decide (2 ≤ count1105 b) else (if i < 1108 then decide (1 ≤ count1107 b) else decide (2 ≤ count1107 b))) else (if i < 1111 then (if i < 1110 then decide (3 ≤ count1107 b) else decide (4 ≤ count1107 b)) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b)))) else (if i < 1116 then (if i < 1114 then decide (3 ≤ count1111 b) else (if i < 1115 then decide (4 ≤ count1111 b) else decide (5 ≤ count1111 b))) else (if i < 1118 then (if i < 1117 then decide (6 ≤ count1111 b) else decide (7 ≤ count1111 b)) else (if i < 1119 then decide (8 ≤ count1111 b) else decide (1 ≤ count1119 b))))))) else (if i < 1147 then (if i < 1133 then (if i < 1126 then (if i < 1123 then (if i < 1121 then decide (2 ≤ count1119 b) else (if i < 1122 then decide (3 ≤ count1119 b) else decide (4 ≤ count1119 b))) else (if i < 1124 then decide (5 ≤ count1119 b) else (if i < 1125 then decide (6 ≤ count1119 b) else decide (7 ≤ count1119 b)))) else (if i < 1129 then (if i < 1127 then decide (8 ≤ count1119 b) else (if i < 1128 then decide (9 ≤ count1119 b) else decide (10 ≤ count1119 b))) else (if i < 1131 then (if i < 1130 then decide (11 ≤ count1119 b) else decide (12 ≤ count1119 b)) else (if i < 1132 then decide (13 ≤ count1119 b) else decide (14 ≤ count1119 b))))) else (if i < 1140 then (if i < 1136 then (if i < 1134 then decide (15 ≤ count1119 b) else (if i < 1135 then decide (1 ≤ count1134 b) else decide (2 ≤ count1134 b))) else (if i < 1138 then (if i < 1137 then decide (1 ≤ count1136 b) else decide (2 ≤ count1136 b)) else (if i < 1139 then decide (3 ≤ count1136 b) else decide (1 ≤ count1139 b)))) else (if i < 1143 then (if i < 1141 then decide (2 ≤ count1139 b) else (if i < 1142 then decide (1 ≤ count1141 b) else decide (2 ≤ count1141 b))) else (if i < 1145 then (if i < 1144 then decide (1 ≤ count1143 b) else decide (2 ≤ count1143 b)) else (if i < 1146 then decide (3 ≤ count1143 b) else decide (4 ≤ count1143 b)))))) else (if i < 1160 then (if i < 1153 then (if i < 1150 then (if i < 1148 then decide (1 ≤ count1147 b) else (if i < 1149 then decide (2 ≤ count1147 b) else decide (3 ≤ count1147 b))) else (if i < 1151 then decide (4 ≤ count1147 b) else (if i < 1152 then decide (5 ≤ count1147 b) else decide (6 ≤ count1147 b)))) else (if i < 1156 then (if i < 1154 then decide (7 ≤ count1147 b) else (if i < 1155 then decide (1 ≤ count1154 b) else decide (2 ≤ count1154 b))) else (if i < 1158 then (if i < 1157 then decide (1 ≤ count1156 b) else decide (2 ≤ count1156 b)) else (if i < 1159 then decide (1 ≤ count1158 b) else decide (2 ≤ count1158 b))))) else (if i < 1167 then (if i < 1163 then (if i < 1161 then decide (3 ≤ count1158 b) else (if i < 1162 then decide (4 ≤ count1158 b) else decide (1 ≤ count1162 b))) else (if i < 1165 then (if i < 1164 then decide (2 ≤ count1162 b) else decide (1 ≤ count1164 b)) else (if i < 1166 then decide (2 ≤ count1164 b) else decide (1 ≤ count1166 b)))) else (if i < 1170 then (if i < 1168 then decide (2 ≤ count1166 b) else (if i < 1169 then decide (3 ≤ count1166 b) else decide (4 ≤ count1166 b))) else (if i < 1172 then (if i < 1171 then decide (1 ≤ count1170 b) else decide (2 ≤ count1170 b)) else (if i < 1173 then decide (3 ≤ count1170 b) else decide (4 ≤ count1170 b)))))))) else (if i < 1227 then (if i < 1200 then (if i < 1187 then (if i < 1180 then (if i < 1177 then (if i < 1175 then decide (5 ≤ count1170 b) else (if i < 1176 then decide (6 ≤ count1170 b) else decide (7 ≤ count1170 b))) else (if i < 1178 then decide (8 ≤ count1170 b) else (if i < 1179 then decide (1 ≤ count1178 b) else decide (2 ≤ count1178 b)))) else (if i < 1183 then (if i < 1181 then decide (3 ≤ count1178 b) else (if i < 1182 then decide (4 ≤ count1178 b) else decide (5 ≤ count1178 b))) else (if i < 1185 then (if i < 1184 then decide (6 ≤ count1178 b) else decide (7 ≤ count1178 b)) else (if i < 1186 then decide (8 ≤ count1178 b) else decide (9 ≤ count1178 b))))) else (if i < 1193 then (if i < 1190 then (if i < 1188 then decide (10 ≤ count1178 b) else (if i < 1189 then decide (11 ≤ count1178 b) else decide (12 ≤ count1178 b))) else (if i < 1191 then decide (13 ≤ count1178 b) else (if i < 1192 then decide (14 ≤ count1178 b) else decide (15 ≤ count1178 b)))) else (if i < 1196 then (if i < 1194 then decide (1 ≤ count1193 b) else (if i < 1195 then decide (2 ≤ count1193 b) else decide (3 ≤ count1193 b))) else (if i < 1198 then (if i < 1197 then decide (4 ≤ count1193 b) else decide (5 ≤ count1193 b)) else (if i < 1199 then decide (6 ≤ count1193 b) else decide (7 ≤ count1193 b)))))) else (if i < 1213 then (if i < 1206 then (if i < 1203 then (if i < 1201 then decide (8 ≤ count1193 b) else (if i < 1202 then decide (9 ≤ count1193 b) else decide (10 ≤ count1193 b))) else (if i < 1204 then decide (11 ≤ count1193 b) else (if i < 1205 then decide (12 ≤ count1193 b) else decide (13 ≤ count1193 b)))) else (if i < 1209 then (if i < 1207 then decide (14 ≤ count1193 b) else (if i < 1208 then decide (15 ≤ count1193 b) else decide (16 ≤ count1193 b))) else (if i < 1211 then (if i < 1210 then decide (17 ≤ count1193 b) else decide (18 ≤ count1193 b)) else (if i < 1212 then decide (19 ≤ count1193 b) else decide (20 ≤ count1193 b))))) else (if i < 1220 then (if i < 1216 then (if i < 1214 then decide (21 ≤ count1193 b) else (if i < 1215 then decide (22 ≤ count1193 b) else decide (23 ≤ count1193 b))) else (if i < 1218 then (if i < 1217 then decide (24 ≤ count1193 b) else decide (25 ≤ count1193 b)) else (if i < 1219 then decide (26 ≤ count1193 b) else decide (27 ≤ count1193 b)))) else (if i < 1223 then (if i < 1221 then decide (28 ≤ count1193 b) else (if i < 1222 then decide (29 ≤ count1193 b) else decide (30 ≤ count1193 b))) else (if i < 1225 then (if i < 1224 then decide (1 ≤ count1223 b) else decide (2 ≤ count1223 b)) else (if i < 1226 then decide (1 ≤ count1225 b) else decide (2 ≤ count1225 b))))))) else (if i < 1254 then (if i < 1240 then (if i < 1233 then (if i < 1230 then (if i < 1228 then decide (3 ≤ count1225 b) else (if i < 1229 then decide (1 ≤ count1228 b) else decide (2 ≤ count1228 b))) else (if i < 1231 then decide (1 ≤ count1230 b) else (if i < 1232 then decide (2 ≤ count1230 b) else decide (1 ≤ count1232 b)))) else (if i < 1236 then (if i < 1234 then decide (2 ≤ count1232 b) else (if i < 1235 then decide (3 ≤ count1232 b) else decide (4 ≤ count1232 b))) else (if i < 1238 then (if i < 1237 then decide (1 ≤ count1236 b) else decide (2 ≤ count1236 b)) else (if i < 1239 then decide (3 ≤ count1236 b) else decide (4 ≤ count1236 b))))) else (if i < 1247 then (if i < 1243 then (if i < 1241 then decide (5 ≤ count1236 b) else (if i < 1242 then decide (6 ≤ count1236 b) else decide (7 ≤ count1236 b))) else (if i < 1245 then (if i < 1244 then decide (1 ≤ count1243 b) else decide (2 ≤ count1243 b)) else (if i < 1246 then decide (1 ≤ count1245 b) else decide (2 ≤ count1245 b)))) else (if i < 1250 then (if i < 1248 then decide (1 ≤ count1247 b) else (if i < 1249 then decide (2 ≤ count1247 b) else decide (3 ≤ count1247 b))) else (if i < 1252 then (if i < 1251 then decide (4 ≤ count1247 b) else decide (1 ≤ count1251 b)) else (if i < 1253 then decide (2 ≤ count1251 b) else decide (1 ≤ count1253 b)))))) else (if i < 1267 then (if i < 1260 then (if i < 1257 then (if i < 1255 then decide (2 ≤ count1253 b) else (if i < 1256 then decide (1 ≤ count1255 b) else decide (2 ≤ count1255 b))) else (if i < 1258 then decide (3 ≤ count1255 b) else (if i < 1259 then decide (4 ≤ count1255 b) else decide (1 ≤ count1259 b)))) else (if i < 1263 then (if i < 1261 then decide (2 ≤ count1259 b) else (if i < 1262 then decide (3 ≤ count1259 b) else decide (4 ≤ count1259 b))) else (if i < 1265 then (if i < 1264 then decide (5 ≤ count1259 b) else decide (6 ≤ count1259 b)) else (if i < 1266 then decide (7 ≤ count1259 b) else decide (8 ≤ count1259 b))))) else (if i < 1274 then (if i < 1270 then (if i < 1268 then decide (1 ≤ count1267 b) else (if i < 1269 then decide (2 ≤ count1267 b) else decide (3 ≤ count1267 b))) else (if i < 1272 then (if i < 1271 then decide (4 ≤ count1267 b) else decide (5 ≤ count1267 b)) else (if i < 1273 then decide (6 ≤ count1267 b) else decide (7 ≤ count1267 b)))) else (if i < 1277 then (if i < 1275 then decide (8 ≤ count1267 b) else (if i < 1276 then decide (9 ≤ count1267 b) else decide (10 ≤ count1267 b))) else (if i < 1279 then (if i < 1278 then decide (11 ≤ count1267 b) else decide (12 ≤ count1267 b)) else (if i < 1280 then decide (13 ≤ count1267 b) else decide (14 ≤ count1267 b)))))))))) else (if i < 1495 then (if i < 1388 then (if i < 1334 then (if i < 1307 then (if i < 1294 then (if i < 1287 then (if i < 1284 then (if i < 1282 then decide (15 ≤ count1267 b) else (if i < 1283 then decide (1 ≤ count1282 b) else decide (2 ≤ count1282 b))) else (if i < 1285 then decide (1 ≤ count1284 b) else (if i < 1286 then decide (2 ≤ count1284 b) else decide (3 ≤ count1284 b)))) else (if i < 1290 then (if i < 1288 then decide (1 ≤ count1287 b) else (if i < 1289 then decide (2 ≤ count1287 b) else decide (1 ≤ count1289 b))) else (if i < 1292 then (if i < 1291 then decide (2 ≤ count1289 b) else decide (1 ≤ count1291 b)) else (if i < 1293 then decide (2 ≤ count1291 b) else decide (3 ≤ count1291 b))))) else (if i < 1300 then (if i < 1297 then (if i < 1295 then decide (4 ≤ count1291 b) else (if i < 1296 then decide (1 ≤ count1295 b) else decide (2 ≤ count1295 b))) else (if i < 1298 then decide (3 ≤ count1295 b) else (if i < 1299 then decide (4 ≤ count1295 b) else decide (5 ≤ count1295 b)))) else (if i < 1303 then (if i < 1301 then decide (6 ≤ count1295 b) else (if i < 1302 then decide (7 ≤ count1295 b) else decide (1 ≤ count1302 b))) else (if i < 1305 then (if i < 1304 then decide (2 ≤ count1302 b) else decide (1 ≤ count1304 b)) else (if i < 1306 then decide (2 ≤ count1304 b) else decide (1 ≤ count1306 b)))))) else (if i < 1320 then (if i < 1313 then (if i < 1310 then (if i < 1308 then decide (2 ≤ count1306 b) else (if i < 1309 then decide (3 ≤ count1306 b) else decide (4 ≤ count1306 b))) else (if i < 1311 then decide (1 ≤ count1310 b) else (if i < 1312 then decide (2 ≤ count1310 b) else decide (1 ≤ count1312 b)))) else (if i < 1316 then (if i < 1314 then decide (2 ≤ count1312 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))) else (if i < 1318 then (if i < 1317 then decide (3 ≤ count1314 b) else decide (4 ≤ count1314 b)) else (if i < 1319 then decide (1 ≤ count1318 b) else decide (2 ≤ count1318 b))))) else (if i < 1327 then (if i < 1323 then (if i < 1321 then decide (3 ≤ count1318 b) else (if i < 1322 then decide (4 ≤ count1318 b) else decide (5 ≤ count1318 b))) else (if i < 1325 then (if i < 1324 then decide (6 ≤ count1318 b) else decide (7 ≤ count1318 b)) else (if i < 1326 then decide (8 ≤ count1318 b) else decide (1 ≤ count1326 b)))) else (if i < 1330 then (if i < 1328 then decide (2 ≤ count1326 b) else (if i < 1329 then decide (3 ≤ count1326 b) else decide (4 ≤ count1326 b))) else (if i < 1332 then (if i < 1331 then decide (5 ≤ count1326 b) else decide (6 ≤ count1326 b)) else (if i < 1333 then decide (7 ≤ count1326 b) else decide (8 ≤ count1326 b))))))) else (if i < 1361 then (if i < 1347 then (if i < 1340 then (if i < 1337 then (if i < 1335 then decide (9 ≤ count1326 b) else (if i < 1336 then decide (10 ≤ count1326 b) else decide (11 ≤ count1326 b))) else (if i < 1338 then decide (12 ≤ count1326 b) else (if i < 1339 then decide (13 ≤ count1326 b) else decide (14 ≤ count1326 b)))) else (if i < 1343 then (if i < 1341 then decide (15 ≤ count1326 b) else (if i < 1342 then decide (1 ≤ count1341 b) else decide (2 ≤ count1341 b))) else (if i < 1345 then (if i < 1344 then decide (3 ≤ count1341 b) else decide (4 ≤ count1341 b)) else (if i < 1346 then decide (5 ≤ count1341 b) else decide (6 ≤ count1341 b))))) else (if i < 1354 then (if i < 1350 then (if i < 1348 then decide (7 ≤ count1341 b) else (if i < 1349 then decide (8 ≤ count1341 b) else decide (9 ≤ count1341 b))) else (if i < 1352 then (if i < 1351 then decide (10 ≤ count1341 b) else decide (11 ≤ count1341 b)) else (if i < 1353 then decide (12 ≤ count1341 b) else decide (13 ≤ count1341 b)))) else (if i < 1357 then (if i < 1355 then decide (14 ≤ count1341 b) else (if i < 1356 then decide (15 ≤ count1341 b) else decide (16 ≤ count1341 b))) else (if i < 1359 then (if i < 1358 then decide (17 ≤ count1341 b) else decide (18 ≤ count1341 b)) else (if i < 1360 then decide (19 ≤ count1341 b) else decide (20 ≤ count1341 b)))))) else (if i < 1374 then (if i < 1367 then (if i < 1364 then (if i < 1362 then decide (21 ≤ count1341 b) else (if i < 1363 then decide (22 ≤ count1341 b) else decide (23 ≤ count1341 b))) else (if i < 1365 then decide (24 ≤ count1341 b) else (if i < 1366 then decide (25 ≤ count1341 b) else decide (26 ≤ count1341 b)))) else (if i < 1370 then (if i < 1368 then decide (27 ≤ count1341 b) else (if i < 1369 then decide (28 ≤ count1341 b) else decide (29 ≤ count1341 b))) else (if i < 1372 then (if i < 1371 then decide (30 ≤ count1341 b) else decide (1 ≤ count1371 b)) else (if i < 1373 then decide (2 ≤ count1371 b) else decide (3 ≤ count1371 b))))) else (if i < 1381 then (if i < 1377 then (if i < 1375 then decide (4 ≤ count1371 b) else (if i < 1376 then decide (5 ≤ count1371 b) else decide (6 ≤ count1371 b))) else (if i < 1379 then (if i < 1378 then decide (7 ≤ count1371 b) else decide (8 ≤ count1371 b)) else (if i < 1380 then decide (9 ≤ count1371 b) else decide (10 ≤ count1371 b)))) else (if i < 1384 then (if i < 1382 then decide (11 ≤ count1371 b) else (if i < 1383 then decide (12 ≤ count1371 b) else decide (13 ≤ count1371 b))) else (if i < 1386 then (if i < 1385 then decide (14 ≤ count1371 b) else decide (15 ≤ count1371 b)) else (if i < 1387 then decide (16 ≤ count1371 b) else decide (17 ≤ count1371 b)))))))) else (if i < 1441 then (if i < 1414 then (if i < 1401 then (if i < 1394 then (if i < 1391 then (if i < 1389 then decide (18 ≤ count1371 b) else (if i < 1390 then decide (19 ≤ count1371 b) else decide (20 ≤ count1371 b))) else (if i < 1392 then decide (21 ≤ count1371 b) else (if i < 1393 then decide (22 ≤ count1371 b) else decide (23 ≤ count1371 b)))) else (if i < 1397 then (if i < 1395 then decide (24 ≤ count1371 b) else (if i < 1396 then decide (25 ≤ count1371 b) else decide (26 ≤ count1371 b))) else (if i < 1399 then (if i < 1398 then decide (27 ≤ count1371 b) else decide (28 ≤ count1371 b)) else (if i < 1400 then decide (29 ≤ count1371 b) else decide (30 ≤ count1371 b))))) else (if i < 1407 then (if i < 1404 then (if i < 1402 then decide (31 ≤ count1371 b) else (if i < 1403 then decide (32 ≤ count1371 b) else decide (33 ≤ count1371 b))) else (if i < 1405 then decide (34 ≤ count1371 b) else (if i < 1406 then decide (35 ≤ count1371 b) else decide (36 ≤ count1371 b)))) else (if i < 1410 then (if i < 1408 then decide (37 ≤ count1371 b) else (if i < 1409 then decide (38 ≤ count1371 b) else decide (39 ≤ count1371 b))) else (if i < 1412 then (if i < 1411 then decide (40 ≤ count1371 b) else decide (41 ≤ count1371 b)) else (if i < 1413 then decide (42 ≤ count1371 b) else decide (1 ≤ count1413 b)))))) else (if i < 1427 then (if i < 1420 then (if i < 1417 then (if i < 1415 then decide (2 ≤ count1413 b) else (if i < 1416 then decide (1 ≤ count1415 b) else decide (2 ≤ count1415 b))) else (if i < 1418 then decide (3 ≤ count1415 b) else (if i < 1419 then decide (1 ≤ count1418 b) else decide (2 ≤ count1418 b)))) else (if i < 1423 then (if i < 1421 then decide (1 ≤ count1420 b) else (if i < 1422 then decide (2 ≤ count1420 b) else decide (1 ≤ count1422 b))) else (if i < 1425 then (if i < 1424 then decide (2 ≤ count1422 b) else decide (3 ≤ count1422 b)) else (if i < 1426 then decide (4 ≤ count1422 b) else decide (1 ≤ count1426 b))))) else (if i < 1434 then (if i < 1430 then (if i < 1428 then decide (2 ≤ count1426 b) else (if i < 1429 then decide (3 ≤ count1426 b) else decide (4 ≤ count1426 b))) else (if i < 1432 then (if i < 1431 then decide (5 ≤ count1426 b) else decide (6 ≤ count1426 b)) else (if i < 1433 then decide (7 ≤ count1426 b) else decide (1 ≤ count1433 b)))) else (if i < 1437 then (if i < 1435 then decide (2 ≤ count1433 b) else (if i < 1436 then decide (1 ≤ count1435 b) else decide (2 ≤ count1435 b))) else (if i < 1439 then (if i < 1438 then decide (1 ≤ count1437 b) else decide (2 ≤ count1437 b)) else (if i < 1440 then decide (3 ≤ count1437 b) else decide (4 ≤ count1437 b))))))) else (if i < 1468 then (if i < 1454 then (if i < 1447 then (if i < 1444 then (if i < 1442 then decide (1 ≤ count1441 b) else (if i < 1443 then decide (2 ≤ count1441 b) else decide (1 ≤ count1443 b))) else (if i < 1445 then decide (2 ≤ count1443 b) else (if i < 1446 then decide (1 ≤ count1445 b) else decide (2 ≤ count1445 b)))) else (if i < 1450 then (if i < 1448 then decide (3 ≤ count1445 b) else (if i < 1449 then decide (4 ≤ count1445 b) else decide (1 ≤ count1449 b))) else (if i < 1452 then (if i < 1451 then decide (2 ≤ count1449 b) else decide (3 ≤ count1449 b)) else (if i < 1453 then decide (4 ≤ count1449 b) else decide (5 ≤ count1449 b))))) else (if i < 1461 then (if i < 1457 then (if i < 1455 then decide (6 ≤ count1449 b) else (if i < 1456 then decide (7 ≤ count1449 b) else decide (8 ≤ count1449 b))) else (if i < 1459 then (if i < 1458 then decide (1 ≤ count1457 b) else decide (2 ≤ count1457 b)) else (if i < 1460 then decide (3 ≤ count1457 b) else decide (4 ≤ count1457 b)))) else (if i < 1464 then (if i < 1462 then decide (5 ≤ count1457 b) else (if i < 1463 then decide (6 ≤ count1457 b) else decide (7 ≤ count1457 b))) else (if i < 1466 then (if i < 1465 then decide (8 ≤ count1457 b) else decide (9 ≤ count1457 b)) else (if i < 1467 then decide (10 ≤ count1457 b) else decide (11 ≤ count1457 b)))))) else (if i < 1481 then (if i < 1474 then (if i < 1471 then (if i < 1469 then decide (12 ≤ count1457 b) else (if i < 1470 then decide (13 ≤ count1457 b) else decide (14 ≤ count1457 b))) else (if i < 1472 then decide (15 ≤ count1457 b) else (if i < 1473 then decide (1 ≤ count1472 b) else decide (2 ≤ count1472 b)))) else (if i < 1477 then (if i < 1475 then decide (1 ≤ count1474 b) else (if i < 1476 then decide (2 ≤ count1474 b) else decide (3 ≤ count1474 b))) else (if i < 1479 then (if i < 1478 then decide (1 ≤ count1477 b) else decide (2 ≤ count1477 b)) else (if i < 1480 then decide (1 ≤ count1479 b) else decide (2 ≤ count1479 b))))) else (if i < 1488 then (if i < 1484 then (if i < 1482 then decide (1 ≤ count1481 b) else (if i < 1483 then decide (2 ≤ count1481 b) else decide (3 ≤ count1481 b))) else (if i < 1486 then (if i < 1485 then decide (4 ≤ count1481 b) else decide (1 ≤ count1485 b)) else (if i < 1487 then decide (2 ≤ count1485 b) else decide (3 ≤ count1485 b)))) else (if i < 1491 then (if i < 1489 then decide (4 ≤ count1485 b) else (if i < 1490 then decide (5 ≤ count1485 b) else decide (6 ≤ count1485 b))) else (if i < 1493 then (if i < 1492 then decide (7 ≤ count1485 b) else decide (1 ≤ count1492 b)) else (if i < 1494 then decide (2 ≤ count1492 b) else decide (1 ≤ count1494 b))))))))) else (if i < 1602 then (if i < 1548 then (if i < 1521 then (if i < 1508 then (if i < 1501 then (if i < 1498 then (if i < 1496 then decide (2 ≤ count1494 b) else (if i < 1497 then decide (1 ≤ count1496 b) else decide (2 ≤ count1496 b))) else (if i < 1499 then decide (3 ≤ count1496 b) else (if i < 1500 then decide (4 ≤ count1496 b) else decide (1 ≤ count1500 b)))) else (if i < 1504 then (if i < 1502 then decide (2 ≤ count1500 b) else (if i < 1503 then decide (1 ≤ count1502 b) else decide (2 ≤ count1502 b))) else (if i < 1506 then (if i < 1505 then decide (1 ≤ count1504 b) else decide (2 ≤ count1504 b)) else (if i < 1507 then decide (3 ≤ count1504 b) else decide (4 ≤ count1504 b))))) else (if i < 1514 then (if i < 1511 then (if i < 1509 then decide (1 ≤ count1508 b) else (if i < 1510 then decide (2 ≤ count1508 b) else decide (3 ≤ count1508 b))) else (if i < 1512 then decide (4 ≤ count1508 b) else (if i < 1513 then decide (5 ≤ count1508 b) else decide (6 ≤ count1508 b)))) else (if i < 1517 then (if i < 1515 then decide (7 ≤ count1508 b) else (if i < 1516 then decide (8 ≤ count1508 b) else decide (1 ≤ count1516 b))) else (if i < 1519 then (if i < 1518 then decide (2 ≤ count1516 b) else decide (3 ≤ count1516 b)) else (if i < 1520 then decide (4 ≤ count1516 b) else decide (5 ≤ count1516 b)))))) else (if i < 1534 then (if i < 1527 then (if i < 1524 then (if i < 1522 then decide (6 ≤ count1516 b) else (if i < 1523 then decide (7 ≤ count1516 b) else decide (8 ≤ count1516 b))) else (if i < 1525 then decide (9 ≤ count1516 b) else (if i < 1526 then decide (10 ≤ count1516 b) else decide (11 ≤ count1516 b)))) else (if i < 1530 then (if i < 1528 then decide (12 ≤ count1516 b) else (if i < 1529 then decide (13 ≤ count1516 b) else decide (14 ≤ count1516 b))) else (if i < 1532 then (if i < 1531 then decide (15 ≤ count1516 b) else decide (1 ≤ count1531 b)) else (if i < 1533 then decide (2 ≤ count1531 b) else decide (3 ≤ count1531 b))))) else (if i < 1541 then (if i < 1537 then (if i < 1535 then decide (4 ≤ count1531 b) else (if i < 1536 then decide (5 ≤ count1531 b) else decide (6 ≤ count1531 b))) else (if i < 1539 then (if i < 1538 then decide (7 ≤ count1531 b) else decide (8 ≤ count1531 b)) else (if i < 1540 then decide (9 ≤ count1531 b) else decide (10 ≤ count1531 b)))) else (if i < 1544 then (if i < 1542 then decide (11 ≤ count1531 b) else (if i < 1543 then decide (12 ≤ count1531 b) else decide (13 ≤ count1531 b))) else (if i < 1546 then (if i < 1545 then decide (14 ≤ count1531 b) else decide (15 ≤ count1531 b)) else (if i < 1547 then decide (16 ≤ count1531 b) else decide (17 ≤ count1531 b))))))) else (if i < 1575 then (if i < 1561 then (if i < 1554 then (if i < 1551 then (if i < 1549 then decide (18 ≤ count1531 b) else (if i < 1550 then decide (19 ≤ count1531 b) else decide (20 ≤ count1531 b))) else (if i < 1552 then decide (1 ≤ count1551 b) else (if i < 1553 then decide (2 ≤ count1551 b) else decide (1 ≤ count1553 b)))) else (if i < 1557 then (if i < 1555 then decide (2 ≤ count1553 b) else (if i < 1556 then decide (3 ≤ count1553 b) else decide (1 ≤ count1556 b))) else (if i < 1559 then (if i < 1558 then decide (2 ≤ count1556 b) else decide (1 ≤ count1558 b)) else (if i < 1560 then decide (2 ≤ count1558 b) else decide (1 ≤ count1560 b))))) else (if i < 1568 then (if i < 1564 then (if i < 1562 then decide (2 ≤ count1560 b) else (if i < 1563 then decide (3 ≤ count1560 b) else decide (4 ≤ count1560 b))) else (if i < 1566 then (if i < 1565 then decide (1 ≤ count1564 b) else decide (2 ≤ count1564 b)) else (if i < 1567 then decide (3 ≤ count1564 b) else decide (4 ≤ count1564 b)))) else (if i < 1571 then (if i < 1569 then decide (5 ≤ count1564 b) else (if i < 1570 then decide (6 ≤ count1564 b) else decide (7 ≤ count1564 b))) else (if i < 1573 then (if i < 1572 then decide (1 ≤ count1571 b) else decide (2 ≤ count1571 b)) else (if i < 1574 then decide (1 ≤ count1573 b) else decide (2 ≤ count1573 b)))))) else (if i < 1588 then (if i < 1581 then (if i < 1578 then (if i < 1576 then decide (1 ≤ count1575 b) else (if i < 1577 then decide (2 ≤ count1575 b) else decide (3 ≤ count1575 b))) else (if i < 1579 then decide (4 ≤ count1575 b) else (if i < 1580 then decide (1 ≤ count1579 b) else decide (2 ≤ count1579 b)))) else (if i < 1584 then (if i < 1582 then decide (1 ≤ count1581 b) else (if i < 1583 then decide (2 ≤ count1581 b) else decide (1 ≤ count1583 b))) else (if i < 1586 then (if i < 1585 then decide (2 ≤ count1583 b) else decide (3 ≤ count1583 b)) else (if i < 1587 then decide (4 ≤ count1583 b) else decide (1 ≤ count1587 b))))) else (if i < 1595 then (if i < 1591 then (if i < 1589 then decide (2 ≤ count1587 b) else (if i < 1590 then decide (3 ≤ count1587 b) else decide (4 ≤ count1587 b))) else (if i < 1593 then (if i < 1592 then decide (5 ≤ count1587 b) else decide (6 ≤ count1587 b)) else (if i < 1594 then decide (7 ≤ count1587 b) else decide (8 ≤ count1587 b)))) else (if i < 1598 then (if i < 1596 then decide (1 ≤ count1595 b) else (if i < 1597 then decide (2 ≤ count1595 b) else decide (3 ≤ count1595 b))) else (if i < 1600 then (if i < 1599 then decide (4 ≤ count1595 b) else decide (5 ≤ count1595 b)) else (if i < 1601 then decide (6 ≤ count1595 b) else decide (7 ≤ count1595 b)))))))) else (if i < 1655 then (if i < 1628 then (if i < 1615 then (if i < 1608 then (if i < 1605 then (if i < 1603 then decide (8 ≤ count1595 b) else (if i < 1604 then decide (9 ≤ count1595 b) else decide (10 ≤ count1595 b))) else (if i < 1606 then decide (11 ≤ count1595 b) else (if i < 1607 then decide (12 ≤ count1595 b) else decide (13 ≤ count1595 b)))) else (if i < 1611 then (if i < 1609 then decide (14 ≤ count1595 b) else (if i < 1610 then decide (15 ≤ count1595 b) else decide (1 ≤ count1610 b))) else (if i < 1613 then (if i < 1612 then decide (2 ≤ count1610 b) else decide (1 ≤ count1612 b)) else (if i < 1614 then decide (2 ≤ count1612 b) else decide (3 ≤ count1612 b))))) else (if i < 1621 then (if i < 1618 then (if i < 1616 then decide (1 ≤ count1615 b) else (if i < 1617 then decide (2 ≤ count1615 b) else decide (1 ≤ count1617 b))) else (if i < 1619 then decide (2 ≤ count1617 b) else (if i < 1620 then decide (1 ≤ count1619 b) else decide (2 ≤ count1619 b)))) else (if i < 1624 then (if i < 1622 then decide (3 ≤ count1619 b) else (if i < 1623 then decide (4 ≤ count1619 b) else decide (1 ≤ count1623 b))) else (if i < 1626 then (if i < 1625 then decide (2 ≤ count1623 b) else decide (3 ≤ count1623 b)) else (if i < 1627 then decide (4 ≤ count1623 b) else decide (5 ≤ count1623 b)))))) else (if i < 1641 then (if i < 1634 then (if i < 1631 then (if i < 1629 then decide (6 ≤ count1623 b) else (if i < 1630 then decide (7 ≤ count1623 b) else decide (1 ≤ count1630 b))) else (if i < 1632 then decide (2 ≤ count1630 b) else (if i < 1633 then decide (1 ≤ count1632 b) else decide (2 ≤ count1632 b)))) else (if i < 1637 then (if i < 1635 then decide (1 ≤ count1634 b) else (if i < 1636 then decide (2 ≤ count1634 b) else decide (3 ≤ count1634 b))) else (if i < 1639 then (if i < 1638 then decide (4 ≤ count1634 b) else decide (1 ≤ count1638 b)) else (if i < 1640 then decide (2 ≤ count1638 b) else decide (1 ≤ count1640 b))))) else (if i < 1648 then (if i < 1644 then (if i < 1642 then decide (2 ≤ count1640 b) else (if i < 1643 then decide (1 ≤ count1642 b) else decide (2 ≤ count1642 b))) else (if i < 1646 then (if i < 1645 then decide (3 ≤ count1642 b) else decide (4 ≤ count1642 b)) else (if i < 1647 then decide (1 ≤ count1646 b) else decide (2 ≤ count1646 b)))) else (if i < 1651 then (if i < 1649 then decide (3 ≤ count1646 b) else (if i < 1650 then decide (4 ≤ count1646 b) else decide (5 ≤ count1646 b))) else (if i < 1653 then (if i < 1652 then decide (6 ≤ count1646 b) else decide (7 ≤ count1646 b)) else (if i < 1654 then decide (8 ≤ count1646 b) else decide (1 ≤ count1654 b))))))) else (if i < 1682 then (if i < 1668 then (if i < 1661 then (if i < 1658 then (if i < 1656 then decide (2 ≤ count1654 b) else (if i < 1657 then decide (3 ≤ count1654 b) else decide (4 ≤ count1654 b))) else (if i < 1659 then decide (5 ≤ count1654 b) else (if i < 1660 then decide (6 ≤ count1654 b) else decide (7 ≤ count1654 b)))) else (if i < 1664 then (if i < 1662 then decide (8 ≤ count1654 b) else (if i < 1663 then decide (9 ≤ count1654 b) else decide (10 ≤ count1654 b))) else (if i < 1666 then (if i < 1665 then decide (11 ≤ count1654 b) else decide (12 ≤ count1654 b)) else (if i < 1667 then decide (13 ≤ count1654 b) else decide (14 ≤ count1654 b))))) else (if i < 1675 then (if i < 1671 then (if i < 1669 then decide (15 ≤ count1654 b) else (if i < 1670 then decide (1 ≤ count1669 b) else decide (2 ≤ count1669 b))) else (if i < 1673 then (if i < 1672 then decide (3 ≤ count1669 b) else decide (4 ≤ count1669 b)) else (if i < 1674 then decide (5 ≤ count1669 b) else decide (6 ≤ count1669 b)))) else (if i < 1678 then (if i < 1676 then decide (7 ≤ count1669 b) else (if i < 1677 then decide (8 ≤ count1669 b) else decide (9 ≤ count1669 b))) else (if i < 1680 then (if i < 1679 then decide (10 ≤ count1669 b) else decide (11 ≤ count1669 b)) else (if i < 1681 then decide (12 ≤ count1669 b) else decide (13 ≤ count1669 b)))))) else (if i < 1695 then (if i < 1688 then (if i < 1685 then (if i < 1683 then decide (14 ≤ count1669 b) else (if i < 1684 then decide (15 ≤ count1669 b) else decide (16 ≤ count1669 b))) else (if i < 1686 then decide (17 ≤ count1669 b) else (if i < 1687 then decide (18 ≤ count1669 b) else decide (19 ≤ count1669 b)))) else (if i < 1691 then (if i < 1689 then decide (20 ≤ count1669 b) else (if i < 1690 then decide (1 ≤ count1689 b) else decide (2 ≤ count1689 b))) else (if i < 1693 then (if i < 1692 then decide (3 ≤ count1689 b) else decide (4 ≤ count1689 b)) else (if i < 1694 then decide (5 ≤ count1689 b) else decide (6 ≤ count1689 b))))) else (if i < 1702 then (if i < 1698 then (if i < 1696 then decide (7 ≤ count1689 b) else (if i < 1697 then decide (8 ≤ count1689 b) else decide (9 ≤ count1689 b))) else (if i < 1700 then (if i < 1699 then decide (10 ≤ count1689 b) else decide (11 ≤ count1689 b)) else (if i < 1701 then decide (12 ≤ count1689 b) else decide (13 ≤ count1689 b)))) else (if i < 1705 then (if i < 1703 then decide (14 ≤ count1689 b) else (if i < 1704 then decide (15 ≤ count1689 b) else decide (16 ≤ count1689 b))) else (if i < 1707 then (if i < 1706 then decide (17 ≤ count1689 b) else decide (18 ≤ count1689 b)) else (if i < 1708 then decide (19 ≤ count1689 b) else decide (20 ≤ count1689 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (10 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (14 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (33 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (35 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (37 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (42 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (48 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (49 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (50 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (54 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (58 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (96 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (98 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (100 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (101 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (102 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (104 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (106 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (107 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (108 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (110 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (113 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (115 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (117 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (118 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (119 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (120 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (121 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (123 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (225 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (227 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (228 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (231 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (233 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (234 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (236 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (237 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (240 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (241 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (242 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (244 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (250 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (252 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (253 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (254 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (255 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (257 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (259 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (261 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (268 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (273 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (353 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (355 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (356 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (357 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (359 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (362 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (363 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (364 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (365 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (368 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (369 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (370 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (374 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (378 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (381 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (382 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (383 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (417 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (419 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (420 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (421 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (423 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (426 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (427 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (428 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (429 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (432 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (433 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (434 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (438 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (442 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (445 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (446 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (447 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (480 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (482 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (483 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (484 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (486 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (487 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (488 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (489 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (490 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (491 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (492 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (493 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (494 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (499 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (500 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (501 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (502 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (503 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (504 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (505 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (507 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (509 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (511 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (33 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (35 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (37 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (42 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (48 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (49 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (50 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (54 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (58 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (96 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (98 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (100 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (101 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (102 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (104 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (106 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (107 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (108 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (110 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (113 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (117 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (119 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (120 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (121 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (123 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (225 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (231 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (237 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (241 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (242 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (250 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (252 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (253 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (269 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (273 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (278 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (285 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (286 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (353 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (356 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (359 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (362 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (363 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (364 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (365 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (369 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (370 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (374 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (378 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (381 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (382 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (383 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (417 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (420 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (423 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (429 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (433 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (434 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (438 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (442 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (445 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (483 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (484 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (489 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (490 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (494 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (500 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (501 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (503 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (504 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (505 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (507 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (511 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (2 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value262 (q : Snake 81) : valuation q 262 = decide (2 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value292 (q : Snake 81) : valuation q 292 = decide (2 ≤ count291 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value350 (q : Snake 81) : valuation q 350 = decide (2 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value450 (q : Snake 81) : valuation q 450 = decide (2 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value452 (q : Snake 81) : valuation q 452 = decide (2 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value460 (q : Snake 81) : valuation q 460 = decide (2 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value462 (q : Snake 81) : valuation q 462 = decide (2 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value464 (q : Snake 81) : valuation q 464 = decide (2 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value466 (q : Snake 81) : valuation q 466 = decide (2 ≤ count465 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (1 ≤ count1413 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (2 ≤ count1413 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (2 ≤ count1415 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (3 ≤ count1415 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (1 ≤ count1418 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (2 ≤ count1418 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (1 ≤ count1420 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (2 ≤ count1420 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (1 ≤ count1422 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (2 ≤ count1422 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (3 ≤ count1422 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (2 ≤ count1426 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (3 ≤ count1426 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (4 ≤ count1426 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (5 ≤ count1426 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (6 ≤ count1426 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (1 ≤ count1433 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (2 ≤ count1433 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (1 ≤ count1435 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (2 ≤ count1435 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (1 ≤ count1437 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (2 ≤ count1437 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (3 ≤ count1437 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (4 ≤ count1437 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (1 ≤ count1441 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (2 ≤ count1441 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (1 ≤ count1443 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (2 ≤ count1443 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (1 ≤ count1445 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (2 ≤ count1445 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (3 ≤ count1445 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (4 ≤ count1445 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (2 ≤ count1449 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (3 ≤ count1449 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (4 ≤ count1449 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (5 ≤ count1449 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (6 ≤ count1449 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (5 ≤ count1457 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (6 ≤ count1457 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (7 ≤ count1457 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (8 ≤ count1457 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (9 ≤ count1457 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (1 ≤ count1472 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (2 ≤ count1472 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (1 ≤ count1474 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (2 ≤ count1474 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (3 ≤ count1474 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (1 ≤ count1477 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (2 ≤ count1477 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (1 ≤ count1479 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (1 ≤ count1481 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (2 ≤ count1481 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (3 ≤ count1481 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (1 ≤ count1485 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (3 ≤ count1485 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (4 ≤ count1485 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (5 ≤ count1485 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (1 ≤ count1492 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (2 ≤ count1492 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (1 ≤ count1494 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (1 ≤ count1496 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (2 ≤ count1496 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (3 ≤ count1496 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (1 ≤ count1500 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (1 ≤ count1502 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (1 ≤ count1504 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (2 ≤ count1504 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (2 ≤ count1508 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (3 ≤ count1508 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (4 ≤ count1508 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (2 ≤ count1516 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (3 ≤ count1516 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (4 ≤ count1516 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (5 ≤ count1516 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (6 ≤ count1516 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (7 ≤ count1516 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (8 ≤ count1531 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (9 ≤ count1531 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (10 ≤ count1531 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (11 ≤ count1531 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (12 ≤ count1531 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (13 ≤ count1531 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (1 ≤ count1553 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (1 ≤ count1556 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (2 ≤ count1556 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (1 ≤ count1558 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (2 ≤ count1558 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (1 ≤ count1560 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (2 ≤ count1560 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (3 ≤ count1560 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (3 ≤ count1564 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (1 ≤ count1571 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (2 ≤ count1571 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (1 ≤ count1573 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (2 ≤ count1573 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (1 ≤ count1575 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (2 ≤ count1575 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (1 ≤ count1579 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (2 ≤ count1579 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (1 ≤ count1581 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (2 ≤ count1581 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (1 ≤ count1583 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (2 ≤ count1583 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (3 ≤ count1583 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (1 ≤ count1587 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (2 ≤ count1587 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (3 ≤ count1587 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (4 ≤ count1587 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (1 ≤ count1595 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (2 ≤ count1595 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (3 ≤ count1595 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (4 ≤ count1595 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (5 ≤ count1595 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (6 ≤ count1595 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (1 ≤ count1610 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (2 ≤ count1610 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (1 ≤ count1612 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (2 ≤ count1612 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (1 ≤ count1615 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (2 ≤ count1615 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (1 ≤ count1617 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (2 ≤ count1617 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (1 ≤ count1619 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (2 ≤ count1619 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (3 ≤ count1619 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (4 ≤ count1619 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (1 ≤ count1623 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (2 ≤ count1623 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (3 ≤ count1623 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (4 ≤ count1623 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (5 ≤ count1623 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (1 ≤ count1630 (baseVal q)) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (2 ≤ count1630 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (1 ≤ count1632 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (2 ≤ count1632 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (1 ≤ count1634 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (2 ≤ count1634 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (3 ≤ count1634 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (4 ≤ count1634 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (1 ≤ count1638 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (2 ≤ count1638 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (1 ≤ count1640 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (2 ≤ count1640 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (1 ≤ count1642 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (2 ≤ count1642 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (3 ≤ count1642 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (4 ≤ count1642 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (1 ≤ count1646 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (2 ≤ count1646 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (3 ≤ count1646 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (4 ≤ count1646 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (5 ≤ count1646 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (6 ≤ count1646 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (7 ≤ count1646 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (8 ≤ count1646 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (2 ≤ count1654 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (3 ≤ count1654 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (4 ≤ count1654 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (5 ≤ count1654 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (6 ≤ count1654 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (7 ≤ count1654 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (8 ≤ count1654 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (9 ≤ count1654 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (10 ≤ count1654 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (7 ≤ count1669 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (8 ≤ count1669 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (9 ≤ count1669 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (10 ≤ count1669 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (11 ≤ count1669 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (12 ≤ count1669 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (20 ≤ count1689 (baseVal q)) := rfl
theorem meaningNeg118 (b : Nat → Bool) : literal (valuationOf b) (-118) = decide (1 ≤ countLit b [-118]) := by
  change literal b (-118) = decide (1 ≤ countLit b [-118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-118) <;> decide
theorem meaningNeg115 (b : Nat → Bool) : literal (valuationOf b) (-115) = decide (1 ≤ countLit b [-115]) := by
  change literal b (-115) = decide (1 ≤ countLit b [-115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-115) <;> decide
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
theorem meaningNeg94 (b : Nat → Bool) : literal (valuationOf b) (-94) = decide (1 ≤ countLit b [-94]) := by
  change literal b (-94) = decide (1 ≤ countLit b [-94])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-94) <;> decide
theorem meaningNeg93 (b : Nat → Bool) : literal (valuationOf b) (-93) = decide (1 ≤ countLit b [-93]) := by
  change literal b (-93) = decide (1 ≤ countLit b [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-93) <;> decide
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
theorem meaningNeg80 (b : Nat → Bool) : literal (valuationOf b) (-80) = decide (1 ≤ countLit b [-80]) := by
  change literal b (-80) = decide (1 ≤ countLit b [-80])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-80) <;> decide
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
theorem meaningNeg69 (b : Nat → Bool) : literal (valuationOf b) (-69) = decide (1 ≤ countLit b [-69]) := by
  change literal b (-69) = decide (1 ≤ countLit b [-69])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-69) <;> decide
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
theorem meaningNeg63 (b : Nat → Bool) : literal (valuationOf b) (-63) = decide (1 ≤ countLit b [-63]) := by
  change literal b (-63) = decide (1 ≤ countLit b [-63])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-63) <;> decide
theorem meaningNeg55 (b : Nat → Bool) : literal (valuationOf b) (-55) = decide (1 ≤ countLit b [-55]) := by
  change literal b (-55) = decide (1 ≤ countLit b [-55])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-55) <;> decide
theorem meaningNeg52 (b : Nat → Bool) : literal (valuationOf b) (-52) = decide (1 ≤ countLit b [-52]) := by
  change literal b (-52) = decide (1 ≤ countLit b [-52])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-52) <;> decide
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
theorem meaningNeg45 (b : Nat → Bool) : literal (valuationOf b) (-45) = decide (1 ≤ countLit b [-45]) := by
  change literal b (-45) = decide (1 ≤ countLit b [-45])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-45) <;> decide
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
theorem meaningNeg31 (b : Nat → Bool) : literal (valuationOf b) (-31) = decide (1 ≤ countLit b [-31]) := by
  change literal b (-31) = decide (1 ≤ countLit b [-31])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-31) <;> decide
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
theorem meaningNeg17 (b : Nat → Bool) : literal (valuationOf b) (-17) = decide (1 ≤ countLit b [-17]) := by
  change literal b (-17) = decide (1 ≤ countLit b [-17])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-17) <;> decide
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
theorem meaningNeg2 (b : Nat → Bool) : literal (valuationOf b) (-2) = decide (1 ≤ countLit b [-2]) := by
  change literal b (-2) = decide (1 ≤ countLit b [-2])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-2) <;> decide
theorem meaning119 (b : Nat → Bool) : literal (valuationOf b) (119) = decide (1 ≤ countLit b [119]) := by
  change literal b (119) = decide (1 ≤ countLit b [119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (119) <;> decide
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
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
theorem meaning130 (b : Nat → Bool) : literal (valuationOf b) (130) = decide (1 ≤ countLit b [130]) := by
  change literal b (130) = decide (1 ≤ countLit b [130])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (130) <;> decide
theorem meaning133 (b : Nat → Bool) : literal (valuationOf b) (133) = decide (1 ≤ countLit b [133]) := by
  change literal b (133) = decide (1 ≤ countLit b [133])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (133) <;> decide
theorem meaning134 (b : Nat → Bool) : literal (valuationOf b) (134) = decide (1 ≤ countLit b [134]) := by
  change literal b (134) = decide (1 ≤ countLit b [134])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (134) <;> decide
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
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
theorem meaning147 (b : Nat → Bool) : literal (valuationOf b) (147) = decide (1 ≤ countLit b [147]) := by
  change literal b (147) = decide (1 ≤ countLit b [147])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (147) <;> decide
theorem meaning148 (b : Nat → Bool) : literal (valuationOf b) (148) = decide (1 ≤ countLit b [148]) := by
  change literal b (148) = decide (1 ≤ countLit b [148])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (148) <;> decide
theorem meaning151 (b : Nat → Bool) : literal (valuationOf b) (151) = decide (1 ≤ countLit b [151]) := by
  change literal b (151) = decide (1 ≤ countLit b [151])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (151) <;> decide
theorem meaning155 (b : Nat → Bool) : literal (valuationOf b) (155) = decide (1 ≤ countLit b [155]) := by
  change literal b (155) = decide (1 ≤ countLit b [155])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (155) <;> decide
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
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
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
theorem meaning175 (b : Nat → Bool) : literal (valuationOf b) (175) = decide (1 ≤ countLit b [175]) := by
  change literal b (175) = decide (1 ≤ countLit b [175])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (175) <;> decide
theorem meaning176 (b : Nat → Bool) : literal (valuationOf b) (176) = decide (1 ≤ countLit b [176]) := by
  change literal b (176) = decide (1 ≤ countLit b [176])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (176) <;> decide
theorem meaning179 (b : Nat → Bool) : literal (valuationOf b) (179) = decide (1 ≤ countLit b [179]) := by
  change literal b (179) = decide (1 ≤ countLit b [179])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (179) <;> decide
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
theorem meaning182 (b : Nat → Bool) : literal (valuationOf b) (182) = decide (1 ≤ countLit b [182]) := by
  change literal b (182) = decide (1 ≤ countLit b [182])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (182) <;> decide
theorem meaning184 (b : Nat → Bool) : literal (valuationOf b) (184) = decide (1 ≤ countLit b [184]) := by
  change literal b (184) = decide (1 ≤ countLit b [184])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (184) <;> decide
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
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) (199) = decide (1 ≤ countLit b [199]) := by
  change literal b (199) = decide (1 ≤ countLit b [199])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (199) <;> decide
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
theorem meaning205 (b : Nat → Bool) : literal (valuationOf b) (205) = decide (1 ≤ countLit b [205]) := by
  change literal b (205) = decide (1 ≤ countLit b [205])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (205) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
theorem meaning214 (b : Nat → Bool) : literal (valuationOf b) (214) = decide (1 ≤ countLit b [214]) := by
  change literal b (214) = decide (1 ≤ countLit b [214])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (214) <;> decide
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) (218) = decide (1 ≤ countLit b [218]) := by
  change literal b (218) = decide (1 ≤ countLit b [218])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (218) <;> decide
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
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) (232) = decide (1 ≤ countLit b [232]) := by
  change literal b (232) = decide (1 ≤ countLit b [232])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (232) <;> decide
theorem meaning234 (b : Nat → Bool) : literal (valuationOf b) (234) = decide (1 ≤ countLit b [234]) := by
  change literal b (234) = decide (1 ≤ countLit b [234])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (234) <;> decide
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) (235) = decide (1 ≤ countLit b [235]) := by
  change literal b (235) = decide (1 ≤ countLit b [235])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (235) <;> decide
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning248 (b : Nat → Bool) : literal (valuationOf b) 248 = decide (2 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning262 (b : Nat → Bool) : literal (valuationOf b) 262 = decide (2 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning292 (b : Nat → Bool) : literal (valuationOf b) 292 = decide (2 ≤ count291 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning350 (b : Nat → Bool) : literal (valuationOf b) 350 = decide (2 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning402 (b : Nat → Bool) : literal (valuationOf b) 402 = decide (2 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning450 (b : Nat → Bool) : literal (valuationOf b) 450 = decide (2 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning452 (b : Nat → Bool) : literal (valuationOf b) 452 = decide (2 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning460 (b : Nat → Bool) : literal (valuationOf b) 460 = decide (2 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning462 (b : Nat → Bool) : literal (valuationOf b) 462 = decide (2 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning464 (b : Nat → Bool) : literal (valuationOf b) 464 = decide (2 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning466 (b : Nat → Bool) : literal (valuationOf b) 466 = decide (2 ≤ count465 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (1 ≤ count1413 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (2 ≤ count1413 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (2 ≤ count1415 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (3 ≤ count1415 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (1 ≤ count1418 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (2 ≤ count1418 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (1 ≤ count1420 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (2 ≤ count1420 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (1 ≤ count1422 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (2 ≤ count1422 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (3 ≤ count1422 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (2 ≤ count1426 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (3 ≤ count1426 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (4 ≤ count1426 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (5 ≤ count1426 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (6 ≤ count1426 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (1 ≤ count1433 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (2 ≤ count1433 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (1 ≤ count1435 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (2 ≤ count1435 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (1 ≤ count1437 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (2 ≤ count1437 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (3 ≤ count1437 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (4 ≤ count1437 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (1 ≤ count1441 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (2 ≤ count1441 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (1 ≤ count1443 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (2 ≤ count1443 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (1 ≤ count1445 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (2 ≤ count1445 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (3 ≤ count1445 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (4 ≤ count1445 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (2 ≤ count1449 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (3 ≤ count1449 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (4 ≤ count1449 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (5 ≤ count1449 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (6 ≤ count1449 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (5 ≤ count1457 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (6 ≤ count1457 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (7 ≤ count1457 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (8 ≤ count1457 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (9 ≤ count1457 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (1 ≤ count1472 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (2 ≤ count1472 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (1 ≤ count1474 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (2 ≤ count1474 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (3 ≤ count1474 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (1 ≤ count1477 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (2 ≤ count1477 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (1 ≤ count1479 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (1 ≤ count1481 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (2 ≤ count1481 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (3 ≤ count1481 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (1 ≤ count1485 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (2 ≤ count1485 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (3 ≤ count1485 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (4 ≤ count1485 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (5 ≤ count1485 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (1 ≤ count1492 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (2 ≤ count1492 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (1 ≤ count1494 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (1 ≤ count1496 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (2 ≤ count1496 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (3 ≤ count1496 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (1 ≤ count1500 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (1 ≤ count1502 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (1 ≤ count1504 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (2 ≤ count1504 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (2 ≤ count1508 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (3 ≤ count1508 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (4 ≤ count1508 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (2 ≤ count1516 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (3 ≤ count1516 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (4 ≤ count1516 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (5 ≤ count1516 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (6 ≤ count1516 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (7 ≤ count1516 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (8 ≤ count1531 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (9 ≤ count1531 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (10 ≤ count1531 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (11 ≤ count1531 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (12 ≤ count1531 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (13 ≤ count1531 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (1 ≤ count1553 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (1 ≤ count1556 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (2 ≤ count1556 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (1 ≤ count1558 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (2 ≤ count1558 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (1 ≤ count1560 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (2 ≤ count1560 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (3 ≤ count1560 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (3 ≤ count1564 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (1 ≤ count1571 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (2 ≤ count1571 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (1 ≤ count1573 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (2 ≤ count1573 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (1 ≤ count1575 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (2 ≤ count1575 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (1 ≤ count1579 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (2 ≤ count1579 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (1 ≤ count1581 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (2 ≤ count1581 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (1 ≤ count1583 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (2 ≤ count1583 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (3 ≤ count1583 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (1 ≤ count1587 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (2 ≤ count1587 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (3 ≤ count1587 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (4 ≤ count1587 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (1 ≤ count1595 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (2 ≤ count1595 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (3 ≤ count1595 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (4 ≤ count1595 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (5 ≤ count1595 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (6 ≤ count1595 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (1 ≤ count1610 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (2 ≤ count1610 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (1 ≤ count1612 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (2 ≤ count1612 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (1 ≤ count1615 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (2 ≤ count1615 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (1 ≤ count1617 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (2 ≤ count1617 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (1 ≤ count1619 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (2 ≤ count1619 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (3 ≤ count1619 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (4 ≤ count1619 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (1 ≤ count1623 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (2 ≤ count1623 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (3 ≤ count1623 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (4 ≤ count1623 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (5 ≤ count1623 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (1 ≤ count1630 b) := rfl
theorem meaning1631 (b : Nat → Bool) : literal (valuationOf b) 1631 = decide (2 ≤ count1630 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (1 ≤ count1632 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (2 ≤ count1632 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (1 ≤ count1634 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (2 ≤ count1634 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (3 ≤ count1634 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (4 ≤ count1634 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (1 ≤ count1638 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (2 ≤ count1638 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (1 ≤ count1640 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (2 ≤ count1640 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (1 ≤ count1642 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (2 ≤ count1642 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (3 ≤ count1642 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (4 ≤ count1642 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (1 ≤ count1646 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (2 ≤ count1646 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (3 ≤ count1646 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (4 ≤ count1646 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (5 ≤ count1646 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (6 ≤ count1646 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (7 ≤ count1646 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (8 ≤ count1646 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (2 ≤ count1654 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (3 ≤ count1654 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (4 ≤ count1654 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (5 ≤ count1654 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (6 ≤ count1654 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (7 ≤ count1654 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (8 ≤ count1654 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (9 ≤ count1654 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (10 ≤ count1654 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (7 ≤ count1669 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (8 ≤ count1669 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (9 ≤ count1669 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (10 ≤ count1669 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (11 ≤ count1669 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (12 ≤ count1669 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (20 ≤ count1689 b) := rfl
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
end Snake9.Regrowth.E112104
