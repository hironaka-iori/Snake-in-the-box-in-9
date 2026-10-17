import E112256Data
namespace Snake9.Regrowth.E112256
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 127 then (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (65 : Vertex)) else decide (InPath q (66 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (69 : Vertex)) else decide (InPath q (70 : Vertex))) else (if i < 6 then decide (InPath q (72 : Vertex)) else decide (InPath q (73 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (75 : Vertex)) else decide (InPath q (76 : Vertex))) else (if i < 10 then decide (InPath q (79 : Vertex)) else decide (InPath q (80 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (83 : Vertex)) else decide (InPath q (84 : Vertex))) else (if i < 14 then decide (InPath q (87 : Vertex)) else decide (InPath q (89 : Vertex)))))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then decide (InPath q (90 : Vertex)) else decide (InPath q (93 : Vertex))) else (if i < 18 then decide (InPath q (94 : Vertex)) else decide (InPath q (95 : Vertex)))) else (if i < 21 then (if i < 20 then decide (InPath q (96 : Vertex)) else decide (InPath q (98 : Vertex))) else (if i < 22 then decide (InPath q (101 : Vertex)) else decide (InPath q (103 : Vertex))))) else (if i < 27 then (if i < 25 then (if i < 24 then decide (InPath q (105 : Vertex)) else decide (InPath q (107 : Vertex))) else (if i < 26 then decide (InPath q (108 : Vertex)) else decide (InPath q (110 : Vertex)))) else (if i < 29 then (if i < 28 then decide (InPath q (112 : Vertex)) else decide (InPath q (113 : Vertex))) else (if i < 30 then decide (InPath q (115 : Vertex)) else decide (InPath q (116 : Vertex))))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then decide (InPath q (118 : Vertex)) else decide (InPath q (122 : Vertex))) else (if i < 34 then decide (InPath q (125 : Vertex)) else decide (InPath q (126 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (127 : Vertex)) else decide (InPath q (192 : Vertex))) else (if i < 38 then decide (InPath q (193 : Vertex)) else decide (InPath q (194 : Vertex))))) else (if i < 43 then (if i < 41 then (if i < 40 then decide (InPath q (196 : Vertex)) else decide (InPath q (200 : Vertex))) else (if i < 42 then decide (InPath q (201 : Vertex)) else decide (InPath q (202 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (204 : Vertex)) else decide (InPath q (207 : Vertex))) else (if i < 46 then decide (InPath q (210 : Vertex)) else decide (InPath q (211 : Vertex)))))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then decide (InPath q (212 : Vertex)) else decide (InPath q (213 : Vertex))) else (if i < 50 then decide (InPath q (215 : Vertex)) else decide (InPath q (217 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (218 : Vertex)) else decide (InPath q (220 : Vertex))) else (if i < 54 then decide (InPath q (221 : Vertex)) else decide (InPath q (223 : Vertex))))) else (if i < 59 then (if i < 57 then (if i < 56 then decide (InPath q (224 : Vertex)) else decide (InPath q (227 : Vertex))) else (if i < 58 then decide (InPath q (228 : Vertex)) else decide (InPath q (231 : Vertex)))) else (if i < 61 then (if i < 60 then decide (InPath q (234 : Vertex)) else decide (InPath q (235 : Vertex))) else (if i < 62 then decide (InPath q (237 : Vertex)) else decide (InPath q (238 : Vertex)))))))) else (if i < 95 then (if i < 79 then (if i < 71 then (if i < 67 then (if i < 65 then (if i < 64 then decide (InPath q (240 : Vertex)) else decide (InPath q (241 : Vertex))) else (if i < 66 then decide (InPath q (243 : Vertex)) else decide (InPath q (244 : Vertex)))) else (if i < 69 then (if i < 68 then decide (InPath q (245 : Vertex)) else decide (InPath q (246 : Vertex))) else (if i < 70 then decide (InPath q (248 : Vertex)) else decide (InPath q (250 : Vertex))))) else (if i < 75 then (if i < 73 then (if i < 72 then decide (InPath q (251 : Vertex)) else decide (InPath q (253 : Vertex))) else (if i < 74 then decide (InPath q (254 : Vertex)) else decide (InPath q (281 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (285 : Vertex)) else decide (InPath q (317 : Vertex))) else (if i < 78 then decide (InPath q (319 : Vertex)) else decide (InPath q (329 : Vertex)))))) else (if i < 87 then (if i < 83 then (if i < 81 then (if i < 80 then decide (InPath q (330 : Vertex)) else decide (InPath q (333 : Vertex))) else (if i < 82 then decide (InPath q (334 : Vertex)) else decide (InPath q (336 : Vertex)))) else (if i < 85 then (if i < 84 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex))) else (if i < 86 then decide (InPath q (341 : Vertex)) else decide (InPath q (342 : Vertex))))) else (if i < 91 then (if i < 89 then (if i < 88 then decide (InPath q (345 : Vertex)) else decide (InPath q (347 : Vertex))) else (if i < 90 then decide (InPath q (348 : Vertex)) else decide (InPath q (349 : Vertex)))) else (if i < 93 then (if i < 92 then decide (InPath q (350 : Vertex)) else decide (InPath q (351 : Vertex))) else (if i < 94 then decide (InPath q (365 : Vertex)) else decide (InPath q (367 : Vertex))))))) else (if i < 111 then (if i < 103 then (if i < 99 then (if i < 97 then (if i < 96 then decide (InPath q (370 : Vertex)) else decide (InPath q (373 : Vertex))) else (if i < 98 then decide (InPath q (375 : Vertex)) else decide (InPath q (379 : Vertex)))) else (if i < 101 then (if i < 100 then decide (InPath q (381 : Vertex)) else decide (InPath q (382 : Vertex))) else (if i < 102 then decide (InPath q (383 : Vertex)) else decide (InPath q (458 : Vertex))))) else (if i < 107 then (if i < 105 then (if i < 104 then decide (InPath q (459 : Vertex)) else decide (InPath q (460 : Vertex))) else (if i < 106 then decide (InPath q (461 : Vertex)) else decide (InPath q (464 : Vertex)))) else (if i < 109 then (if i < 108 then decide (InPath q (465 : Vertex)) else decide (InPath q (467 : Vertex))) else (if i < 110 then decide (InPath q (469 : Vertex)) else decide (InPath q (472 : Vertex)))))) else (if i < 119 then (if i < 115 then (if i < 113 then (if i < 112 then decide (InPath q (473 : Vertex)) else decide (InPath q (475 : Vertex))) else (if i < 114 then decide (InPath q (476 : Vertex)) else decide (InPath q (477 : Vertex)))) else (if i < 117 then (if i < 116 then decide (InPath q (478 : Vertex)) else decide (InPath q (495 : Vertex))) else (if i < 118 then decide (InPath q (496 : Vertex)) else decide (InPath q (498 : Vertex))))) else (if i < 123 then (if i < 121 then (if i < 120 then decide (InPath q (499 : Vertex)) else decide (InPath q (500 : Vertex))) else (if i < 122 then decide (InPath q (501 : Vertex)) else decide (InPath q (503 : Vertex)))) else (if i < 125 then (if i < 124 then decide (InPath q (506 : Vertex)) else decide (InPath q (507 : Vertex))) else (if i < 126 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 191 then (if i < 159 then (if i < 143 then (if i < 135 then (if i < 131 then (if i < 129 then (if i < 128 then decide (InPath q (511 : Vertex)) else decide (BallClauseLogic.Endpoint q (65 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else decide (BallClauseLogic.Endpoint q (69 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (72 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (73 : Vertex)) else decide (BallClauseLogic.Endpoint q (75 : Vertex))))) else (if i < 139 then (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (76 : Vertex)) else decide (BallClauseLogic.Endpoint q (79 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else decide (BallClauseLogic.Endpoint q (83 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (87 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (89 : Vertex)) else decide (BallClauseLogic.Endpoint q (90 : Vertex)))))) else (if i < 151 then (if i < 147 then (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (93 : Vertex)) else decide (BallClauseLogic.Endpoint q (94 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (96 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (98 : Vertex)) else decide (BallClauseLogic.Endpoint q (101 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (105 : Vertex))))) else (if i < 155 then (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (107 : Vertex)) else decide (BallClauseLogic.Endpoint q (108 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (110 : Vertex)) else decide (BallClauseLogic.Endpoint q (112 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (113 : Vertex)) else decide (BallClauseLogic.Endpoint q (115 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (116 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex))))))) else (if i < 175 then (if i < 167 then (if i < 163 then (if i < 161 then (if i < 160 then decide (BallClauseLogic.Endpoint q (122 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (126 : Vertex)) else decide (BallClauseLogic.Endpoint q (127 : Vertex)))) else (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (193 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (194 : Vertex)) else decide (BallClauseLogic.Endpoint q (196 : Vertex))))) else (if i < 171 then (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else decide (BallClauseLogic.Endpoint q (201 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (202 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else decide (BallClauseLogic.Endpoint q (210 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else decide (BallClauseLogic.Endpoint q (212 : Vertex)))))) else (if i < 183 then (if i < 179 then (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (213 : Vertex)) else decide (BallClauseLogic.Endpoint q (215 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (217 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex)))) else (if i < 181 then (if i < 180 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex))) else (if i < 182 then decide (BallClauseLogic.Endpoint q (223 : Vertex)) else decide (BallClauseLogic.Endpoint q (224 : Vertex))))) else (if i < 187 then (if i < 185 then (if i < 184 then decide (BallClauseLogic.Endpoint q (227 : Vertex)) else decide (BallClauseLogic.Endpoint q (228 : Vertex))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (231 : Vertex)) else decide (BallClauseLogic.Endpoint q (234 : Vertex)))) else (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (235 : Vertex)) else decide (BallClauseLogic.Endpoint q (237 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else decide (BallClauseLogic.Endpoint q (240 : Vertex)))))))) else (if i < 223 then (if i < 207 then (if i < 199 then (if i < 195 then (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (241 : Vertex)) else decide (BallClauseLogic.Endpoint q (243 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (245 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (246 : Vertex)) else decide (BallClauseLogic.Endpoint q (248 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (250 : Vertex)) else decide (BallClauseLogic.Endpoint q (251 : Vertex))))) else (if i < 203 then (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (253 : Vertex)) else decide (BallClauseLogic.Endpoint q (254 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (285 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (319 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else decide (BallClauseLogic.Endpoint q (330 : Vertex)))))) else (if i < 215 then (if i < 211 then (if i < 209 then (if i < 208 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (334 : Vertex))) else (if i < 210 then decide (BallClauseLogic.Endpoint q (336 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex)))) else (if i < 213 then (if i < 212 then decide (BallClauseLogic.Endpoint q (338 : Vertex)) else decide (BallClauseLogic.Endpoint q (341 : Vertex))) else (if i < 214 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (345 : Vertex))))) else (if i < 219 then (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (347 : Vertex)) else decide (BallClauseLogic.Endpoint q (348 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex)))) else (if i < 221 then (if i < 220 then decide (BallClauseLogic.Endpoint q (351 : Vertex)) else decide (BallClauseLogic.Endpoint q (365 : Vertex))) else (if i < 222 then decide (BallClauseLogic.Endpoint q (367 : Vertex)) else decide (BallClauseLogic.Endpoint q (370 : Vertex))))))) else (if i < 239 then (if i < 231 then (if i < 227 then (if i < 225 then (if i < 224 then decide (BallClauseLogic.Endpoint q (373 : Vertex)) else decide (BallClauseLogic.Endpoint q (375 : Vertex))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else decide (BallClauseLogic.Endpoint q (381 : Vertex)))) else (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (382 : Vertex)) else decide (BallClauseLogic.Endpoint q (383 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (458 : Vertex)) else decide (BallClauseLogic.Endpoint q (459 : Vertex))))) else (if i < 235 then (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (460 : Vertex)) else decide (BallClauseLogic.Endpoint q (461 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (464 : Vertex)) else decide (BallClauseLogic.Endpoint q (465 : Vertex)))) else (if i < 237 then (if i < 236 then decide (BallClauseLogic.Endpoint q (467 : Vertex)) else decide (BallClauseLogic.Endpoint q (469 : Vertex))) else (if i < 238 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex)))))) else (if i < 247 then (if i < 243 then (if i < 241 then (if i < 240 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (476 : Vertex))) else (if i < 242 then decide (BallClauseLogic.Endpoint q (477 : Vertex)) else decide (BallClauseLogic.Endpoint q (478 : Vertex)))) else (if i < 245 then (if i < 244 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (496 : Vertex))) else (if i < 246 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else decide (BallClauseLogic.Endpoint q (499 : Vertex))))) else (if i < 251 then (if i < 249 then (if i < 248 then decide (BallClauseLogic.Endpoint q (500 : Vertex)) else decide (BallClauseLogic.Endpoint q (501 : Vertex))) else (if i < 250 then decide (BallClauseLogic.Endpoint q (503 : Vertex)) else decide (BallClauseLogic.Endpoint q (506 : Vertex)))) else (if i < 253 then (if i < 252 then decide (BallClauseLogic.Endpoint q (507 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 254 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count255 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134]
def count267 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count269 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142]
def count281 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
def count283 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146]
def count289 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154, 155, 156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count315 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count317 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count331 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 173, 174]
def count343 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count347 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count377 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count379 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count381 (b : Nat → Bool) : Nat := countLit b [191, 192, 193]
def count383 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197]
def count389 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197]
def count391 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count393 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204, 205]
def count405 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]
def count407 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count409 (b : Nat → Bool) : Nat := countLit b [208, 210]
def count411 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 210]
def count413 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count417 (b : Nat → Bool) : Nat := countLit b [211, 212, 213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 210, 211, 212, 213, 214]
def count421 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count431 (b : Nat → Bool) : Nat := countLit b [219, 220, 221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218, 219, 220, 221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count437 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count439 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count441 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count443 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226]
def count445 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [227, 228, 229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230]
def count453 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [235, 236, 237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234, 235, 236, 237, 238]
def count467 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238]
def count469 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242]
def count475 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count477 (b : Nat → Bool) : Nat := countLit b [245, 246]
def count479 (b : Nat → Bool) : Nat := countLit b [243, 244, 245, 246]
def count481 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242, 243, 244, 245, 246]
def count483 (b : Nat → Bool) : Nat := countLit b [247, 248]
def count485 (b : Nat → Bool) : Nat := countLit b [249, 250]
def count487 (b : Nat → Bool) : Nat := countLit b [247, 248, 249, 250]
def count489 (b : Nat → Bool) : Nat := countLit b [251, 252]
def count491 (b : Nat → Bool) : Nat := countLit b [253, 254]
def count493 (b : Nat → Bool) : Nat := countLit b [251, 252, 253, 254]
def count495 (b : Nat → Bool) : Nat := countLit b [247, 248, 249, 250, 251, 252, 253, 254]
def count497 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count499 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count501 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count503 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254]
def count505 (b : Nat → Bool) : Nat := countLit b [2, 5]
def count507 (b : Nat → Bool) : Nat := countLit b [1, 2, 5]
def count510 (b : Nat → Bool) : Nat := countLit b [7, 10]
def count512 (b : Nat → Bool) : Nat := countLit b [11, 14]
def count514 (b : Nat → Bool) : Nat := countLit b [7, 10, 11, 14]
def count518 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 10, 11, 14]
def count525 (b : Nat → Bool) : Nat := countLit b [15, 18]
def count527 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count529 (b : Nat → Bool) : Nat := countLit b [15, 18, 19, 21]
def count533 (b : Nat → Bool) : Nat := countLit b [23, 25]
def count535 (b : Nat → Bool) : Nat := countLit b [28, 30]
def count537 (b : Nat → Bool) : Nat := countLit b [23, 25, 28, 30]
def count541 (b : Nat → Bool) : Nat := countLit b [15, 18, 19, 21, 23, 25, 28, 30]
def count549 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 10, 11, 14, 15, 18, 19, 21, 23, 25, 28, 30]
def count564 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count566 (b : Nat → Bool) : Nat := countLit b [33, 34, 36]
def count569 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count571 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count573 (b : Nat → Bool) : Nat := countLit b [41, 42, 43, 44]
def count577 (b : Nat → Bool) : Nat := countLit b [33, 34, 36, 41, 42, 43, 44]
def count584 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count586 (b : Nat → Bool) : Nat := countLit b [49, 53]
def count588 (b : Nat → Bool) : Nat := countLit b [45, 47, 49, 53]
def count592 (b : Nat → Bool) : Nat := countLit b [57, 58]
def count594 (b : Nat → Bool) : Nat := countLit b [60, 61]
def count596 (b : Nat → Bool) : Nat := countLit b [57, 58, 60, 61]
def count600 (b : Nat → Bool) : Nat := countLit b [45, 47, 49, 53, 57, 58, 60, 61]
def count608 (b : Nat → Bool) : Nat := countLit b [33, 34, 36, 41, 42, 43, 44, 45, 47, 49, 53, 57, 58, 60, 61]
def count623 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 10, 11, 14, 15, 18, 19, 21, 23, 25, 28, 30, 33, 34, 36, 41, 42, 43, 44, 45, 47, 49, 53, 57, 58, 60, 61]
def count653 (b : Nat → Bool) : Nat := countLit b [63, 65]
def count655 (b : Nat → Bool) : Nat := countLit b [62, 63, 65]
def count658 (b : Nat → Bool) : Nat := countLit b [67, 68]
def count660 (b : Nat → Bool) : Nat := countLit b [70, 74]
def count662 (b : Nat → Bool) : Nat := countLit b [67, 68, 70, 74]
def count666 (b : Nat → Bool) : Nat := countLit b [62, 63, 65, 67, 68, 70, 74]
def count673 (b : Nat → Bool) : Nat := countLit b [76, 78]
def count675 (b : Nat → Bool) : Nat := countLit b [79, 83]
def count677 (b : Nat → Bool) : Nat := countLit b [76, 78, 79, 83]
def count681 (b : Nat → Bool) : Nat := countLit b [84, 88]
def count683 (b : Nat → Bool) : Nat := countLit b [90, 91]
def count685 (b : Nat → Bool) : Nat := countLit b [84, 88, 90, 91]
def count689 (b : Nat → Bool) : Nat := countLit b [76, 78, 79, 83, 84, 88, 90, 91]
def count697 (b : Nat → Bool) : Nat := countLit b [62, 63, 65, 67, 68, 70, 74, 76, 78, 79, 83, 84, 88, 90, 91]
def count712 (b : Nat → Bool) : Nat := countLit b [93, 96]
def count714 (b : Nat → Bool) : Nat := countLit b [101, 103]
def count716 (b : Nat → Bool) : Nat := countLit b [93, 96, 101, 103]
def count720 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count722 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count724 (b : Nat → Bool) : Nat := countLit b [105, 106, 108, 109]
def count728 (b : Nat → Bool) : Nat := countLit b [93, 96, 101, 103, 105, 106, 108, 109]
def count736 (b : Nat → Bool) : Nat := countLit b [111, 113]
def count738 (b : Nat → Bool) : Nat := countLit b [116, 118]
def count740 (b : Nat → Bool) : Nat := countLit b [111, 113, 116, 118]
def count744 (b : Nat → Bool) : Nat := countLit b [120, 122]
def count746 (b : Nat → Bool) : Nat := countLit b [124, 126]
def count748 (b : Nat → Bool) : Nat := countLit b [120, 122, 124, 126]
def count752 (b : Nat → Bool) : Nat := countLit b [111, 113, 116, 118, 120, 122, 124, 126]
def count760 (b : Nat → Bool) : Nat := countLit b [93, 96, 101, 103, 105, 106, 108, 109, 111, 113, 116, 118, 120, 122, 124, 126]
def count776 (b : Nat → Bool) : Nat := countLit b [62, 63, 65, 67, 68, 70, 74, 76, 78, 79, 83, 84, 88, 90, 91, 93, 96, 101, 103, 105, 106, 108, 109, 111, 113, 116, 118, 120, 122, 124, 126]
def count807 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 10, 11, 14, 15, 18, 19, 21, 23, 25, 28, 30, 33, 34, 36, 41, 42, 43, 44, 45, 47, 49, 53, 57, 58, 60, 61, 62, 63, 65, 67, 68, 70, 74, 76, 78, 79, 83, 84, 88, 90, 91, 93, 96, 101, 103, 105, 106, 108, 109, 111, 113, 116, 118, 120, 122, 124, 126]
def count849 (b : Nat → Bool) : Nat := countLit b [-2, -5]
def count851 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5]
def count854 (b : Nat → Bool) : Nat := countLit b [-7, -10]
def count856 (b : Nat → Bool) : Nat := countLit b [-11, -14]
def count858 (b : Nat → Bool) : Nat := countLit b [-7, -10, -11, -14]
def count862 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -10, -11, -14]
def count869 (b : Nat → Bool) : Nat := countLit b [-15, -18]
def count871 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count873 (b : Nat → Bool) : Nat := countLit b [-15, -18, -19, -21]
def count877 (b : Nat → Bool) : Nat := countLit b [-23, -25]
def count879 (b : Nat → Bool) : Nat := countLit b [-28, -30]
def count881 (b : Nat → Bool) : Nat := countLit b [-23, -25, -28, -30]
def count885 (b : Nat → Bool) : Nat := countLit b [-15, -18, -19, -21, -23, -25, -28, -30]
def count893 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]
def count908 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count910 (b : Nat → Bool) : Nat := countLit b [-33, -34, -36]
def count913 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count915 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count917 (b : Nat → Bool) : Nat := countLit b [-41, -42, -43, -44]
def count921 (b : Nat → Bool) : Nat := countLit b [-33, -34, -36, -41, -42, -43, -44]
def count928 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count930 (b : Nat → Bool) : Nat := countLit b [-49, -53]
def count932 (b : Nat → Bool) : Nat := countLit b [-45, -47, -49, -53]
def count936 (b : Nat → Bool) : Nat := countLit b [-57, -58]
def count938 (b : Nat → Bool) : Nat := countLit b [-60, -61]
def count940 (b : Nat → Bool) : Nat := countLit b [-57, -58, -60, -61]
def count944 (b : Nat → Bool) : Nat := countLit b [-45, -47, -49, -53, -57, -58, -60, -61]
def count952 (b : Nat → Bool) : Nat := countLit b [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]
def count967 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]
def count988 (b : Nat → Bool) : Nat := countLit b [-63, -65]
def count990 (b : Nat → Bool) : Nat := countLit b [-62, -63, -65]
def count993 (b : Nat → Bool) : Nat := countLit b [-67, -68]
def count995 (b : Nat → Bool) : Nat := countLit b [-70, -74]
def count997 (b : Nat → Bool) : Nat := countLit b [-67, -68, -70, -74]
def count1001 (b : Nat → Bool) : Nat := countLit b [-62, -63, -65, -67, -68, -70, -74]
def count1008 (b : Nat → Bool) : Nat := countLit b [-76, -78]
def count1010 (b : Nat → Bool) : Nat := countLit b [-79, -83]
def count1012 (b : Nat → Bool) : Nat := countLit b [-76, -78, -79, -83]
def count1016 (b : Nat → Bool) : Nat := countLit b [-84, -88]
def count1018 (b : Nat → Bool) : Nat := countLit b [-90, -91]
def count1020 (b : Nat → Bool) : Nat := countLit b [-84, -88, -90, -91]
def count1024 (b : Nat → Bool) : Nat := countLit b [-76, -78, -79, -83, -84, -88, -90, -91]
def count1032 (b : Nat → Bool) : Nat := countLit b [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91]
def count1047 (b : Nat → Bool) : Nat := countLit b [-93, -96]
def count1049 (b : Nat → Bool) : Nat := countLit b [-101, -103]
def count1051 (b : Nat → Bool) : Nat := countLit b [-93, -96, -101, -103]
def count1055 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count1057 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count1059 (b : Nat → Bool) : Nat := countLit b [-105, -106, -108, -109]
def count1063 (b : Nat → Bool) : Nat := countLit b [-93, -96, -101, -103, -105, -106, -108, -109]
def count1071 (b : Nat → Bool) : Nat := countLit b [-111, -113]
def count1073 (b : Nat → Bool) : Nat := countLit b [-116, -118]
def count1075 (b : Nat → Bool) : Nat := countLit b [-111, -113, -116, -118]
def count1079 (b : Nat → Bool) : Nat := countLit b [-120, -122]
def count1081 (b : Nat → Bool) : Nat := countLit b [-124, -126]
def count1083 (b : Nat → Bool) : Nat := countLit b [-120, -122, -124, -126]
def count1087 (b : Nat → Bool) : Nat := countLit b [-111, -113, -116, -118, -120, -122, -124, -126]
def count1095 (b : Nat → Bool) : Nat := countLit b [-93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]
def count1111 (b : Nat → Bool) : Nat := countLit b [-62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]
def count1132 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30, -33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61, -62, -63, -65, -67, -68, -70, -74, -76, -78, -79, -83, -84, -88, -90, -91, -93, -96, -101, -103, -105, -106, -108, -109, -111, -113, -116, -118, -120, -122, -124, -126]
def count1153 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count1155 (b : Nat → Bool) : Nat := countLit b [6, 8]
def count1157 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8]
def count1161 (b : Nat → Bool) : Nat := countLit b [9, 12]
def count1163 (b : Nat → Bool) : Nat := countLit b [13, 16]
def count1165 (b : Nat → Bool) : Nat := countLit b [9, 12, 13, 16]
def count1169 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 9, 12, 13, 16]
def count1177 (b : Nat → Bool) : Nat := countLit b [17, 20]
def count1179 (b : Nat → Bool) : Nat := countLit b [22, 24]
def count1181 (b : Nat → Bool) : Nat := countLit b [17, 20, 22, 24]
def count1185 (b : Nat → Bool) : Nat := countLit b [26, 27]
def count1187 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count1189 (b : Nat → Bool) : Nat := countLit b [26, 27, 29, 31]
def count1193 (b : Nat → Bool) : Nat := countLit b [17, 20, 22, 24, 26, 27, 29, 31]
def count1201 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 9, 12, 13, 16, 17, 20, 22, 24, 26, 27, 29, 31]
def count1217 (b : Nat → Bool) : Nat := countLit b [32, 35]
def count1219 (b : Nat → Bool) : Nat := countLit b [37, 38]
def count1221 (b : Nat → Bool) : Nat := countLit b [32, 35, 37, 38]
def count1225 (b : Nat → Bool) : Nat := countLit b [39, 40]
def count1227 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count1229 (b : Nat → Bool) : Nat := countLit b [39, 40, 46, 48]
def count1233 (b : Nat → Bool) : Nat := countLit b [32, 35, 37, 38, 39, 40, 46, 48]
def count1241 (b : Nat → Bool) : Nat := countLit b [50, 51]
def count1243 (b : Nat → Bool) : Nat := countLit b [52, 54]
def count1245 (b : Nat → Bool) : Nat := countLit b [50, 51, 52, 54]
def count1249 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count1251 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count1253 (b : Nat → Bool) : Nat := countLit b [59, 64, 66]
def count1256 (b : Nat → Bool) : Nat := countLit b [55, 56, 59, 64, 66]
def count1261 (b : Nat → Bool) : Nat := countLit b [50, 51, 52, 54, 55, 56, 59, 64, 66]
def count1270 (b : Nat → Bool) : Nat := countLit b [32, 35, 37, 38, 39, 40, 46, 48, 50, 51, 52, 54, 55, 56, 59, 64, 66]
def count1287 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 9, 12, 13, 16, 17, 20, 22, 24, 26, 27, 29, 31, 32, 35, 37, 38, 39, 40, 46, 48, 50, 51, 52, 54, 55, 56, 59, 64, 66]
def count1320 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count1322 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count1324 (b : Nat → Bool) : Nat := countLit b [69, 71, 72, 73]
def count1328 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count1330 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count1332 (b : Nat → Bool) : Nat := countLit b [75, 77, 80, 81]
def count1336 (b : Nat → Bool) : Nat := countLit b [69, 71, 72, 73, 75, 77, 80, 81]
def count1344 (b : Nat → Bool) : Nat := countLit b [82, 85]
def count1346 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count1348 (b : Nat → Bool) : Nat := countLit b [82, 85, 86, 87]
def count1352 (b : Nat → Bool) : Nat := countLit b [89, 92]
def count1354 (b : Nat → Bool) : Nat := countLit b [94, 95]
def count1356 (b : Nat → Bool) : Nat := countLit b [89, 92, 94, 95]
def count1360 (b : Nat → Bool) : Nat := countLit b [82, 85, 86, 87, 89, 92, 94, 95]
def count1368 (b : Nat → Bool) : Nat := countLit b [69, 71, 72, 73, 75, 77, 80, 81, 82, 85, 86, 87, 89, 92, 94, 95]
def count1384 (b : Nat → Bool) : Nat := countLit b [97, 98]
def count1386 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count1388 (b : Nat → Bool) : Nat := countLit b [97, 98, 99, 100]
def count1392 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count1394 (b : Nat → Bool) : Nat := countLit b [107, 110]
def count1396 (b : Nat → Bool) : Nat := countLit b [102, 104, 107, 110]
def count1400 (b : Nat → Bool) : Nat := countLit b [97, 98, 99, 100, 102, 104, 107, 110]
def count1408 (b : Nat → Bool) : Nat := countLit b [112, 114]
def count1410 (b : Nat → Bool) : Nat := countLit b [115, 117]
def count1412 (b : Nat → Bool) : Nat := countLit b [112, 114, 115, 117]
def count1416 (b : Nat → Bool) : Nat := countLit b [119, 121]
def count1418 (b : Nat → Bool) : Nat := countLit b [125, 127]
def count1420 (b : Nat → Bool) : Nat := countLit b [123, 125, 127]
def count1423 (b : Nat → Bool) : Nat := countLit b [119, 121, 123, 125, 127]
def count1428 (b : Nat → Bool) : Nat := countLit b [112, 114, 115, 117, 119, 121, 123, 125, 127]
def count1437 (b : Nat → Bool) : Nat := countLit b [97, 98, 99, 100, 102, 104, 107, 110, 112, 114, 115, 117, 119, 121, 123, 125, 127]
def count1454 (b : Nat → Bool) : Nat := countLit b [69, 71, 72, 73, 75, 77, 80, 81, 82, 85, 86, 87, 89, 92, 94, 95, 97, 98, 99, 100, 102, 104, 107, 110, 112, 114, 115, 117, 119, 121, 123, 125, 127]
def count1487 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 8, 9, 12, 13, 16, 17, 20, 22, 24, 26, 27, 29, 31, 32, 35, 37, 38, 39, 40, 46, 48, 50, 51, 52, 54, 55, 56, 59, 64, 66, 69, 71, 72, 73, 75, 77, 80, 81, 82, 85, 86, 87, 89, 92, 94, 95, 97, 98, 99, 100, 102, 104, 107, 110, 112, 114, 115, 117, 119, 121, 123, 125, 127]
def count1529 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count1531 (b : Nat → Bool) : Nat := countLit b [-6, -8]
def count1533 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8]
def count1537 (b : Nat → Bool) : Nat := countLit b [-9, -12]
def count1539 (b : Nat → Bool) : Nat := countLit b [-13, -16]
def count1541 (b : Nat → Bool) : Nat := countLit b [-9, -12, -13, -16]
def count1545 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -9, -12, -13, -16]
def count1553 (b : Nat → Bool) : Nat := countLit b [-17, -20]
def count1555 (b : Nat → Bool) : Nat := countLit b [-22, -24]
def count1557 (b : Nat → Bool) : Nat := countLit b [-17, -20, -22, -24]
def count1561 (b : Nat → Bool) : Nat := countLit b [-26, -27]
def count1563 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count1565 (b : Nat → Bool) : Nat := countLit b [-26, -27, -29, -31]
def count1569 (b : Nat → Bool) : Nat := countLit b [-17, -20, -22, -24, -26, -27, -29, -31]
def count1577 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31]
def count1593 (b : Nat → Bool) : Nat := countLit b [-32, -35]
def count1595 (b : Nat → Bool) : Nat := countLit b [-37, -38]
def count1597 (b : Nat → Bool) : Nat := countLit b [-32, -35, -37, -38]
def count1601 (b : Nat → Bool) : Nat := countLit b [-39, -40]
def count1603 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count1605 (b : Nat → Bool) : Nat := countLit b [-39, -40, -46, -48]
def count1609 (b : Nat → Bool) : Nat := countLit b [-32, -35, -37, -38, -39, -40, -46, -48]
def count1617 (b : Nat → Bool) : Nat := countLit b [-50, -51]
def count1619 (b : Nat → Bool) : Nat := countLit b [-52, -54]
def count1621 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52, -54]
def count1625 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count1627 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1629 (b : Nat → Bool) : Nat := countLit b [-59, -64, -66]
def count1632 (b : Nat → Bool) : Nat := countLit b [-55, -56, -59, -64, -66]
def count1637 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52, -54, -55, -56, -59, -64, -66]
def count1646 (b : Nat → Bool) : Nat := countLit b [-32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66]
def count1663 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31, -32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66]
def count1689 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count1691 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count1693 (b : Nat → Bool) : Nat := countLit b [-69, -71, -72, -73]
def count1697 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count1699 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1701 (b : Nat → Bool) : Nat := countLit b [-75, -77, -80, -81]
def count1705 (b : Nat → Bool) : Nat := countLit b [-69, -71, -72, -73, -75, -77, -80, -81]
def count1713 (b : Nat → Bool) : Nat := countLit b [-82, -85]
def count1715 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count1717 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86, -87]
def count1721 (b : Nat → Bool) : Nat := countLit b [-89, -92]
def count1723 (b : Nat → Bool) : Nat := countLit b [-94, -95]
def count1725 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94, -95]
def count1729 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86, -87, -89, -92, -94, -95]
def count1737 (b : Nat → Bool) : Nat := countLit b [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95]
def count1753 (b : Nat → Bool) : Nat := countLit b [-97, -98]
def count1755 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1757 (b : Nat → Bool) : Nat := countLit b [-97, -98, -99, -100]
def count1761 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count1763 (b : Nat → Bool) : Nat := countLit b [-107, -110]
def count1765 (b : Nat → Bool) : Nat := countLit b [-102, -104, -107, -110]
def count1769 (b : Nat → Bool) : Nat := countLit b [-97, -98, -99, -100, -102, -104, -107, -110]
def count1777 (b : Nat → Bool) : Nat := countLit b [-112, -114]
def count1779 (b : Nat → Bool) : Nat := countLit b [-115, -117]
def count1781 (b : Nat → Bool) : Nat := countLit b [-112, -114, -115, -117]
def count1785 (b : Nat → Bool) : Nat := countLit b [-119, -121]
def count1787 (b : Nat → Bool) : Nat := countLit b [-125, -127]
def count1789 (b : Nat → Bool) : Nat := countLit b [-123, -125, -127]
def count1792 (b : Nat → Bool) : Nat := countLit b [-119, -121, -123, -125, -127]
def count1797 (b : Nat → Bool) : Nat := countLit b [-112, -114, -115, -117, -119, -121, -123, -125, -127]
def count1806 (b : Nat → Bool) : Nat := countLit b [-97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127]
def count1823 (b : Nat → Bool) : Nat := countLit b [-69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95, -97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127]
def count1849 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -8, -9, -12, -13, -16, -17, -20, -22, -24, -26, -27, -29, -31, -32, -35, -37, -38, -39, -40, -46, -48, -50, -51, -52, -54, -55, -56, -59, -64, -66, -69, -71, -72, -73, -75, -77, -80, -81, -82, -85, -86, -87, -89, -92, -94, -95, -97, -98, -99, -100, -102, -104, -107, -110, -112, -114, -115, -117, -119, -121, -123, -125, -127]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 937 then (if i < 468 then (if i < 234 then (if i < 117 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 25 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else b 24)) else (if i < 27 then (if i < 26 then b 25 else b 26) else (if i < 28 then b 27 else b 28))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else b 35))) else (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 41 then (if i < 40 then b 39 else b 40) else (if i < 42 then b 41 else b 42)))) else (if i < 50 then (if i < 46 then (if i < 44 then b 43 else (if i < 45 then b 44 else b 45)) else (if i < 48 then (if i < 47 then b 46 else b 47) else (if i < 49 then b 48 else b 49))) else (if i < 54 then (if i < 52 then (if i < 51 then b 50 else b 51) else (if i < 53 then b 52 else b 53)) else (if i < 56 then (if i < 55 then b 54 else b 55) else (if i < 57 then b 56 else b 57)))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else b 64))) else (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 70 then (if i < 69 then b 68 else b 69) else (if i < 71 then b 70 else b 71)))) else (if i < 79 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 77 then (if i < 76 then b 75 else b 76) else (if i < 78 then b 77 else b 78))) else (if i < 83 then (if i < 81 then (if i < 80 then b 79 else b 80) else (if i < 82 then b 81 else b 82)) else (if i < 85 then (if i < 84 then b 83 else b 84) else (if i < 86 then b 85 else b 86))))) else (if i < 102 then (if i < 94 then (if i < 90 then (if i < 88 then b 87 else (if i < 89 then b 88 else b 89)) else (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else b 93))) else (if i < 98 then (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else b 97)) else (if i < 100 then (if i < 99 then b 98 else b 99) else (if i < 101 then b 100 else b 101)))) else (if i < 109 then (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 107 then (if i < 106 then b 105 else b 106) else (if i < 108 then b 107 else b 108))) else (if i < 113 then (if i < 111 then (if i < 110 then b 109 else b 110) else (if i < 112 then b 111 else b 112)) else (if i < 115 then (if i < 114 then b 113 else b 114) else (if i < 116 then b 115 else b 116))))))) else (if i < 175 then (if i < 146 then (if i < 131 then (if i < 124 then (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 122 then (if i < 121 then b 120 else b 121) else (if i < 123 then b 122 else b 123))) else (if i < 127 then (if i < 125 then b 124 else (if i < 126 then b 125 else b 126)) else (if i < 129 then (if i < 128 then b 127 else b 128) else (if i < 130 then b 129 else b 130)))) else (if i < 138 then (if i < 134 then (if i < 132 then b 131 else (if i < 133 then b 132 else b 133)) else (if i < 136 then (if i < 135 then b 134 else b 135) else (if i < 137 then b 136 else b 137))) else (if i < 142 then (if i < 140 then (if i < 139 then b 138 else b 139) else (if i < 141 then b 140 else b 141)) else (if i < 144 then (if i < 143 then b 142 else b 143) else (if i < 145 then b 144 else b 145))))) else (if i < 160 then (if i < 153 then (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 151 then (if i < 150 then b 149 else b 150) else (if i < 152 then b 151 else b 152))) else (if i < 156 then (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)) else (if i < 158 then (if i < 157 then b 156 else b 157) else (if i < 159 then b 158 else b 159)))) else (if i < 167 then (if i < 163 then (if i < 161 then b 160 else (if i < 162 then b 161 else b 162)) else (if i < 165 then (if i < 164 then b 163 else b 164) else (if i < 166 then b 165 else b 166))) else (if i < 171 then (if i < 169 then (if i < 168 then b 167 else b 168) else (if i < 170 then b 169 else b 170)) else (if i < 173 then (if i < 172 then b 171 else b 172) else (if i < 174 then b 173 else b 174)))))) else (if i < 204 then (if i < 189 then (if i < 182 then (if i < 178 then (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)) else (if i < 180 then (if i < 179 then b 178 else b 179) else (if i < 181 then b 180 else b 181))) else (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 187 then (if i < 186 then b 185 else b 186) else (if i < 188 then b 187 else b 188)))) else (if i < 196 then (if i < 192 then (if i < 190 then b 189 else (if i < 191 then b 190 else b 191)) else (if i < 194 then (if i < 193 then b 192 else b 193) else (if i < 195 then b 194 else b 195))) else (if i < 200 then (if i < 198 then (if i < 197 then b 196 else b 197) else (if i < 199 then b 198 else b 199)) else (if i < 202 then (if i < 201 then b 200 else b 201) else (if i < 203 then b 202 else b 203))))) else (if i < 219 then (if i < 211 then (if i < 207 then (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)) else (if i < 209 then (if i < 208 then b 207 else b 208) else (if i < 210 then b 209 else b 210))) else (if i < 215 then (if i < 213 then (if i < 212 then b 211 else b 212) else (if i < 214 then b 213 else b 214)) else (if i < 217 then (if i < 216 then b 215 else b 216) else (if i < 218 then b 217 else b 218)))) else (if i < 226 then (if i < 222 then (if i < 220 then b 219 else (if i < 221 then b 220 else b 221)) else (if i < 224 then (if i < 223 then b 222 else b 223) else (if i < 225 then b 224 else b 225))) else (if i < 230 then (if i < 228 then (if i < 227 then b 226 else b 227) else (if i < 229 then b 228 else b 229)) else (if i < 232 then (if i < 231 then b 230 else b 231) else (if i < 233 then b 232 else b 233)))))))) else (if i < 351 then (if i < 292 then (if i < 263 then (if i < 248 then (if i < 241 then (if i < 237 then (if i < 235 then b 234 else (if i < 236 then b 235 else b 236)) else (if i < 239 then (if i < 238 then b 237 else b 238) else (if i < 240 then b 239 else b 240))) else (if i < 244 then (if i < 242 then b 241 else (if i < 243 then b 242 else b 243)) else (if i < 246 then (if i < 245 then b 244 else b 245) else (if i < 247 then b 246 else b 247)))) else (if i < 255 then (if i < 251 then (if i < 249 then b 248 else (if i < 250 then b 249 else b 250)) else (if i < 253 then (if i < 252 then b 251 else b 252) else (if i < 254 then b 253 else b 254))) else (if i < 259 then (if i < 257 then (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b)) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))) else (if i < 261 then (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)) else (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b)))))) else (if i < 277 then (if i < 270 then (if i < 266 then (if i < 264 then decide (1 ≤ count263 b) else (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b))) else (if i < 268 then (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)))) else (if i < 273 then (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b))) else (if i < 275 then (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b)) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))))) else (if i < 284 then (if i < 280 then (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))) else (if i < 282 then (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)) else (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)))) else (if i < 288 then (if i < 286 then (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))) else (if i < 290 then (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b))))))) else (if i < 321 then (if i < 306 then (if i < 299 then (if i < 295 then (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))) else (if i < 297 then (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b)) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))) else (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b))))) else (if i < 313 then (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))) else (if i < 317 then (if i < 315 then (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b)) else (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b))) else (if i < 319 then (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)))))) else (if i < 336 then (if i < 328 then (if i < 324 then (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b))) else (if i < 326 then (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b)) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b)))) else (if i < 332 then (if i < 330 then (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))) else (if i < 334 then (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))))) else (if i < 343 then (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))) else (if i < 347 then (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b))) else (if i < 349 then (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b)) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b)))))))) else (if i < 409 then (if i < 380 then (if i < 365 then (if i < 358 then (if i < 354 then (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))) else (if i < 356 then (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b)) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b)))) else (if i < 361 then (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))) else (if i < 363 then (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b))))) else (if i < 372 then (if i < 368 then (if i < 366 then decide (1 ≤ count365 b) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))) else (if i < 370 then (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b)) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)))) else (if i < 376 then (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b))) else (if i < 378 then (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)))))) else (if i < 394 then (if i < 387 then (if i < 383 then (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b))) else (if i < 385 then (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)))) else (if i < 390 then (if i < 388 then decide (1 ≤ count387 b) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b))) else (if i < 392 then (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b)) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))))) else (if i < 401 then (if i < 397 then (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))) else (if i < 399 then (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b)) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)))) else (if i < 405 then (if i < 403 then (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b)) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b))) else (if i < 407 then (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b)) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))))))) else (if i < 438 then (if i < 423 then (if i < 416 then (if i < 412 then (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b))) else (if i < 414 then (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b)) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)))) else (if i < 419 then (if i < 417 then decide (2 ≤ count415 b) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b))) else (if i < 421 then (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b)) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b))))) else (if i < 430 then (if i < 426 then (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b))) else (if i < 428 then (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b)) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b)))) else (if i < 434 then (if i < 432 then (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))) else (if i < 436 then (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b)) else (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b)))))) else (if i < 453 then (if i < 445 then (if i < 441 then (if i < 439 then decide (2 ≤ count437 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b))) else (if i < 443 then (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b)) else (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b)))) else (if i < 449 then (if i < 447 then (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b)) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b))) else (if i < 451 then (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))))) else (if i < 460 then (if i < 456 then (if i < 454 then decide (1 ≤ count453 b) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b))) else (if i < 458 then (if i < 457 then decide (2 ≤ count455 b) else decide (1 ≤ count457 b)) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b)))) else (if i < 464 then (if i < 462 then (if i < 461 then decide (2 ≤ count459 b) else decide (1 ≤ count461 b)) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b))) else (if i < 466 then (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b)) else (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b)))))))))) else (if i < 702 then (if i < 585 then (if i < 526 then (if i < 497 then (if i < 482 then (if i < 475 then (if i < 471 then (if i < 469 then decide (2 ≤ count467 b) else (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b))) else (if i < 473 then (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b)) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)))) else (if i < 478 then (if i < 476 then decide (1 ≤ count475 b) else (if i < 477 then decide (2 ≤ count475 b) else decide (1 ≤ count477 b))) else (if i < 480 then (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b)) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b))))) else (if i < 489 then (if i < 485 then (if i < 483 then decide (2 ≤ count481 b) else (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b))) else (if i < 487 then (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b)) else (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b)))) else (if i < 493 then (if i < 491 then (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b)) else (if i < 492 then decide (1 ≤ count491 b) else decide (2 ≤ count491 b))) else (if i < 495 then (if i < 494 then decide (1 ≤ count493 b) else decide (2 ≤ count493 b)) else (if i < 496 then decide (1 ≤ count495 b) else decide (2 ≤ count495 b)))))) else (if i < 511 then (if i < 504 then (if i < 500 then (if i < 498 then decide (1 ≤ count497 b) else (if i < 499 then decide (2 ≤ count497 b) else decide (1 ≤ count499 b))) else (if i < 502 then (if i < 501 then decide (2 ≤ count499 b) else decide (1 ≤ count501 b)) else (if i < 503 then decide (2 ≤ count501 b) else decide (1 ≤ count503 b)))) else (if i < 507 then (if i < 505 then decide (2 ≤ count503 b) else (if i < 506 then decide (1 ≤ count505 b) else decide (2 ≤ count505 b))) else (if i < 509 then (if i < 508 then decide (1 ≤ count507 b) else decide (2 ≤ count507 b)) else (if i < 510 then decide (3 ≤ count507 b) else decide (1 ≤ count510 b))))) else (if i < 518 then (if i < 514 then (if i < 512 then decide (2 ≤ count510 b) else (if i < 513 then decide (1 ≤ count512 b) else decide (2 ≤ count512 b))) else (if i < 516 then (if i < 515 then decide (1 ≤ count514 b) else decide (2 ≤ count514 b)) else (if i < 517 then decide (3 ≤ count514 b) else decide (4 ≤ count514 b)))) else (if i < 522 then (if i < 520 then (if i < 519 then decide (1 ≤ count518 b) else decide (2 ≤ count518 b)) else (if i < 521 then decide (3 ≤ count518 b) else decide (4 ≤ count518 b))) else (if i < 524 then (if i < 523 then decide (5 ≤ count518 b) else decide (6 ≤ count518 b)) else (if i < 525 then decide (7 ≤ count518 b) else decide (1 ≤ count525 b))))))) else (if i < 555 then (if i < 540 then (if i < 533 then (if i < 529 then (if i < 527 then decide (2 ≤ count525 b) else (if i < 528 then decide (1 ≤ count527 b) else decide (2 ≤ count527 b))) else (if i < 531 then (if i < 530 then decide (1 ≤ count529 b) else decide (2 ≤ count529 b)) else (if i < 532 then decide (3 ≤ count529 b) else decide (4 ≤ count529 b)))) else (if i < 536 then (if i < 534 then decide (1 ≤ count533 b) else (if i < 535 then decide (2 ≤ count533 b) else decide (1 ≤ count535 b))) else (if i < 538 then (if i < 537 then decide (2 ≤ count535 b) else decide (1 ≤ count537 b)) else (if i < 539 then decide (2 ≤ count537 b) else decide (3 ≤ count537 b))))) else (if i < 547 then (if i < 543 then (if i < 541 then decide (4 ≤ count537 b) else (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b))) else (if i < 545 then (if i < 544 then decide (3 ≤ count541 b) else decide (4 ≤ count541 b)) else (if i < 546 then decide (5 ≤ count541 b) else decide (6 ≤ count541 b)))) else (if i < 551 then (if i < 549 then (if i < 548 then decide (7 ≤ count541 b) else decide (8 ≤ count541 b)) else (if i < 550 then decide (1 ≤ count549 b) else decide (2 ≤ count549 b))) else (if i < 553 then (if i < 552 then decide (3 ≤ count549 b) else decide (4 ≤ count549 b)) else (if i < 554 then decide (5 ≤ count549 b) else decide (6 ≤ count549 b)))))) else (if i < 570 then (if i < 562 then (if i < 558 then (if i < 556 then decide (7 ≤ count549 b) else (if i < 557 then decide (8 ≤ count549 b) else decide (9 ≤ count549 b))) else (if i < 560 then (if i < 559 then decide (10 ≤ count549 b) else decide (11 ≤ count549 b)) else (if i < 561 then decide (12 ≤ count549 b) else decide (13 ≤ count549 b)))) else (if i < 566 then (if i < 564 then (if i < 563 then decide (14 ≤ count549 b) else decide (15 ≤ count549 b)) else (if i < 565 then decide (1 ≤ count564 b) else decide (2 ≤ count564 b))) else (if i < 568 then (if i < 567 then decide (1 ≤ count566 b) else decide (2 ≤ count566 b)) else (if i < 569 then decide (3 ≤ count566 b) else decide (1 ≤ count569 b))))) else (if i < 577 then (if i < 573 then (if i < 571 then decide (2 ≤ count569 b) else (if i < 572 then decide (1 ≤ count571 b) else decide (2 ≤ count571 b))) else (if i < 575 then (if i < 574 then decide (1 ≤ count573 b) else decide (2 ≤ count573 b)) else (if i < 576 then decide (3 ≤ count573 b) else decide (4 ≤ count573 b)))) else (if i < 581 then (if i < 579 then (if i < 578 then decide (1 ≤ count577 b) else decide (2 ≤ count577 b)) else (if i < 580 then decide (3 ≤ count577 b) else decide (4 ≤ count577 b))) else (if i < 583 then (if i < 582 then decide (5 ≤ count577 b) else decide (6 ≤ count577 b)) else (if i < 584 then decide (7 ≤ count577 b) else decide (1 ≤ count584 b)))))))) else (if i < 643 then (if i < 614 then (if i < 599 then (if i < 592 then (if i < 588 then (if i < 586 then decide (2 ≤ count584 b) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b))) else (if i < 590 then (if i < 589 then decide (1 ≤ count588 b) else decide (2 ≤ count588 b)) else (if i < 591 then decide (3 ≤ count588 b) else decide (4 ≤ count588 b)))) else (if i < 595 then (if i < 593 then decide (1 ≤ count592 b) else (if i < 594 then decide (2 ≤ count592 b) else decide (1 ≤ count594 b))) else (if i < 597 then (if i < 596 then decide (2 ≤ count594 b) else decide (1 ≤ count596 b)) else (if i < 598 then decide (2 ≤ count596 b) else decide (3 ≤ count596 b))))) else (if i < 606 then (if i < 602 then (if i < 600 then decide (4 ≤ count596 b) else (if i < 601 then decide (1 ≤ count600 b) else decide (2 ≤ count600 b))) else (if i < 604 then (if i < 603 then decide (3 ≤ count600 b) else decide (4 ≤ count600 b)) else (if i < 605 then decide (5 ≤ count600 b) else decide (6 ≤ count600 b)))) else (if i < 610 then (if i < 608 then (if i < 607 then decide (7 ≤ count600 b) else decide (8 ≤ count600 b)) else (if i < 609 then decide (1 ≤ count608 b) else decide (2 ≤ count608 b))) else (if i < 612 then (if i < 611 then decide (3 ≤ count608 b) else decide (4 ≤ count608 b)) else (if i < 613 then decide (5 ≤ count608 b) else decide (6 ≤ count608 b)))))) else (if i < 628 then (if i < 621 then (if i < 617 then (if i < 615 then decide (7 ≤ count608 b) else (if i < 616 then decide (8 ≤ count608 b) else decide (9 ≤ count608 b))) else (if i < 619 then (if i < 618 then decide (10 ≤ count608 b) else decide (11 ≤ count608 b)) else (if i < 620 then decide (12 ≤ count608 b) else decide (13 ≤ count608 b)))) else (if i < 624 then (if i < 622 then decide (14 ≤ count608 b) else (if i < 623 then decide (15 ≤ count608 b) else decide (1 ≤ count623 b))) else (if i < 626 then (if i < 625 then decide (2 ≤ count623 b) else decide (3 ≤ count623 b)) else (if i < 627 then decide (4 ≤ count623 b) else decide (5 ≤ count623 b))))) else (if i < 635 then (if i < 631 then (if i < 629 then decide (6 ≤ count623 b) else (if i < 630 then decide (7 ≤ count623 b) else decide (8 ≤ count623 b))) else (if i < 633 then (if i < 632 then decide (9 ≤ count623 b) else decide (10 ≤ count623 b)) else (if i < 634 then decide (11 ≤ count623 b) else decide (12 ≤ count623 b)))) else (if i < 639 then (if i < 637 then (if i < 636 then decide (13 ≤ count623 b) else decide (14 ≤ count623 b)) else (if i < 638 then decide (15 ≤ count623 b) else decide (16 ≤ count623 b))) else (if i < 641 then (if i < 640 then decide (17 ≤ count623 b) else decide (18 ≤ count623 b)) else (if i < 642 then decide (19 ≤ count623 b) else decide (20 ≤ count623 b))))))) else (if i < 672 then (if i < 657 then (if i < 650 then (if i < 646 then (if i < 644 then decide (21 ≤ count623 b) else (if i < 645 then decide (22 ≤ count623 b) else decide (23 ≤ count623 b))) else (if i < 648 then (if i < 647 then decide (24 ≤ count623 b) else decide (25 ≤ count623 b)) else (if i < 649 then decide (26 ≤ count623 b) else decide (27 ≤ count623 b)))) else (if i < 653 then (if i < 651 then decide (28 ≤ count623 b) else (if i < 652 then decide (29 ≤ count623 b) else decide (30 ≤ count623 b))) else (if i < 655 then (if i < 654 then decide (1 ≤ count653 b) else decide (2 ≤ count653 b)) else (if i < 656 then decide (1 ≤ count655 b) else decide (2 ≤ count655 b))))) else (if i < 664 then (if i < 660 then (if i < 658 then decide (3 ≤ count655 b) else (if i < 659 then decide (1 ≤ count658 b) else decide (2 ≤ count658 b))) else (if i < 662 then (if i < 661 then decide (1 ≤ count660 b) else decide (2 ≤ count660 b)) else (if i < 663 then decide (1 ≤ count662 b) else decide (2 ≤ count662 b)))) else (if i < 668 then (if i < 666 then (if i < 665 then decide (3 ≤ count662 b) else decide (4 ≤ count662 b)) else (if i < 667 then decide (1 ≤ count666 b) else decide (2 ≤ count666 b))) else (if i < 670 then (if i < 669 then decide (3 ≤ count666 b) else decide (4 ≤ count666 b)) else (if i < 671 then decide (5 ≤ count666 b) else decide (6 ≤ count666 b)))))) else (if i < 687 then (if i < 679 then (if i < 675 then (if i < 673 then decide (7 ≤ count666 b) else (if i < 674 then decide (1 ≤ count673 b) else decide (2 ≤ count673 b))) else (if i < 677 then (if i < 676 then decide (1 ≤ count675 b) else decide (2 ≤ count675 b)) else (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b)))) else (if i < 683 then (if i < 681 then (if i < 680 then decide (3 ≤ count677 b) else decide (4 ≤ count677 b)) else (if i < 682 then decide (1 ≤ count681 b) else decide (2 ≤ count681 b))) else (if i < 685 then (if i < 684 then decide (1 ≤ count683 b) else decide (2 ≤ count683 b)) else (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b))))) else (if i < 694 then (if i < 690 then (if i < 688 then decide (3 ≤ count685 b) else (if i < 689 then decide (4 ≤ count685 b) else decide (1 ≤ count689 b))) else (if i < 692 then (if i < 691 then decide (2 ≤ count689 b) else decide (3 ≤ count689 b)) else (if i < 693 then decide (4 ≤ count689 b) else decide (5 ≤ count689 b)))) else (if i < 698 then (if i < 696 then (if i < 695 then decide (6 ≤ count689 b) else decide (7 ≤ count689 b)) else (if i < 697 then decide (8 ≤ count689 b) else decide (1 ≤ count697 b))) else (if i < 700 then (if i < 699 then decide (2 ≤ count697 b) else decide (3 ≤ count697 b)) else (if i < 701 then decide (4 ≤ count697 b) else decide (5 ≤ count697 b))))))))) else (if i < 819 then (if i < 760 then (if i < 731 then (if i < 716 then (if i < 709 then (if i < 705 then (if i < 703 then decide (6 ≤ count697 b) else (if i < 704 then decide (7 ≤ count697 b) else decide (8 ≤ count697 b))) else (if i < 707 then (if i < 706 then decide (9 ≤ count697 b) else decide (10 ≤ count697 b)) else (if i < 708 then decide (11 ≤ count697 b) else decide (12 ≤ count697 b)))) else (if i < 712 then (if i < 710 then decide (13 ≤ count697 b) else (if i < 711 then decide (14 ≤ count697 b) else decide (15 ≤ count697 b))) else (if i < 714 then (if i < 713 then decide (1 ≤ count712 b) else decide (2 ≤ count712 b)) else (if i < 715 then decide (1 ≤ count714 b) else decide (2 ≤ count714 b))))) else (if i < 723 then (if i < 719 then (if i < 717 then decide (1 ≤ count716 b) else (if i < 718 then decide (2 ≤ count716 b) else decide (3 ≤ count716 b))) else (if i < 721 then (if i < 720 then decide (4 ≤ count716 b) else decide (1 ≤ count720 b)) else (if i < 722 then decide (2 ≤ count720 b) else decide (1 ≤ count722 b)))) else (if i < 727 then (if i < 725 then (if i < 724 then decide (2 ≤ count722 b) else decide (1 ≤ count724 b)) else (if i < 726 then decide (2 ≤ count724 b) else decide (3 ≤ count724 b))) else (if i < 729 then (if i < 728 then decide (4 ≤ count724 b) else decide (1 ≤ count728 b)) else (if i < 730 then decide (2 ≤ count728 b) else decide (3 ≤ count728 b)))))) else (if i < 745 then (if i < 738 then (if i < 734 then (if i < 732 then decide (4 ≤ count728 b) else (if i < 733 then decide (5 ≤ count728 b) else decide (6 ≤ count728 b))) else (if i < 736 then (if i < 735 then decide (7 ≤ count728 b) else decide (8 ≤ count728 b)) else (if i < 737 then decide (1 ≤ count736 b) else decide (2 ≤ count736 b)))) else (if i < 741 then (if i < 739 then decide (1 ≤ count738 b) else (if i < 740 then decide (2 ≤ count738 b) else decide (1 ≤ count740 b))) else (if i < 743 then (if i < 742 then decide (2 ≤ count740 b) else decide (3 ≤ count740 b)) else (if i < 744 then decide (4 ≤ count740 b) else decide (1 ≤ count744 b))))) else (if i < 752 then (if i < 748 then (if i < 746 then decide (2 ≤ count744 b) else (if i < 747 then decide (1 ≤ count746 b) else decide (2 ≤ count746 b))) else (if i < 750 then (if i < 749 then decide (1 ≤ count748 b) else decide (2 ≤ count748 b)) else (if i < 751 then decide (3 ≤ count748 b) else decide (4 ≤ count748 b)))) else (if i < 756 then (if i < 754 then (if i < 753 then decide (1 ≤ count752 b) else decide (2 ≤ count752 b)) else (if i < 755 then decide (3 ≤ count752 b) else decide (4 ≤ count752 b))) else (if i < 758 then (if i < 757 then decide (5 ≤ count752 b) else decide (6 ≤ count752 b)) else (if i < 759 then decide (7 ≤ count752 b) else decide (8 ≤ count752 b))))))) else (if i < 789 then (if i < 774 then (if i < 767 then (if i < 763 then (if i < 761 then decide (1 ≤ count760 b) else (if i < 762 then decide (2 ≤ count760 b) else decide (3 ≤ count760 b))) else (if i < 765 then (if i < 764 then decide (4 ≤ count760 b) else decide (5 ≤ count760 b)) else (if i < 766 then decide (6 ≤ count760 b) else decide (7 ≤ count760 b)))) else (if i < 770 then (if i < 768 then decide (8 ≤ count760 b) else (if i < 769 then decide (9 ≤ count760 b) else decide (10 ≤ count760 b))) else (if i < 772 then (if i < 771 then decide (11 ≤ count760 b) else decide (12 ≤ count760 b)) else (if i < 773 then decide (13 ≤ count760 b) else decide (14 ≤ count760 b))))) else (if i < 781 then (if i < 777 then (if i < 775 then decide (15 ≤ count760 b) else (if i < 776 then decide (16 ≤ count760 b) else decide (1 ≤ count776 b))) else (if i < 779 then (if i < 778 then decide (2 ≤ count776 b) else decide (3 ≤ count776 b)) else (if i < 780 then decide (4 ≤ count776 b) else decide (5 ≤ count776 b)))) else (if i < 785 then (if i < 783 then (if i < 782 then decide (6 ≤ count776 b) else decide (7 ≤ count776 b)) else (if i < 784 then decide (8 ≤ count776 b) else decide (9 ≤ count776 b))) else (if i < 787 then (if i < 786 then decide (10 ≤ count776 b) else decide (11 ≤ count776 b)) else (if i < 788 then decide (12 ≤ count776 b) else decide (13 ≤ count776 b)))))) else (if i < 804 then (if i < 796 then (if i < 792 then (if i < 790 then decide (14 ≤ count776 b) else (if i < 791 then decide (15 ≤ count776 b) else decide (16 ≤ count776 b))) else (if i < 794 then (if i < 793 then decide (17 ≤ count776 b) else decide (18 ≤ count776 b)) else (if i < 795 then decide (19 ≤ count776 b) else decide (20 ≤ count776 b)))) else (if i < 800 then (if i < 798 then (if i < 797 then decide (21 ≤ count776 b) else decide (22 ≤ count776 b)) else (if i < 799 then decide (23 ≤ count776 b) else decide (24 ≤ count776 b))) else (if i < 802 then (if i < 801 then decide (25 ≤ count776 b) else decide (26 ≤ count776 b)) else (if i < 803 then decide (27 ≤ count776 b) else decide (28 ≤ count776 b))))) else (if i < 811 then (if i < 807 then (if i < 805 then decide (29 ≤ count776 b) else (if i < 806 then decide (30 ≤ count776 b) else decide (31 ≤ count776 b))) else (if i < 809 then (if i < 808 then decide (1 ≤ count807 b) else decide (2 ≤ count807 b)) else (if i < 810 then decide (3 ≤ count807 b) else decide (4 ≤ count807 b)))) else (if i < 815 then (if i < 813 then (if i < 812 then decide (5 ≤ count807 b) else decide (6 ≤ count807 b)) else (if i < 814 then decide (7 ≤ count807 b) else decide (8 ≤ count807 b))) else (if i < 817 then (if i < 816 then decide (9 ≤ count807 b) else decide (10 ≤ count807 b)) else (if i < 818 then decide (11 ≤ count807 b) else decide (12 ≤ count807 b)))))))) else (if i < 878 then (if i < 848 then (if i < 833 then (if i < 826 then (if i < 822 then (if i < 820 then decide (13 ≤ count807 b) else (if i < 821 then decide (14 ≤ count807 b) else decide (15 ≤ count807 b))) else (if i < 824 then (if i < 823 then decide (16 ≤ count807 b) else decide (17 ≤ count807 b)) else (if i < 825 then decide (18 ≤ count807 b) else decide (19 ≤ count807 b)))) else (if i < 829 then (if i < 827 then decide (20 ≤ count807 b) else (if i < 828 then decide (21 ≤ count807 b) else decide (22 ≤ count807 b))) else (if i < 831 then (if i < 830 then decide (23 ≤ count807 b) else decide (24 ≤ count807 b)) else (if i < 832 then decide (25 ≤ count807 b) else decide (26 ≤ count807 b))))) else (if i < 840 then (if i < 836 then (if i < 834 then decide (27 ≤ count807 b) else (if i < 835 then decide (28 ≤ count807 b) else decide (29 ≤ count807 b))) else (if i < 838 then (if i < 837 then decide (30 ≤ count807 b) else decide (31 ≤ count807 b)) else (if i < 839 then decide (32 ≤ count807 b) else decide (33 ≤ count807 b)))) else (if i < 844 then (if i < 842 then (if i < 841 then decide (34 ≤ count807 b) else decide (35 ≤ count807 b)) else (if i < 843 then decide (36 ≤ count807 b) else decide (37 ≤ count807 b))) else (if i < 846 then (if i < 845 then decide (38 ≤ count807 b) else decide (39 ≤ count807 b)) else (if i < 847 then decide (40 ≤ count807 b) else decide (41 ≤ count807 b)))))) else (if i < 863 then (if i < 855 then (if i < 851 then (if i < 849 then decide (42 ≤ count807 b) else (if i < 850 then decide (1 ≤ count849 b) else decide (2 ≤ count849 b))) else (if i < 853 then (if i < 852 then decide (1 ≤ count851 b) else decide (2 ≤ count851 b)) else (if i < 854 then decide (3 ≤ count851 b) else decide (1 ≤ count854 b)))) else (if i < 859 then (if i < 857 then (if i < 856 then decide (2 ≤ count854 b) else decide (1 ≤ count856 b)) else (if i < 858 then decide (2 ≤ count856 b) else decide (1 ≤ count858 b))) else (if i < 861 then (if i < 860 then decide (2 ≤ count858 b) else decide (3 ≤ count858 b)) else (if i < 862 then decide (4 ≤ count858 b) else decide (1 ≤ count862 b))))) else (if i < 870 then (if i < 866 then (if i < 864 then decide (2 ≤ count862 b) else (if i < 865 then decide (3 ≤ count862 b) else decide (4 ≤ count862 b))) else (if i < 868 then (if i < 867 then decide (5 ≤ count862 b) else decide (6 ≤ count862 b)) else (if i < 869 then decide (7 ≤ count862 b) else decide (1 ≤ count869 b)))) else (if i < 874 then (if i < 872 then (if i < 871 then decide (2 ≤ count869 b) else decide (1 ≤ count871 b)) else (if i < 873 then decide (2 ≤ count871 b) else decide (1 ≤ count873 b))) else (if i < 876 then (if i < 875 then decide (2 ≤ count873 b) else decide (3 ≤ count873 b)) else (if i < 877 then decide (4 ≤ count873 b) else decide (1 ≤ count877 b))))))) else (if i < 907 then (if i < 892 then (if i < 885 then (if i < 881 then (if i < 879 then decide (2 ≤ count877 b) else (if i < 880 then decide (1 ≤ count879 b) else decide (2 ≤ count879 b))) else (if i < 883 then (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b)) else (if i < 884 then decide (3 ≤ count881 b) else decide (4 ≤ count881 b)))) else (if i < 888 then (if i < 886 then decide (1 ≤ count885 b) else (if i < 887 then decide (2 ≤ count885 b) else decide (3 ≤ count885 b))) else (if i < 890 then (if i < 889 then decide (4 ≤ count885 b) else decide (5 ≤ count885 b)) else (if i < 891 then decide (6 ≤ count885 b) else decide (7 ≤ count885 b))))) else (if i < 899 then (if i < 895 then (if i < 893 then decide (8 ≤ count885 b) else (if i < 894 then decide (1 ≤ count893 b) else decide (2 ≤ count893 b))) else (if i < 897 then (if i < 896 then decide (3 ≤ count893 b) else decide (4 ≤ count893 b)) else (if i < 898 then decide (5 ≤ count893 b) else decide (6 ≤ count893 b)))) else (if i < 903 then (if i < 901 then (if i < 900 then decide (7 ≤ count893 b) else decide (8 ≤ count893 b)) else (if i < 902 then decide (9 ≤ count893 b) else decide (10 ≤ count893 b))) else (if i < 905 then (if i < 904 then decide (11 ≤ count893 b) else decide (12 ≤ count893 b)) else (if i < 906 then decide (13 ≤ count893 b) else decide (14 ≤ count893 b)))))) else (if i < 922 then (if i < 914 then (if i < 910 then (if i < 908 then decide (15 ≤ count893 b) else (if i < 909 then decide (1 ≤ count908 b) else decide (2 ≤ count908 b))) else (if i < 912 then (if i < 911 then decide (1 ≤ count910 b) else decide (2 ≤ count910 b)) else (if i < 913 then decide (3 ≤ count910 b) else decide (1 ≤ count913 b)))) else (if i < 918 then (if i < 916 then (if i < 915 then decide (2 ≤ count913 b) else decide (1 ≤ count915 b)) else (if i < 917 then decide (2 ≤ count915 b) else decide (1 ≤ count917 b))) else (if i < 920 then (if i < 919 then decide (2 ≤ count917 b) else decide (3 ≤ count917 b)) else (if i < 921 then decide (4 ≤ count917 b) else decide (1 ≤ count921 b))))) else (if i < 929 then (if i < 925 then (if i < 923 then decide (2 ≤ count921 b) else (if i < 924 then decide (3 ≤ count921 b) else decide (4 ≤ count921 b))) else (if i < 927 then (if i < 926 then decide (5 ≤ count921 b) else decide (6 ≤ count921 b)) else (if i < 928 then decide (7 ≤ count921 b) else decide (1 ≤ count928 b)))) else (if i < 933 then (if i < 931 then (if i < 930 then decide (2 ≤ count928 b) else decide (1 ≤ count930 b)) else (if i < 932 then decide (2 ≤ count930 b) else decide (1 ≤ count932 b))) else (if i < 935 then (if i < 934 then decide (2 ≤ count932 b) else decide (3 ≤ count932 b)) else (if i < 936 then decide (4 ≤ count932 b) else decide (1 ≤ count936 b))))))))))) else (if i < 1406 then (if i < 1171 then (if i < 1054 then (if i < 995 then (if i < 966 then (if i < 951 then (if i < 944 then (if i < 940 then (if i < 938 then decide (2 ≤ count936 b) else (if i < 939 then decide (1 ≤ count938 b) else decide (2 ≤ count938 b))) else (if i < 942 then (if i < 941 then decide (1 ≤ count940 b) else decide (2 ≤ count940 b)) else (if i < 943 then decide (3 ≤ count940 b) else decide (4 ≤ count940 b)))) else (if i < 947 then (if i < 945 then decide (1 ≤ count944 b) else (if i < 946 then decide (2 ≤ count944 b) else decide (3 ≤ count944 b))) else (if i < 949 then (if i < 948 then decide (4 ≤ count944 b) else decide (5 ≤ count944 b)) else (if i < 950 then decide (6 ≤ count944 b) else decide (7 ≤ count944 b))))) else (if i < 958 then (if i < 954 then (if i < 952 then decide (8 ≤ count944 b) else (if i < 953 then decide (1 ≤ count952 b) else decide (2 ≤ count952 b))) else (if i < 956 then (if i < 955 then decide (3 ≤ count952 b) else decide (4 ≤ count952 b)) else (if i < 957 then decide (5 ≤ count952 b) else decide (6 ≤ count952 b)))) else (if i < 962 then (if i < 960 then (if i < 959 then decide (7 ≤ count952 b) else decide (8 ≤ count952 b)) else (if i < 961 then decide (9 ≤ count952 b) else decide (10 ≤ count952 b))) else (if i < 964 then (if i < 963 then decide (11 ≤ count952 b) else decide (12 ≤ count952 b)) else (if i < 965 then decide (13 ≤ count952 b) else decide (14 ≤ count952 b)))))) else (if i < 980 then (if i < 973 then (if i < 969 then (if i < 967 then decide (15 ≤ count952 b) else (if i < 968 then decide (1 ≤ count967 b) else decide (2 ≤ count967 b))) else (if i < 971 then (if i < 970 then decide (3 ≤ count967 b) else decide (4 ≤ count967 b)) else (if i < 972 then decide (5 ≤ count967 b) else decide (6 ≤ count967 b)))) else (if i < 976 then (if i < 974 then decide (7 ≤ count967 b) else (if i < 975 then decide (8 ≤ count967 b) else decide (9 ≤ count967 b))) else (if i < 978 then (if i < 977 then decide (10 ≤ count967 b) else decide (11 ≤ count967 b)) else (if i < 979 then decide (12 ≤ count967 b) else decide (13 ≤ count967 b))))) else (if i < 987 then (if i < 983 then (if i < 981 then decide (14 ≤ count967 b) else (if i < 982 then decide (15 ≤ count967 b) else decide (16 ≤ count967 b))) else (if i < 985 then (if i < 984 then decide (17 ≤ count967 b) else decide (18 ≤ count967 b)) else (if i < 986 then decide (19 ≤ count967 b) else decide (20 ≤ count967 b)))) else (if i < 991 then (if i < 989 then (if i < 988 then decide (21 ≤ count967 b) else decide (1 ≤ count988 b)) else (if i < 990 then decide (2 ≤ count988 b) else decide (1 ≤ count990 b))) else (if i < 993 then (if i < 992 then decide (2 ≤ count990 b) else decide (3 ≤ count990 b)) else (if i < 994 then decide (1 ≤ count993 b) else decide (2 ≤ count993 b))))))) else (if i < 1024 then (if i < 1009 then (if i < 1002 then (if i < 998 then (if i < 996 then decide (1 ≤ count995 b) else (if i < 997 then decide (2 ≤ count995 b) else decide (1 ≤ count997 b))) else (if i < 1000 then (if i < 999 then decide (2 ≤ count997 b) else decide (3 ≤ count997 b)) else (if i < 1001 then decide (4 ≤ count997 b) else decide (1 ≤ count1001 b)))) else (if i < 1005 then (if i < 1003 then decide (2 ≤ count1001 b) else (if i < 1004 then decide (3 ≤ count1001 b) else decide (4 ≤ count1001 b))) else (if i < 1007 then (if i < 1006 then decide (5 ≤ count1001 b) else decide (6 ≤ count1001 b)) else (if i < 1008 then decide (7 ≤ count1001 b) else decide (1 ≤ count1008 b))))) else (if i < 1016 then (if i < 1012 then (if i < 1010 then decide (2 ≤ count1008 b) else (if i < 1011 then decide (1 ≤ count1010 b) else decide (2 ≤ count1010 b))) else (if i < 1014 then (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b)) else (if i < 1015 then decide (3 ≤ count1012 b) else decide (4 ≤ count1012 b)))) else (if i < 1020 then (if i < 1018 then (if i < 1017 then decide (1 ≤ count1016 b) else decide (2 ≤ count1016 b)) else (if i < 1019 then decide (1 ≤ count1018 b) else decide (2 ≤ count1018 b))) else (if i < 1022 then (if i < 1021 then decide (1 ≤ count1020 b) else decide (2 ≤ count1020 b)) else (if i < 1023 then decide (3 ≤ count1020 b) else decide (4 ≤ count1020 b)))))) else (if i < 1039 then (if i < 1031 then (if i < 1027 then (if i < 1025 then decide (1 ≤ count1024 b) else (if i < 1026 then decide (2 ≤ count1024 b) else decide (3 ≤ count1024 b))) else (if i < 1029 then (if i < 1028 then decide (4 ≤ count1024 b) else decide (5 ≤ count1024 b)) else (if i < 1030 then decide (6 ≤ count1024 b) else decide (7 ≤ count1024 b)))) else (if i < 1035 then (if i < 1033 then (if i < 1032 then decide (8 ≤ count1024 b) else decide (1 ≤ count1032 b)) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (3 ≤ count1032 b))) else (if i < 1037 then (if i < 1036 then decide (4 ≤ count1032 b) else decide (5 ≤ count1032 b)) else (if i < 1038 then decide (6 ≤ count1032 b) else decide (7 ≤ count1032 b))))) else (if i < 1046 then (if i < 1042 then (if i < 1040 then decide (8 ≤ count1032 b) else (if i < 1041 then decide (9 ≤ count1032 b) else decide (10 ≤ count1032 b))) else (if i < 1044 then (if i < 1043 then decide (11 ≤ count1032 b) else decide (12 ≤ count1032 b)) else (if i < 1045 then decide (13 ≤ count1032 b) else decide (14 ≤ count1032 b)))) else (if i < 1050 then (if i < 1048 then (if i < 1047 then decide (15 ≤ count1032 b) else decide (1 ≤ count1047 b)) else (if i < 1049 then decide (2 ≤ count1047 b) else decide (1 ≤ count1049 b))) else (if i < 1052 then (if i < 1051 then decide (2 ≤ count1049 b) else decide (1 ≤ count1051 b)) else (if i < 1053 then decide (2 ≤ count1051 b) else decide (3 ≤ count1051 b)))))))) else (if i < 1112 then (if i < 1083 then (if i < 1068 then (if i < 1061 then (if i < 1057 then (if i < 1055 then decide (4 ≤ count1051 b) else (if i < 1056 then decide (1 ≤ count1055 b) else decide (2 ≤ count1055 b))) else (if i < 1059 then (if i < 1058 then decide (1 ≤ count1057 b) else decide (2 ≤ count1057 b)) else (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b)))) else (if i < 1064 then (if i < 1062 then decide (3 ≤ count1059 b) else (if i < 1063 then decide (4 ≤ count1059 b) else decide (1 ≤ count1063 b))) else (if i < 1066 then (if i < 1065 then decide (2 ≤ count1063 b) else decide (3 ≤ count1063 b)) else (if i < 1067 then decide (4 ≤ count1063 b) else decide (5 ≤ count1063 b))))) else (if i < 1075 then (if i < 1071 then (if i < 1069 then decide (6 ≤ count1063 b) else (if i < 1070 then decide (7 ≤ count1063 b) else decide (8 ≤ count1063 b))) else (if i < 1073 then (if i < 1072 then decide (1 ≤ count1071 b) else decide (2 ≤ count1071 b)) else (if i < 1074 then decide (1 ≤ count1073 b) else decide (2 ≤ count1073 b)))) else (if i < 1079 then (if i < 1077 then (if i < 1076 then decide (1 ≤ count1075 b) else decide (2 ≤ count1075 b)) else (if i < 1078 then decide (3 ≤ count1075 b) else decide (4 ≤ count1075 b))) else (if i < 1081 then (if i < 1080 then decide (1 ≤ count1079 b) else decide (2 ≤ count1079 b)) else (if i < 1082 then decide (1 ≤ count1081 b) else decide (2 ≤ count1081 b)))))) else (if i < 1097 then (if i < 1090 then (if i < 1086 then (if i < 1084 then decide (1 ≤ count1083 b) else (if i < 1085 then decide (2 ≤ count1083 b) else decide (3 ≤ count1083 b))) else (if i < 1088 then (if i < 1087 then decide (4 ≤ count1083 b) else decide (1 ≤ count1087 b)) else (if i < 1089 then decide (2 ≤ count1087 b) else decide (3 ≤ count1087 b)))) else (if i < 1093 then (if i < 1091 then decide (4 ≤ count1087 b) else (if i < 1092 then decide (5 ≤ count1087 b) else decide (6 ≤ count1087 b))) else (if i < 1095 then (if i < 1094 then decide (7 ≤ count1087 b) else decide (8 ≤ count1087 b)) else (if i < 1096 then decide (1 ≤ count1095 b) else decide (2 ≤ count1095 b))))) else (if i < 1104 then (if i < 1100 then (if i < 1098 then decide (3 ≤ count1095 b) else (if i < 1099 then decide (4 ≤ count1095 b) else decide (5 ≤ count1095 b))) else (if i < 1102 then (if i < 1101 then decide (6 ≤ count1095 b) else decide (7 ≤ count1095 b)) else (if i < 1103 then decide (8 ≤ count1095 b) else decide (9 ≤ count1095 b)))) else (if i < 1108 then (if i < 1106 then (if i < 1105 then decide (10 ≤ count1095 b) else decide (11 ≤ count1095 b)) else (if i < 1107 then decide (12 ≤ count1095 b) else decide (13 ≤ count1095 b))) else (if i < 1110 then (if i < 1109 then decide (14 ≤ count1095 b) else decide (15 ≤ count1095 b)) else (if i < 1111 then decide (16 ≤ count1095 b) else decide (1 ≤ count1111 b))))))) else (if i < 1141 then (if i < 1126 then (if i < 1119 then (if i < 1115 then (if i < 1113 then decide (2 ≤ count1111 b) else (if i < 1114 then decide (3 ≤ count1111 b) else decide (4 ≤ count1111 b))) else (if i < 1117 then (if i < 1116 then decide (5 ≤ count1111 b) else decide (6 ≤ count1111 b)) else (if i < 1118 then decide (7 ≤ count1111 b) else decide (8 ≤ count1111 b)))) else (if i < 1122 then (if i < 1120 then decide (9 ≤ count1111 b) else (if i < 1121 then decide (10 ≤ count1111 b) else decide (11 ≤ count1111 b))) else (if i < 1124 then (if i < 1123 then decide (12 ≤ count1111 b) else decide (13 ≤ count1111 b)) else (if i < 1125 then decide (14 ≤ count1111 b) else decide (15 ≤ count1111 b))))) else (if i < 1133 then (if i < 1129 then (if i < 1127 then decide (16 ≤ count1111 b) else (if i < 1128 then decide (17 ≤ count1111 b) else decide (18 ≤ count1111 b))) else (if i < 1131 then (if i < 1130 then decide (19 ≤ count1111 b) else decide (20 ≤ count1111 b)) else (if i < 1132 then decide (21 ≤ count1111 b) else decide (1 ≤ count1132 b)))) else (if i < 1137 then (if i < 1135 then (if i < 1134 then decide (2 ≤ count1132 b) else decide (3 ≤ count1132 b)) else (if i < 1136 then decide (4 ≤ count1132 b) else decide (5 ≤ count1132 b))) else (if i < 1139 then (if i < 1138 then decide (6 ≤ count1132 b) else decide (7 ≤ count1132 b)) else (if i < 1140 then decide (8 ≤ count1132 b) else decide (9 ≤ count1132 b)))))) else (if i < 1156 then (if i < 1148 then (if i < 1144 then (if i < 1142 then decide (10 ≤ count1132 b) else (if i < 1143 then decide (11 ≤ count1132 b) else decide (12 ≤ count1132 b))) else (if i < 1146 then (if i < 1145 then decide (13 ≤ count1132 b) else decide (14 ≤ count1132 b)) else (if i < 1147 then decide (15 ≤ count1132 b) else decide (16 ≤ count1132 b)))) else (if i < 1152 then (if i < 1150 then (if i < 1149 then decide (17 ≤ count1132 b) else decide (18 ≤ count1132 b)) else (if i < 1151 then decide (19 ≤ count1132 b) else decide (20 ≤ count1132 b))) else (if i < 1154 then (if i < 1153 then decide (21 ≤ count1132 b) else decide (1 ≤ count1153 b)) else (if i < 1155 then decide (2 ≤ count1153 b) else decide (1 ≤ count1155 b))))) else (if i < 1163 then (if i < 1159 then (if i < 1157 then decide (2 ≤ count1155 b) else (if i < 1158 then decide (1 ≤ count1157 b) else decide (2 ≤ count1157 b))) else (if i < 1161 then (if i < 1160 then decide (3 ≤ count1157 b) else decide (4 ≤ count1157 b)) else (if i < 1162 then decide (1 ≤ count1161 b) else decide (2 ≤ count1161 b)))) else (if i < 1167 then (if i < 1165 then (if i < 1164 then decide (1 ≤ count1163 b) else decide (2 ≤ count1163 b)) else (if i < 1166 then decide (1 ≤ count1165 b) else decide (2 ≤ count1165 b))) else (if i < 1169 then (if i < 1168 then decide (3 ≤ count1165 b) else decide (4 ≤ count1165 b)) else (if i < 1170 then decide (1 ≤ count1169 b) else decide (2 ≤ count1169 b))))))))) else (if i < 1288 then (if i < 1229 then (if i < 1200 then (if i < 1185 then (if i < 1178 then (if i < 1174 then (if i < 1172 then decide (3 ≤ count1169 b) else (if i < 1173 then decide (4 ≤ count1169 b) else decide (5 ≤ count1169 b))) else (if i < 1176 then (if i < 1175 then decide (6 ≤ count1169 b) else decide (7 ≤ count1169 b)) else (if i < 1177 then decide (8 ≤ count1169 b) else decide (1 ≤ count1177 b)))) else (if i < 1181 then (if i < 1179 then decide (2 ≤ count1177 b) else (if i < 1180 then decide (1 ≤ count1179 b) else decide (2 ≤ count1179 b))) else (if i < 1183 then (if i < 1182 then decide (1 ≤ count1181 b) else decide (2 ≤ count1181 b)) else (if i < 1184 then decide (3 ≤ count1181 b) else decide (4 ≤ count1181 b))))) else (if i < 1192 then (if i < 1188 then (if i < 1186 then decide (1 ≤ count1185 b) else (if i < 1187 then decide (2 ≤ count1185 b) else decide (1 ≤ count1187 b))) else (if i < 1190 then (if i < 1189 then decide (2 ≤ count1187 b) else decide (1 ≤ count1189 b)) else (if i < 1191 then decide (2 ≤ count1189 b) else decide (3 ≤ count1189 b)))) else (if i < 1196 then (if i < 1194 then (if i < 1193 then decide (4 ≤ count1189 b) else decide (1 ≤ count1193 b)) else (if i < 1195 then decide (2 ≤ count1193 b) else decide (3 ≤ count1193 b))) else (if i < 1198 then (if i < 1197 then decide (4 ≤ count1193 b) else decide (5 ≤ count1193 b)) else (if i < 1199 then decide (6 ≤ count1193 b) else decide (7 ≤ count1193 b)))))) else (if i < 1214 then (if i < 1207 then (if i < 1203 then (if i < 1201 then decide (8 ≤ count1193 b) else (if i < 1202 then decide (1 ≤ count1201 b) else decide (2 ≤ count1201 b))) else (if i < 1205 then (if i < 1204 then decide (3 ≤ count1201 b) else decide (4 ≤ count1201 b)) else (if i < 1206 then decide (5 ≤ count1201 b) else decide (6 ≤ count1201 b)))) else (if i < 1210 then (if i < 1208 then decide (7 ≤ count1201 b) else (if i < 1209 then decide (8 ≤ count1201 b) else decide (9 ≤ count1201 b))) else (if i < 1212 then (if i < 1211 then decide (10 ≤ count1201 b) else decide (11 ≤ count1201 b)) else (if i < 1213 then decide (12 ≤ count1201 b) else decide (13 ≤ count1201 b))))) else (if i < 1221 then (if i < 1217 then (if i < 1215 then decide (14 ≤ count1201 b) else (if i < 1216 then decide (15 ≤ count1201 b) else decide (16 ≤ count1201 b))) else (if i < 1219 then (if i < 1218 then decide (1 ≤ count1217 b) else decide (2 ≤ count1217 b)) else (if i < 1220 then decide (1 ≤ count1219 b) else decide (2 ≤ count1219 b)))) else (if i < 1225 then (if i < 1223 then (if i < 1222 then decide (1 ≤ count1221 b) else decide (2 ≤ count1221 b)) else (if i < 1224 then decide (3 ≤ count1221 b) else decide (4 ≤ count1221 b))) else (if i < 1227 then (if i < 1226 then decide (1 ≤ count1225 b) else decide (2 ≤ count1225 b)) else (if i < 1228 then decide (1 ≤ count1227 b) else decide (2 ≤ count1227 b))))))) else (if i < 1258 then (if i < 1243 then (if i < 1236 then (if i < 1232 then (if i < 1230 then decide (1 ≤ count1229 b) else (if i < 1231 then decide (2 ≤ count1229 b) else decide (3 ≤ count1229 b))) else (if i < 1234 then (if i < 1233 then decide (4 ≤ count1229 b) else decide (1 ≤ count1233 b)) else (if i < 1235 then decide (2 ≤ count1233 b) else decide (3 ≤ count1233 b)))) else (if i < 1239 then (if i < 1237 then decide (4 ≤ count1233 b) else (if i < 1238 then decide (5 ≤ count1233 b) else decide (6 ≤ count1233 b))) else (if i < 1241 then (if i < 1240 then decide (7 ≤ count1233 b) else decide (8 ≤ count1233 b)) else (if i < 1242 then decide (1 ≤ count1241 b) else decide (2 ≤ count1241 b))))) else (if i < 1250 then (if i < 1246 then (if i < 1244 then decide (1 ≤ count1243 b) else (if i < 1245 then decide (2 ≤ count1243 b) else decide (1 ≤ count1245 b))) else (if i < 1248 then (if i < 1247 then decide (2 ≤ count1245 b) else decide (3 ≤ count1245 b)) else (if i < 1249 then decide (4 ≤ count1245 b) else decide (1 ≤ count1249 b)))) else (if i < 1254 then (if i < 1252 then (if i < 1251 then decide (2 ≤ count1249 b) else decide (1 ≤ count1251 b)) else (if i < 1253 then decide (2 ≤ count1251 b) else decide (1 ≤ count1253 b))) else (if i < 1256 then (if i < 1255 then decide (2 ≤ count1253 b) else decide (3 ≤ count1253 b)) else (if i < 1257 then decide (1 ≤ count1256 b) else decide (2 ≤ count1256 b)))))) else (if i < 1273 then (if i < 1265 then (if i < 1261 then (if i < 1259 then decide (3 ≤ count1256 b) else (if i < 1260 then decide (4 ≤ count1256 b) else decide (5 ≤ count1256 b))) else (if i < 1263 then (if i < 1262 then decide (1 ≤ count1261 b) else decide (2 ≤ count1261 b)) else (if i < 1264 then decide (3 ≤ count1261 b) else decide (4 ≤ count1261 b)))) else (if i < 1269 then (if i < 1267 then (if i < 1266 then decide (5 ≤ count1261 b) else decide (6 ≤ count1261 b)) else (if i < 1268 then decide (7 ≤ count1261 b) else decide (8 ≤ count1261 b))) else (if i < 1271 then (if i < 1270 then decide (9 ≤ count1261 b) else decide (1 ≤ count1270 b)) else (if i < 1272 then decide (2 ≤ count1270 b) else decide (3 ≤ count1270 b))))) else (if i < 1280 then (if i < 1276 then (if i < 1274 then decide (4 ≤ count1270 b) else (if i < 1275 then decide (5 ≤ count1270 b) else decide (6 ≤ count1270 b))) else (if i < 1278 then (if i < 1277 then decide (7 ≤ count1270 b) else decide (8 ≤ count1270 b)) else (if i < 1279 then decide (9 ≤ count1270 b) else decide (10 ≤ count1270 b)))) else (if i < 1284 then (if i < 1282 then (if i < 1281 then decide (11 ≤ count1270 b) else decide (12 ≤ count1270 b)) else (if i < 1283 then decide (13 ≤ count1270 b) else decide (14 ≤ count1270 b))) else (if i < 1286 then (if i < 1285 then decide (15 ≤ count1270 b) else decide (16 ≤ count1270 b)) else (if i < 1287 then decide (17 ≤ count1270 b) else decide (1 ≤ count1287 b)))))))) else (if i < 1347 then (if i < 1317 then (if i < 1302 then (if i < 1295 then (if i < 1291 then (if i < 1289 then decide (2 ≤ count1287 b) else (if i < 1290 then decide (3 ≤ count1287 b) else decide (4 ≤ count1287 b))) else (if i < 1293 then (if i < 1292 then decide (5 ≤ count1287 b) else decide (6 ≤ count1287 b)) else (if i < 1294 then decide (7 ≤ count1287 b) else decide (8 ≤ count1287 b)))) else (if i < 1298 then (if i < 1296 then decide (9 ≤ count1287 b) else (if i < 1297 then decide (10 ≤ count1287 b) else decide (11 ≤ count1287 b))) else (if i < 1300 then (if i < 1299 then decide (12 ≤ count1287 b) else decide (13 ≤ count1287 b)) else (if i < 1301 then decide (14 ≤ count1287 b) else decide (15 ≤ count1287 b))))) else (if i < 1309 then (if i < 1305 then (if i < 1303 then decide (16 ≤ count1287 b) else (if i < 1304 then decide (17 ≤ count1287 b) else decide (18 ≤ count1287 b))) else (if i < 1307 then (if i < 1306 then decide (19 ≤ count1287 b) else decide (20 ≤ count1287 b)) else (if i < 1308 then decide (21 ≤ count1287 b) else decide (22 ≤ count1287 b)))) else (if i < 1313 then (if i < 1311 then (if i < 1310 then decide (23 ≤ count1287 b) else decide (24 ≤ count1287 b)) else (if i < 1312 then decide (25 ≤ count1287 b) else decide (26 ≤ count1287 b))) else (if i < 1315 then (if i < 1314 then decide (27 ≤ count1287 b) else decide (28 ≤ count1287 b)) else (if i < 1316 then decide (29 ≤ count1287 b) else decide (30 ≤ count1287 b)))))) else (if i < 1332 then (if i < 1324 then (if i < 1320 then (if i < 1318 then decide (31 ≤ count1287 b) else (if i < 1319 then decide (32 ≤ count1287 b) else decide (33 ≤ count1287 b))) else (if i < 1322 then (if i < 1321 then decide (1 ≤ count1320 b) else decide (2 ≤ count1320 b)) else (if i < 1323 then decide (1 ≤ count1322 b) else decide (2 ≤ count1322 b)))) else (if i < 1328 then (if i < 1326 then (if i < 1325 then decide (1 ≤ count1324 b) else decide (2 ≤ count1324 b)) else (if i < 1327 then decide (3 ≤ count1324 b) else decide (4 ≤ count1324 b))) else (if i < 1330 then (if i < 1329 then decide (1 ≤ count1328 b) else decide (2 ≤ count1328 b)) else (if i < 1331 then decide (1 ≤ count1330 b) else decide (2 ≤ count1330 b))))) else (if i < 1339 then (if i < 1335 then (if i < 1333 then decide (1 ≤ count1332 b) else (if i < 1334 then decide (2 ≤ count1332 b) else decide (3 ≤ count1332 b))) else (if i < 1337 then (if i < 1336 then decide (4 ≤ count1332 b) else decide (1 ≤ count1336 b)) else (if i < 1338 then decide (2 ≤ count1336 b) else decide (3 ≤ count1336 b)))) else (if i < 1343 then (if i < 1341 then (if i < 1340 then decide (4 ≤ count1336 b) else decide (5 ≤ count1336 b)) else (if i < 1342 then decide (6 ≤ count1336 b) else decide (7 ≤ count1336 b))) else (if i < 1345 then (if i < 1344 then decide (8 ≤ count1336 b) else decide (1 ≤ count1344 b)) else (if i < 1346 then decide (2 ≤ count1344 b) else decide (1 ≤ count1346 b))))))) else (if i < 1376 then (if i < 1361 then (if i < 1354 then (if i < 1350 then (if i < 1348 then decide (2 ≤ count1346 b) else (if i < 1349 then decide (1 ≤ count1348 b) else decide (2 ≤ count1348 b))) else (if i < 1352 then (if i < 1351 then decide (3 ≤ count1348 b) else decide (4 ≤ count1348 b)) else (if i < 1353 then decide (1 ≤ count1352 b) else decide (2 ≤ count1352 b)))) else (if i < 1357 then (if i < 1355 then decide (1 ≤ count1354 b) else (if i < 1356 then decide (2 ≤ count1354 b) else decide (1 ≤ count1356 b))) else (if i < 1359 then (if i < 1358 then decide (2 ≤ count1356 b) else decide (3 ≤ count1356 b)) else (if i < 1360 then decide (4 ≤ count1356 b) else decide (1 ≤ count1360 b))))) else (if i < 1368 then (if i < 1364 then (if i < 1362 then decide (2 ≤ count1360 b) else (if i < 1363 then decide (3 ≤ count1360 b) else decide (4 ≤ count1360 b))) else (if i < 1366 then (if i < 1365 then decide (5 ≤ count1360 b) else decide (6 ≤ count1360 b)) else (if i < 1367 then decide (7 ≤ count1360 b) else decide (8 ≤ count1360 b)))) else (if i < 1372 then (if i < 1370 then (if i < 1369 then decide (1 ≤ count1368 b) else decide (2 ≤ count1368 b)) else (if i < 1371 then decide (3 ≤ count1368 b) else decide (4 ≤ count1368 b))) else (if i < 1374 then (if i < 1373 then decide (5 ≤ count1368 b) else decide (6 ≤ count1368 b)) else (if i < 1375 then decide (7 ≤ count1368 b) else decide (8 ≤ count1368 b)))))) else (if i < 1391 then (if i < 1383 then (if i < 1379 then (if i < 1377 then decide (9 ≤ count1368 b) else (if i < 1378 then decide (10 ≤ count1368 b) else decide (11 ≤ count1368 b))) else (if i < 1381 then (if i < 1380 then decide (12 ≤ count1368 b) else decide (13 ≤ count1368 b)) else (if i < 1382 then decide (14 ≤ count1368 b) else decide (15 ≤ count1368 b)))) else (if i < 1387 then (if i < 1385 then (if i < 1384 then decide (16 ≤ count1368 b) else decide (1 ≤ count1384 b)) else (if i < 1386 then decide (2 ≤ count1384 b) else decide (1 ≤ count1386 b))) else (if i < 1389 then (if i < 1388 then decide (2 ≤ count1386 b) else decide (1 ≤ count1388 b)) else (if i < 1390 then decide (2 ≤ count1388 b) else decide (3 ≤ count1388 b))))) else (if i < 1398 then (if i < 1394 then (if i < 1392 then decide (4 ≤ count1388 b) else (if i < 1393 then decide (1 ≤ count1392 b) else decide (2 ≤ count1392 b))) else (if i < 1396 then (if i < 1395 then decide (1 ≤ count1394 b) else decide (2 ≤ count1394 b)) else (if i < 1397 then decide (1 ≤ count1396 b) else decide (2 ≤ count1396 b)))) else (if i < 1402 then (if i < 1400 then (if i < 1399 then decide (3 ≤ count1396 b) else decide (4 ≤ count1396 b)) else (if i < 1401 then decide (1 ≤ count1400 b) else decide (2 ≤ count1400 b))) else (if i < 1404 then (if i < 1403 then decide (3 ≤ count1400 b) else decide (4 ≤ count1400 b)) else (if i < 1405 then decide (5 ≤ count1400 b) else decide (6 ≤ count1400 b)))))))))) else (if i < 1640 then (if i < 1523 then (if i < 1464 then (if i < 1435 then (if i < 1420 then (if i < 1413 then (if i < 1409 then (if i < 1407 then decide (7 ≤ count1400 b) else (if i < 1408 then decide (8 ≤ count1400 b) else decide (1 ≤ count1408 b))) else (if i < 1411 then (if i < 1410 then decide (2 ≤ count1408 b) else decide (1 ≤ count1410 b)) else (if i < 1412 then decide (2 ≤ count1410 b) else decide (1 ≤ count1412 b)))) else (if i < 1416 then (if i < 1414 then decide (2 ≤ count1412 b) else (if i < 1415 then decide (3 ≤ count1412 b) else decide (4 ≤ count1412 b))) else (if i < 1418 then (if i < 1417 then decide (1 ≤ count1416 b) else decide (2 ≤ count1416 b)) else (if i < 1419 then decide (1 ≤ count1418 b) else decide (2 ≤ count1418 b))))) else (if i < 1427 then (if i < 1423 then (if i < 1421 then decide (1 ≤ count1420 b) else (if i < 1422 then decide (2 ≤ count1420 b) else decide (3 ≤ count1420 b))) else (if i < 1425 then (if i < 1424 then decide (1 ≤ count1423 b) else decide (2 ≤ count1423 b)) else (if i < 1426 then decide (3 ≤ count1423 b) else decide (4 ≤ count1423 b)))) else (if i < 1431 then (if i < 1429 then (if i < 1428 then decide (5 ≤ count1423 b) else decide (1 ≤ count1428 b)) else (if i < 1430 then decide (2 ≤ count1428 b) else decide (3 ≤ count1428 b))) else (if i < 1433 then (if i < 1432 then decide (4 ≤ count1428 b) else decide (5 ≤ count1428 b)) else (if i < 1434 then decide (6 ≤ count1428 b) else decide (7 ≤ count1428 b)))))) else (if i < 1449 then (if i < 1442 then (if i < 1438 then (if i < 1436 then decide (8 ≤ count1428 b) else (if i < 1437 then decide (9 ≤ count1428 b) else decide (1 ≤ count1437 b))) else (if i < 1440 then (if i < 1439 then decide (2 ≤ count1437 b) else decide (3 ≤ count1437 b)) else (if i < 1441 then decide (4 ≤ count1437 b) else decide (5 ≤ count1437 b)))) else (if i < 1445 then (if i < 1443 then decide (6 ≤ count1437 b) else (if i < 1444 then decide (7 ≤ count1437 b) else decide (8 ≤ count1437 b))) else (if i < 1447 then (if i < 1446 then decide (9 ≤ count1437 b) else decide (10 ≤ count1437 b)) else (if i < 1448 then decide (11 ≤ count1437 b) else decide (12 ≤ count1437 b))))) else (if i < 1456 then (if i < 1452 then (if i < 1450 then decide (13 ≤ count1437 b) else (if i < 1451 then decide (14 ≤ count1437 b) else decide (15 ≤ count1437 b))) else (if i < 1454 then (if i < 1453 then decide (16 ≤ count1437 b) else decide (17 ≤ count1437 b)) else (if i < 1455 then decide (1 ≤ count1454 b) else decide (2 ≤ count1454 b)))) else (if i < 1460 then (if i < 1458 then (if i < 1457 then decide (3 ≤ count1454 b) else decide (4 ≤ count1454 b)) else (if i < 1459 then decide (5 ≤ count1454 b) else decide (6 ≤ count1454 b))) else (if i < 1462 then (if i < 1461 then decide (7 ≤ count1454 b) else decide (8 ≤ count1454 b)) else (if i < 1463 then decide (9 ≤ count1454 b) else decide (10 ≤ count1454 b))))))) else (if i < 1493 then (if i < 1478 then (if i < 1471 then (if i < 1467 then (if i < 1465 then decide (11 ≤ count1454 b) else (if i < 1466 then decide (12 ≤ count1454 b) else decide (13 ≤ count1454 b))) else (if i < 1469 then (if i < 1468 then decide (14 ≤ count1454 b) else decide (15 ≤ count1454 b)) else (if i < 1470 then decide (16 ≤ count1454 b) else decide (17 ≤ count1454 b)))) else (if i < 1474 then (if i < 1472 then decide (18 ≤ count1454 b) else (if i < 1473 then decide (19 ≤ count1454 b) else decide (20 ≤ count1454 b))) else (if i < 1476 then (if i < 1475 then decide (21 ≤ count1454 b) else decide (22 ≤ count1454 b)) else (if i < 1477 then decide (23 ≤ count1454 b) else decide (24 ≤ count1454 b))))) else (if i < 1485 then (if i < 1481 then (if i < 1479 then decide (25 ≤ count1454 b) else (if i < 1480 then decide (26 ≤ count1454 b) else decide (27 ≤ count1454 b))) else (if i < 1483 then (if i < 1482 then decide (28 ≤ count1454 b) else decide (29 ≤ count1454 b)) else (if i < 1484 then decide (30 ≤ count1454 b) else decide (31 ≤ count1454 b)))) else (if i < 1489 then (if i < 1487 then (if i < 1486 then decide (32 ≤ count1454 b) else decide (33 ≤ count1454 b)) else (if i < 1488 then decide (1 ≤ count1487 b) else decide (2 ≤ count1487 b))) else (if i < 1491 then (if i < 1490 then decide (3 ≤ count1487 b) else decide (4 ≤ count1487 b)) else (if i < 1492 then decide (5 ≤ count1487 b) else decide (6 ≤ count1487 b)))))) else (if i < 1508 then (if i < 1500 then (if i < 1496 then (if i < 1494 then decide (7 ≤ count1487 b) else (if i < 1495 then decide (8 ≤ count1487 b) else decide (9 ≤ count1487 b))) else (if i < 1498 then (if i < 1497 then decide (10 ≤ count1487 b) else decide (11 ≤ count1487 b)) else (if i < 1499 then decide (12 ≤ count1487 b) else decide (13 ≤ count1487 b)))) else (if i < 1504 then (if i < 1502 then (if i < 1501 then decide (14 ≤ count1487 b) else decide (15 ≤ count1487 b)) else (if i < 1503 then decide (16 ≤ count1487 b) else decide (17 ≤ count1487 b))) else (if i < 1506 then (if i < 1505 then decide (18 ≤ count1487 b) else decide (19 ≤ count1487 b)) else (if i < 1507 then decide (20 ≤ count1487 b) else decide (21 ≤ count1487 b))))) else (if i < 1515 then (if i < 1511 then (if i < 1509 then decide (22 ≤ count1487 b) else (if i < 1510 then decide (23 ≤ count1487 b) else decide (24 ≤ count1487 b))) else (if i < 1513 then (if i < 1512 then decide (25 ≤ count1487 b) else decide (26 ≤ count1487 b)) else (if i < 1514 then decide (27 ≤ count1487 b) else decide (28 ≤ count1487 b)))) else (if i < 1519 then (if i < 1517 then (if i < 1516 then decide (29 ≤ count1487 b) else decide (30 ≤ count1487 b)) else (if i < 1518 then decide (31 ≤ count1487 b) else decide (32 ≤ count1487 b))) else (if i < 1521 then (if i < 1520 then decide (33 ≤ count1487 b) else decide (34 ≤ count1487 b)) else (if i < 1522 then decide (35 ≤ count1487 b) else decide (36 ≤ count1487 b)))))))) else (if i < 1581 then (if i < 1552 then (if i < 1537 then (if i < 1530 then (if i < 1526 then (if i < 1524 then decide (37 ≤ count1487 b) else (if i < 1525 then decide (38 ≤ count1487 b) else decide (39 ≤ count1487 b))) else (if i < 1528 then (if i < 1527 then decide (40 ≤ count1487 b) else decide (41 ≤ count1487 b)) else (if i < 1529 then decide (42 ≤ count1487 b) else decide (1 ≤ count1529 b)))) else (if i < 1533 then (if i < 1531 then decide (2 ≤ count1529 b) else (if i < 1532 then decide (1 ≤ count1531 b) else decide (2 ≤ count1531 b))) else (if i < 1535 then (if i < 1534 then decide (1 ≤ count1533 b) else decide (2 ≤ count1533 b)) else (if i < 1536 then decide (3 ≤ count1533 b) else decide (4 ≤ count1533 b))))) else (if i < 1544 then (if i < 1540 then (if i < 1538 then decide (1 ≤ count1537 b) else (if i < 1539 then decide (2 ≤ count1537 b) else decide (1 ≤ count1539 b))) else (if i < 1542 then (if i < 1541 then decide (2 ≤ count1539 b) else decide (1 ≤ count1541 b)) else (if i < 1543 then decide (2 ≤ count1541 b) else decide (3 ≤ count1541 b)))) else (if i < 1548 then (if i < 1546 then (if i < 1545 then decide (4 ≤ count1541 b) else decide (1 ≤ count1545 b)) else (if i < 1547 then decide (2 ≤ count1545 b) else decide (3 ≤ count1545 b))) else (if i < 1550 then (if i < 1549 then decide (4 ≤ count1545 b) else decide (5 ≤ count1545 b)) else (if i < 1551 then decide (6 ≤ count1545 b) else decide (7 ≤ count1545 b)))))) else (if i < 1566 then (if i < 1559 then (if i < 1555 then (if i < 1553 then decide (8 ≤ count1545 b) else (if i < 1554 then decide (1 ≤ count1553 b) else decide (2 ≤ count1553 b))) else (if i < 1557 then (if i < 1556 then decide (1 ≤ count1555 b) else decide (2 ≤ count1555 b)) else (if i < 1558 then decide (1 ≤ count1557 b) else decide (2 ≤ count1557 b)))) else (if i < 1562 then (if i < 1560 then decide (3 ≤ count1557 b) else (if i < 1561 then decide (4 ≤ count1557 b) else decide (1 ≤ count1561 b))) else (if i < 1564 then (if i < 1563 then decide (2 ≤ count1561 b) else decide (1 ≤ count1563 b)) else (if i < 1565 then decide (2 ≤ count1563 b) else decide (1 ≤ count1565 b))))) else (if i < 1573 then (if i < 1569 then (if i < 1567 then decide (2 ≤ count1565 b) else (if i < 1568 then decide (3 ≤ count1565 b) else decide (4 ≤ count1565 b))) else (if i < 1571 then (if i < 1570 then decide (1 ≤ count1569 b) else decide (2 ≤ count1569 b)) else (if i < 1572 then decide (3 ≤ count1569 b) else decide (4 ≤ count1569 b)))) else (if i < 1577 then (if i < 1575 then (if i < 1574 then decide (5 ≤ count1569 b) else decide (6 ≤ count1569 b)) else (if i < 1576 then decide (7 ≤ count1569 b) else decide (8 ≤ count1569 b))) else (if i < 1579 then (if i < 1578 then decide (1 ≤ count1577 b) else decide (2 ≤ count1577 b)) else (if i < 1580 then decide (3 ≤ count1577 b) else decide (4 ≤ count1577 b))))))) else (if i < 1610 then (if i < 1595 then (if i < 1588 then (if i < 1584 then (if i < 1582 then decide (5 ≤ count1577 b) else (if i < 1583 then decide (6 ≤ count1577 b) else decide (7 ≤ count1577 b))) else (if i < 1586 then (if i < 1585 then decide (8 ≤ count1577 b) else decide (9 ≤ count1577 b)) else (if i < 1587 then decide (10 ≤ count1577 b) else decide (11 ≤ count1577 b)))) else (if i < 1591 then (if i < 1589 then decide (12 ≤ count1577 b) else (if i < 1590 then decide (13 ≤ count1577 b) else decide (14 ≤ count1577 b))) else (if i < 1593 then (if i < 1592 then decide (15 ≤ count1577 b) else decide (16 ≤ count1577 b)) else (if i < 1594 then decide (1 ≤ count1593 b) else decide (2 ≤ count1593 b))))) else (if i < 1602 then (if i < 1598 then (if i < 1596 then decide (1 ≤ count1595 b) else (if i < 1597 then decide (2 ≤ count1595 b) else decide (1 ≤ count1597 b))) else (if i < 1600 then (if i < 1599 then decide (2 ≤ count1597 b) else decide (3 ≤ count1597 b)) else (if i < 1601 then decide (4 ≤ count1597 b) else decide (1 ≤ count1601 b)))) else (if i < 1606 then (if i < 1604 then (if i < 1603 then decide (2 ≤ count1601 b) else decide (1 ≤ count1603 b)) else (if i < 1605 then decide (2 ≤ count1603 b) else decide (1 ≤ count1605 b))) else (if i < 1608 then (if i < 1607 then decide (2 ≤ count1605 b) else decide (3 ≤ count1605 b)) else (if i < 1609 then decide (4 ≤ count1605 b) else decide (1 ≤ count1609 b)))))) else (if i < 1625 then (if i < 1617 then (if i < 1613 then (if i < 1611 then decide (2 ≤ count1609 b) else (if i < 1612 then decide (3 ≤ count1609 b) else decide (4 ≤ count1609 b))) else (if i < 1615 then (if i < 1614 then decide (5 ≤ count1609 b) else decide (6 ≤ count1609 b)) else (if i < 1616 then decide (7 ≤ count1609 b) else decide (8 ≤ count1609 b)))) else (if i < 1621 then (if i < 1619 then (if i < 1618 then decide (1 ≤ count1617 b) else decide (2 ≤ count1617 b)) else (if i < 1620 then decide (1 ≤ count1619 b) else decide (2 ≤ count1619 b))) else (if i < 1623 then (if i < 1622 then decide (1 ≤ count1621 b) else decide (2 ≤ count1621 b)) else (if i < 1624 then decide (3 ≤ count1621 b) else decide (4 ≤ count1621 b))))) else (if i < 1632 then (if i < 1628 then (if i < 1626 then decide (1 ≤ count1625 b) else (if i < 1627 then decide (2 ≤ count1625 b) else decide (1 ≤ count1627 b))) else (if i < 1630 then (if i < 1629 then decide (2 ≤ count1627 b) else decide (1 ≤ count1629 b)) else (if i < 1631 then decide (2 ≤ count1629 b) else decide (3 ≤ count1629 b)))) else (if i < 1636 then (if i < 1634 then (if i < 1633 then decide (1 ≤ count1632 b) else decide (2 ≤ count1632 b)) else (if i < 1635 then decide (3 ≤ count1632 b) else decide (4 ≤ count1632 b))) else (if i < 1638 then (if i < 1637 then decide (5 ≤ count1632 b) else decide (1 ≤ count1637 b)) else (if i < 1639 then decide (2 ≤ count1637 b) else decide (3 ≤ count1637 b))))))))) else (if i < 1757 then (if i < 1698 then (if i < 1669 then (if i < 1654 then (if i < 1647 then (if i < 1643 then (if i < 1641 then decide (4 ≤ count1637 b) else (if i < 1642 then decide (5 ≤ count1637 b) else decide (6 ≤ count1637 b))) else (if i < 1645 then (if i < 1644 then decide (7 ≤ count1637 b) else decide (8 ≤ count1637 b)) else (if i < 1646 then decide (9 ≤ count1637 b) else decide (1 ≤ count1646 b)))) else (if i < 1650 then (if i < 1648 then decide (2 ≤ count1646 b) else (if i < 1649 then decide (3 ≤ count1646 b) else decide (4 ≤ count1646 b))) else (if i < 1652 then (if i < 1651 then decide (5 ≤ count1646 b) else decide (6 ≤ count1646 b)) else (if i < 1653 then decide (7 ≤ count1646 b) else decide (8 ≤ count1646 b))))) else (if i < 1661 then (if i < 1657 then (if i < 1655 then decide (9 ≤ count1646 b) else (if i < 1656 then decide (10 ≤ count1646 b) else decide (11 ≤ count1646 b))) else (if i < 1659 then (if i < 1658 then decide (12 ≤ count1646 b) else decide (13 ≤ count1646 b)) else (if i < 1660 then decide (14 ≤ count1646 b) else decide (15 ≤ count1646 b)))) else (if i < 1665 then (if i < 1663 then (if i < 1662 then decide (16 ≤ count1646 b) else decide (17 ≤ count1646 b)) else (if i < 1664 then decide (1 ≤ count1663 b) else decide (2 ≤ count1663 b))) else (if i < 1667 then (if i < 1666 then decide (3 ≤ count1663 b) else decide (4 ≤ count1663 b)) else (if i < 1668 then decide (5 ≤ count1663 b) else decide (6 ≤ count1663 b)))))) else (if i < 1683 then (if i < 1676 then (if i < 1672 then (if i < 1670 then decide (7 ≤ count1663 b) else (if i < 1671 then decide (8 ≤ count1663 b) else decide (9 ≤ count1663 b))) else (if i < 1674 then (if i < 1673 then decide (10 ≤ count1663 b) else decide (11 ≤ count1663 b)) else (if i < 1675 then decide (12 ≤ count1663 b) else decide (13 ≤ count1663 b)))) else (if i < 1679 then (if i < 1677 then decide (14 ≤ count1663 b) else (if i < 1678 then decide (15 ≤ count1663 b) else decide (16 ≤ count1663 b))) else (if i < 1681 then (if i < 1680 then decide (17 ≤ count1663 b) else decide (18 ≤ count1663 b)) else (if i < 1682 then decide (19 ≤ count1663 b) else decide (20 ≤ count1663 b))))) else (if i < 1690 then (if i < 1686 then (if i < 1684 then decide (21 ≤ count1663 b) else (if i < 1685 then decide (22 ≤ count1663 b) else decide (23 ≤ count1663 b))) else (if i < 1688 then (if i < 1687 then decide (24 ≤ count1663 b) else decide (25 ≤ count1663 b)) else (if i < 1689 then decide (26 ≤ count1663 b) else decide (1 ≤ count1689 b)))) else (if i < 1694 then (if i < 1692 then (if i < 1691 then decide (2 ≤ count1689 b) else decide (1 ≤ count1691 b)) else (if i < 1693 then decide (2 ≤ count1691 b) else decide (1 ≤ count1693 b))) else (if i < 1696 then (if i < 1695 then decide (2 ≤ count1693 b) else decide (3 ≤ count1693 b)) else (if i < 1697 then decide (4 ≤ count1693 b) else decide (1 ≤ count1697 b))))))) else (if i < 1727 then (if i < 1712 then (if i < 1705 then (if i < 1701 then (if i < 1699 then decide (2 ≤ count1697 b) else (if i < 1700 then decide (1 ≤ count1699 b) else decide (2 ≤ count1699 b))) else (if i < 1703 then (if i < 1702 then decide (1 ≤ count1701 b) else decide (2 ≤ count1701 b)) else (if i < 1704 then decide (3 ≤ count1701 b) else decide (4 ≤ count1701 b)))) else (if i < 1708 then (if i < 1706 then decide (1 ≤ count1705 b) else (if i < 1707 then decide (2 ≤ count1705 b) else decide (3 ≤ count1705 b))) else (if i < 1710 then (if i < 1709 then decide (4 ≤ count1705 b) else decide (5 ≤ count1705 b)) else (if i < 1711 then decide (6 ≤ count1705 b) else decide (7 ≤ count1705 b))))) else (if i < 1719 then (if i < 1715 then (if i < 1713 then decide (8 ≤ count1705 b) else (if i < 1714 then decide (1 ≤ count1713 b) else decide (2 ≤ count1713 b))) else (if i < 1717 then (if i < 1716 then decide (1 ≤ count1715 b) else decide (2 ≤ count1715 b)) else (if i < 1718 then decide (1 ≤ count1717 b) else decide (2 ≤ count1717 b)))) else (if i < 1723 then (if i < 1721 then (if i < 1720 then decide (3 ≤ count1717 b) else decide (4 ≤ count1717 b)) else (if i < 1722 then decide (1 ≤ count1721 b) else decide (2 ≤ count1721 b))) else (if i < 1725 then (if i < 1724 then decide (1 ≤ count1723 b) else decide (2 ≤ count1723 b)) else (if i < 1726 then decide (1 ≤ count1725 b) else decide (2 ≤ count1725 b)))))) else (if i < 1742 then (if i < 1734 then (if i < 1730 then (if i < 1728 then decide (3 ≤ count1725 b) else (if i < 1729 then decide (4 ≤ count1725 b) else decide (1 ≤ count1729 b))) else (if i < 1732 then (if i < 1731 then decide (2 ≤ count1729 b) else decide (3 ≤ count1729 b)) else (if i < 1733 then decide (4 ≤ count1729 b) else decide (5 ≤ count1729 b)))) else (if i < 1738 then (if i < 1736 then (if i < 1735 then decide (6 ≤ count1729 b) else decide (7 ≤ count1729 b)) else (if i < 1737 then decide (8 ≤ count1729 b) else decide (1 ≤ count1737 b))) else (if i < 1740 then (if i < 1739 then decide (2 ≤ count1737 b) else decide (3 ≤ count1737 b)) else (if i < 1741 then decide (4 ≤ count1737 b) else decide (5 ≤ count1737 b))))) else (if i < 1749 then (if i < 1745 then (if i < 1743 then decide (6 ≤ count1737 b) else (if i < 1744 then decide (7 ≤ count1737 b) else decide (8 ≤ count1737 b))) else (if i < 1747 then (if i < 1746 then decide (9 ≤ count1737 b) else decide (10 ≤ count1737 b)) else (if i < 1748 then decide (11 ≤ count1737 b) else decide (12 ≤ count1737 b)))) else (if i < 1753 then (if i < 1751 then (if i < 1750 then decide (13 ≤ count1737 b) else decide (14 ≤ count1737 b)) else (if i < 1752 then decide (15 ≤ count1737 b) else decide (16 ≤ count1737 b))) else (if i < 1755 then (if i < 1754 then decide (1 ≤ count1753 b) else decide (2 ≤ count1753 b)) else (if i < 1756 then decide (1 ≤ count1755 b) else decide (2 ≤ count1755 b)))))))) else (if i < 1816 then (if i < 1786 then (if i < 1771 then (if i < 1764 then (if i < 1760 then (if i < 1758 then decide (1 ≤ count1757 b) else (if i < 1759 then decide (2 ≤ count1757 b) else decide (3 ≤ count1757 b))) else (if i < 1762 then (if i < 1761 then decide (4 ≤ count1757 b) else decide (1 ≤ count1761 b)) else (if i < 1763 then decide (2 ≤ count1761 b) else decide (1 ≤ count1763 b)))) else (if i < 1767 then (if i < 1765 then decide (2 ≤ count1763 b) else (if i < 1766 then decide (1 ≤ count1765 b) else decide (2 ≤ count1765 b))) else (if i < 1769 then (if i < 1768 then decide (3 ≤ count1765 b) else decide (4 ≤ count1765 b)) else (if i < 1770 then decide (1 ≤ count1769 b) else decide (2 ≤ count1769 b))))) else (if i < 1778 then (if i < 1774 then (if i < 1772 then decide (3 ≤ count1769 b) else (if i < 1773 then decide (4 ≤ count1769 b) else decide (5 ≤ count1769 b))) else (if i < 1776 then (if i < 1775 then decide (6 ≤ count1769 b) else decide (7 ≤ count1769 b)) else (if i < 1777 then decide (8 ≤ count1769 b) else decide (1 ≤ count1777 b)))) else (if i < 1782 then (if i < 1780 then (if i < 1779 then decide (2 ≤ count1777 b) else decide (1 ≤ count1779 b)) else (if i < 1781 then decide (2 ≤ count1779 b) else decide (1 ≤ count1781 b))) else (if i < 1784 then (if i < 1783 then decide (2 ≤ count1781 b) else decide (3 ≤ count1781 b)) else (if i < 1785 then decide (4 ≤ count1781 b) else decide (1 ≤ count1785 b)))))) else (if i < 1801 then (if i < 1793 then (if i < 1789 then (if i < 1787 then decide (2 ≤ count1785 b) else (if i < 1788 then decide (1 ≤ count1787 b) else decide (2 ≤ count1787 b))) else (if i < 1791 then (if i < 1790 then decide (1 ≤ count1789 b) else decide (2 ≤ count1789 b)) else (if i < 1792 then decide (3 ≤ count1789 b) else decide (1 ≤ count1792 b)))) else (if i < 1797 then (if i < 1795 then (if i < 1794 then decide (2 ≤ count1792 b) else decide (3 ≤ count1792 b)) else (if i < 1796 then decide (4 ≤ count1792 b) else decide (5 ≤ count1792 b))) else (if i < 1799 then (if i < 1798 then decide (1 ≤ count1797 b) else decide (2 ≤ count1797 b)) else (if i < 1800 then decide (3 ≤ count1797 b) else decide (4 ≤ count1797 b))))) else (if i < 1808 then (if i < 1804 then (if i < 1802 then decide (5 ≤ count1797 b) else (if i < 1803 then decide (6 ≤ count1797 b) else decide (7 ≤ count1797 b))) else (if i < 1806 then (if i < 1805 then decide (8 ≤ count1797 b) else decide (9 ≤ count1797 b)) else (if i < 1807 then decide (1 ≤ count1806 b) else decide (2 ≤ count1806 b)))) else (if i < 1812 then (if i < 1810 then (if i < 1809 then decide (3 ≤ count1806 b) else decide (4 ≤ count1806 b)) else (if i < 1811 then decide (5 ≤ count1806 b) else decide (6 ≤ count1806 b))) else (if i < 1814 then (if i < 1813 then decide (7 ≤ count1806 b) else decide (8 ≤ count1806 b)) else (if i < 1815 then decide (9 ≤ count1806 b) else decide (10 ≤ count1806 b))))))) else (if i < 1845 then (if i < 1830 then (if i < 1823 then (if i < 1819 then (if i < 1817 then decide (11 ≤ count1806 b) else (if i < 1818 then decide (12 ≤ count1806 b) else decide (13 ≤ count1806 b))) else (if i < 1821 then (if i < 1820 then decide (14 ≤ count1806 b) else decide (15 ≤ count1806 b)) else (if i < 1822 then decide (16 ≤ count1806 b) else decide (17 ≤ count1806 b)))) else (if i < 1826 then (if i < 1824 then decide (1 ≤ count1823 b) else (if i < 1825 then decide (2 ≤ count1823 b) else decide (3 ≤ count1823 b))) else (if i < 1828 then (if i < 1827 then decide (4 ≤ count1823 b) else decide (5 ≤ count1823 b)) else (if i < 1829 then decide (6 ≤ count1823 b) else decide (7 ≤ count1823 b))))) else (if i < 1837 then (if i < 1833 then (if i < 1831 then decide (8 ≤ count1823 b) else (if i < 1832 then decide (9 ≤ count1823 b) else decide (10 ≤ count1823 b))) else (if i < 1835 then (if i < 1834 then decide (11 ≤ count1823 b) else decide (12 ≤ count1823 b)) else (if i < 1836 then decide (13 ≤ count1823 b) else decide (14 ≤ count1823 b)))) else (if i < 1841 then (if i < 1839 then (if i < 1838 then decide (15 ≤ count1823 b) else decide (16 ≤ count1823 b)) else (if i < 1840 then decide (17 ≤ count1823 b) else decide (18 ≤ count1823 b))) else (if i < 1843 then (if i < 1842 then decide (19 ≤ count1823 b) else decide (20 ≤ count1823 b)) else (if i < 1844 then decide (21 ≤ count1823 b) else decide (22 ≤ count1823 b)))))) else (if i < 1860 then (if i < 1852 then (if i < 1848 then (if i < 1846 then decide (23 ≤ count1823 b) else (if i < 1847 then decide (24 ≤ count1823 b) else decide (25 ≤ count1823 b))) else (if i < 1850 then (if i < 1849 then decide (26 ≤ count1823 b) else decide (1 ≤ count1849 b)) else (if i < 1851 then decide (2 ≤ count1849 b) else decide (3 ≤ count1849 b)))) else (if i < 1856 then (if i < 1854 then (if i < 1853 then decide (4 ≤ count1849 b) else decide (5 ≤ count1849 b)) else (if i < 1855 then decide (6 ≤ count1849 b) else decide (7 ≤ count1849 b))) else (if i < 1858 then (if i < 1857 then decide (8 ≤ count1849 b) else decide (9 ≤ count1849 b)) else (if i < 1859 then decide (10 ≤ count1849 b) else decide (11 ≤ count1849 b))))) else (if i < 1867 then (if i < 1863 then (if i < 1861 then decide (12 ≤ count1849 b) else (if i < 1862 then decide (13 ≤ count1849 b) else decide (14 ≤ count1849 b))) else (if i < 1865 then (if i < 1864 then decide (15 ≤ count1849 b) else decide (16 ≤ count1849 b)) else (if i < 1866 then decide (17 ≤ count1849 b) else decide (18 ≤ count1849 b)))) else (if i < 1871 then (if i < 1869 then (if i < 1868 then decide (19 ≤ count1849 b) else decide (20 ≤ count1849 b)) else (if i < 1870 then decide (21 ≤ count1849 b) else decide (22 ≤ count1849 b))) else (if i < 1873 then (if i < 1872 then decide (23 ≤ count1849 b) else decide (24 ≤ count1849 b)) else (if i < 1874 then decide (25 ≤ count1849 b) else decide (26 ≤ count1849 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (65 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (66 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (69 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (70 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (72 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (73 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (75 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (76 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (79 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (80 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (83 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (84 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (87 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (89 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (90 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (93 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (94 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (95 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (96 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (98 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (101 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (103 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (105 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (107 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (108 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (110 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (112 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (113 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (115 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (116 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (118 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (122 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (125 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (126 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (127 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (192 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (193 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (194 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (196 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (200 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (201 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (202 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (204 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (207 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (210 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (211 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (212 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (213 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (215 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (217 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (218 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (220 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (221 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (223 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (224 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (227 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (228 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (231 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (234 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (235 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (237 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (238 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (240 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (241 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (243 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (244 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (245 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (246 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (248 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (250 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (251 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (253 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (254 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (281 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (285 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (317 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (319 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (329 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (330 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (333 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (334 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (336 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (337 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (338 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (341 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (342 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (345 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (347 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (348 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (349 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (350 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (351 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (365 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (367 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (370 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (373 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (375 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (379 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (381 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (382 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (383 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (458 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (459 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (460 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (461 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (464 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (465 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (467 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (469 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (472 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (473 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (475 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (476 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (477 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (478 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (495 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (496 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (498 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (499 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (500 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (501 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (503 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (506 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (507 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (InPath q (508 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (InPath q (509 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (InPath q (511 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (65 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (70 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (72 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (75 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (83 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (89 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (90 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (93 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (96 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (98 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (101 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (105 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (107 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (108 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (110 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (112 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (113 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (116 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (126 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (127 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (194 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (196 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (202 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (210 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (212 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (213 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (215 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (223 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (224 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (231 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (235 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (237 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (240 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (241 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (243 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (246 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (250 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (253 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (254 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (285 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (317 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (319 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (329 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (330 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (334 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (336 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (347 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (351 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (365 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (367 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (370 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (373 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (375 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (379 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (381 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (382 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (383 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (459 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (461 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (465 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (467 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (469 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (473 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (476 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (477 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (478 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (496 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (BallClauseLogic.Endpoint q (500 : Vertex)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (BallClauseLogic.Endpoint q (501 : Vertex)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (BallClauseLogic.Endpoint q (503 : Vertex)) := rfl
theorem value250 (q : Snake 81) : valuation q 250 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (BallClauseLogic.Endpoint q (507 : Vertex)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (BallClauseLogic.Endpoint q (511 : Vertex)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value264 (q : Snake 81) : valuation q 264 = decide (2 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value276 (q : Snake 81) : valuation q 276 = decide (2 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value278 (q : Snake 81) : valuation q 278 = decide (2 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value286 (q : Snake 81) : valuation q 286 = decide (2 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value288 (q : Snake 81) : valuation q 288 = decide (2 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
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
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value336 (q : Snake 81) : valuation q 336 = decide (2 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value364 (q : Snake 81) : valuation q 364 = decide (2 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value366 (q : Snake 81) : valuation q 366 = decide (2 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value370 (q : Snake 81) : valuation q 370 = decide (2 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value384 (q : Snake 81) : valuation q 384 = decide (2 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
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
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value452 (q : Snake 81) : valuation q 452 = decide (2 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value466 (q : Snake 81) : valuation q 466 = decide (2 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 (baseVal q)) := rfl
theorem value480 (q : Snake 81) : valuation q 480 = decide (2 ≤ count479 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value482 (q : Snake 81) : valuation q 482 = decide (2 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value487 (q : Snake 81) : valuation q 487 = decide (1 ≤ count487 (baseVal q)) := rfl
theorem value488 (q : Snake 81) : valuation q 488 = decide (2 ≤ count487 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value491 (q : Snake 81) : valuation q 491 = decide (1 ≤ count491 (baseVal q)) := rfl
theorem value493 (q : Snake 81) : valuation q 493 = decide (1 ≤ count493 (baseVal q)) := rfl
theorem value495 (q : Snake 81) : valuation q 495 = decide (1 ≤ count495 (baseVal q)) := rfl
theorem value496 (q : Snake 81) : valuation q 496 = decide (2 ≤ count495 (baseVal q)) := rfl
theorem value497 (q : Snake 81) : valuation q 497 = decide (1 ≤ count497 (baseVal q)) := rfl
theorem value498 (q : Snake 81) : valuation q 498 = decide (2 ≤ count497 (baseVal q)) := rfl
theorem value499 (q : Snake 81) : valuation q 499 = decide (1 ≤ count499 (baseVal q)) := rfl
theorem value500 (q : Snake 81) : valuation q 500 = decide (2 ≤ count499 (baseVal q)) := rfl
theorem value501 (q : Snake 81) : valuation q 501 = decide (1 ≤ count501 (baseVal q)) := rfl
theorem value502 (q : Snake 81) : valuation q 502 = decide (2 ≤ count501 (baseVal q)) := rfl
theorem value504 (q : Snake 81) : valuation q 504 = decide (2 ≤ count503 (baseVal q)) := rfl
theorem value849 (q : Snake 81) : valuation q 849 = decide (1 ≤ count849 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (2 ≤ count849 (baseVal q)) := rfl
theorem value851 (q : Snake 81) : valuation q 851 = decide (1 ≤ count851 (baseVal q)) := rfl
theorem value852 (q : Snake 81) : valuation q 852 = decide (2 ≤ count851 (baseVal q)) := rfl
theorem value853 (q : Snake 81) : valuation q 853 = decide (3 ≤ count851 (baseVal q)) := rfl
theorem value854 (q : Snake 81) : valuation q 854 = decide (1 ≤ count854 (baseVal q)) := rfl
theorem value855 (q : Snake 81) : valuation q 855 = decide (2 ≤ count854 (baseVal q)) := rfl
theorem value856 (q : Snake 81) : valuation q 856 = decide (1 ≤ count856 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (2 ≤ count856 (baseVal q)) := rfl
theorem value858 (q : Snake 81) : valuation q 858 = decide (1 ≤ count858 (baseVal q)) := rfl
theorem value859 (q : Snake 81) : valuation q 859 = decide (2 ≤ count858 (baseVal q)) := rfl
theorem value860 (q : Snake 81) : valuation q 860 = decide (3 ≤ count858 (baseVal q)) := rfl
theorem value861 (q : Snake 81) : valuation q 861 = decide (4 ≤ count858 (baseVal q)) := rfl
theorem value862 (q : Snake 81) : valuation q 862 = decide (1 ≤ count862 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (2 ≤ count862 (baseVal q)) := rfl
theorem value864 (q : Snake 81) : valuation q 864 = decide (3 ≤ count862 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (4 ≤ count862 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (5 ≤ count862 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (6 ≤ count862 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (7 ≤ count862 (baseVal q)) := rfl
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
theorem value879 (q : Snake 81) : valuation q 879 = decide (1 ≤ count879 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (2 ≤ count879 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (1 ≤ count881 (baseVal q)) := rfl
theorem value882 (q : Snake 81) : valuation q 882 = decide (2 ≤ count881 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (3 ≤ count881 (baseVal q)) := rfl
theorem value884 (q : Snake 81) : valuation q 884 = decide (4 ≤ count881 (baseVal q)) := rfl
theorem value885 (q : Snake 81) : valuation q 885 = decide (1 ≤ count885 (baseVal q)) := rfl
theorem value886 (q : Snake 81) : valuation q 886 = decide (2 ≤ count885 (baseVal q)) := rfl
theorem value887 (q : Snake 81) : valuation q 887 = decide (3 ≤ count885 (baseVal q)) := rfl
theorem value888 (q : Snake 81) : valuation q 888 = decide (4 ≤ count885 (baseVal q)) := rfl
theorem value889 (q : Snake 81) : valuation q 889 = decide (5 ≤ count885 (baseVal q)) := rfl
theorem value890 (q : Snake 81) : valuation q 890 = decide (6 ≤ count885 (baseVal q)) := rfl
theorem value891 (q : Snake 81) : valuation q 891 = decide (7 ≤ count885 (baseVal q)) := rfl
theorem value893 (q : Snake 81) : valuation q 893 = decide (1 ≤ count893 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (2 ≤ count893 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (3 ≤ count893 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (4 ≤ count893 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (5 ≤ count893 (baseVal q)) := rfl
theorem value898 (q : Snake 81) : valuation q 898 = decide (6 ≤ count893 (baseVal q)) := rfl
theorem value899 (q : Snake 81) : valuation q 899 = decide (7 ≤ count893 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (8 ≤ count893 (baseVal q)) := rfl
theorem value901 (q : Snake 81) : valuation q 901 = decide (9 ≤ count893 (baseVal q)) := rfl
theorem value902 (q : Snake 81) : valuation q 902 = decide (10 ≤ count893 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (1 ≤ count908 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (2 ≤ count908 (baseVal q)) := rfl
theorem value910 (q : Snake 81) : valuation q 910 = decide (1 ≤ count910 (baseVal q)) := rfl
theorem value911 (q : Snake 81) : valuation q 911 = decide (2 ≤ count910 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (3 ≤ count910 (baseVal q)) := rfl
theorem value913 (q : Snake 81) : valuation q 913 = decide (1 ≤ count913 (baseVal q)) := rfl
theorem value914 (q : Snake 81) : valuation q 914 = decide (2 ≤ count913 (baseVal q)) := rfl
theorem value915 (q : Snake 81) : valuation q 915 = decide (1 ≤ count915 (baseVal q)) := rfl
theorem value916 (q : Snake 81) : valuation q 916 = decide (2 ≤ count915 (baseVal q)) := rfl
theorem value917 (q : Snake 81) : valuation q 917 = decide (1 ≤ count917 (baseVal q)) := rfl
theorem value918 (q : Snake 81) : valuation q 918 = decide (2 ≤ count917 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (3 ≤ count917 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (4 ≤ count917 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (1 ≤ count921 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (2 ≤ count921 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (3 ≤ count921 (baseVal q)) := rfl
theorem value924 (q : Snake 81) : valuation q 924 = decide (4 ≤ count921 (baseVal q)) := rfl
theorem value925 (q : Snake 81) : valuation q 925 = decide (5 ≤ count921 (baseVal q)) := rfl
theorem value926 (q : Snake 81) : valuation q 926 = decide (6 ≤ count921 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (7 ≤ count921 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (1 ≤ count928 (baseVal q)) := rfl
theorem value929 (q : Snake 81) : valuation q 929 = decide (2 ≤ count928 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (1 ≤ count930 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (2 ≤ count930 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (1 ≤ count932 (baseVal q)) := rfl
theorem value933 (q : Snake 81) : valuation q 933 = decide (2 ≤ count932 (baseVal q)) := rfl
theorem value934 (q : Snake 81) : valuation q 934 = decide (3 ≤ count932 (baseVal q)) := rfl
theorem value935 (q : Snake 81) : valuation q 935 = decide (4 ≤ count932 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (1 ≤ count936 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (2 ≤ count936 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (1 ≤ count938 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (2 ≤ count938 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (1 ≤ count940 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (2 ≤ count940 (baseVal q)) := rfl
theorem value942 (q : Snake 81) : valuation q 942 = decide (3 ≤ count940 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (4 ≤ count940 (baseVal q)) := rfl
theorem value944 (q : Snake 81) : valuation q 944 = decide (1 ≤ count944 (baseVal q)) := rfl
theorem value945 (q : Snake 81) : valuation q 945 = decide (2 ≤ count944 (baseVal q)) := rfl
theorem value946 (q : Snake 81) : valuation q 946 = decide (3 ≤ count944 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (4 ≤ count944 (baseVal q)) := rfl
theorem value948 (q : Snake 81) : valuation q 948 = decide (5 ≤ count944 (baseVal q)) := rfl
theorem value949 (q : Snake 81) : valuation q 949 = decide (6 ≤ count944 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (1 ≤ count952 (baseVal q)) := rfl
theorem value953 (q : Snake 81) : valuation q 953 = decide (2 ≤ count952 (baseVal q)) := rfl
theorem value954 (q : Snake 81) : valuation q 954 = decide (3 ≤ count952 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (4 ≤ count952 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (5 ≤ count952 (baseVal q)) := rfl
theorem value957 (q : Snake 81) : valuation q 957 = decide (6 ≤ count952 (baseVal q)) := rfl
theorem value958 (q : Snake 81) : valuation q 958 = decide (7 ≤ count952 (baseVal q)) := rfl
theorem value959 (q : Snake 81) : valuation q 959 = decide (8 ≤ count952 (baseVal q)) := rfl
theorem value960 (q : Snake 81) : valuation q 960 = decide (9 ≤ count952 (baseVal q)) := rfl
theorem value961 (q : Snake 81) : valuation q 961 = decide (10 ≤ count952 (baseVal q)) := rfl
theorem value962 (q : Snake 81) : valuation q 962 = decide (11 ≤ count952 (baseVal q)) := rfl
theorem value973 (q : Snake 81) : valuation q 973 = decide (7 ≤ count967 (baseVal q)) := rfl
theorem value974 (q : Snake 81) : valuation q 974 = decide (8 ≤ count967 (baseVal q)) := rfl
theorem value975 (q : Snake 81) : valuation q 975 = decide (9 ≤ count967 (baseVal q)) := rfl
theorem value976 (q : Snake 81) : valuation q 976 = decide (10 ≤ count967 (baseVal q)) := rfl
theorem value977 (q : Snake 81) : valuation q 977 = decide (11 ≤ count967 (baseVal q)) := rfl
theorem value978 (q : Snake 81) : valuation q 978 = decide (12 ≤ count967 (baseVal q)) := rfl
theorem value979 (q : Snake 81) : valuation q 979 = decide (13 ≤ count967 (baseVal q)) := rfl
theorem value980 (q : Snake 81) : valuation q 980 = decide (14 ≤ count967 (baseVal q)) := rfl
theorem value981 (q : Snake 81) : valuation q 981 = decide (15 ≤ count967 (baseVal q)) := rfl
theorem value982 (q : Snake 81) : valuation q 982 = decide (16 ≤ count967 (baseVal q)) := rfl
theorem value988 (q : Snake 81) : valuation q 988 = decide (1 ≤ count988 (baseVal q)) := rfl
theorem value989 (q : Snake 81) : valuation q 989 = decide (2 ≤ count988 (baseVal q)) := rfl
theorem value990 (q : Snake 81) : valuation q 990 = decide (1 ≤ count990 (baseVal q)) := rfl
theorem value991 (q : Snake 81) : valuation q 991 = decide (2 ≤ count990 (baseVal q)) := rfl
theorem value992 (q : Snake 81) : valuation q 992 = decide (3 ≤ count990 (baseVal q)) := rfl
theorem value993 (q : Snake 81) : valuation q 993 = decide (1 ≤ count993 (baseVal q)) := rfl
theorem value994 (q : Snake 81) : valuation q 994 = decide (2 ≤ count993 (baseVal q)) := rfl
theorem value995 (q : Snake 81) : valuation q 995 = decide (1 ≤ count995 (baseVal q)) := rfl
theorem value996 (q : Snake 81) : valuation q 996 = decide (2 ≤ count995 (baseVal q)) := rfl
theorem value997 (q : Snake 81) : valuation q 997 = decide (1 ≤ count997 (baseVal q)) := rfl
theorem value998 (q : Snake 81) : valuation q 998 = decide (2 ≤ count997 (baseVal q)) := rfl
theorem value999 (q : Snake 81) : valuation q 999 = decide (3 ≤ count997 (baseVal q)) := rfl
theorem value1000 (q : Snake 81) : valuation q 1000 = decide (4 ≤ count997 (baseVal q)) := rfl
theorem value1001 (q : Snake 81) : valuation q 1001 = decide (1 ≤ count1001 (baseVal q)) := rfl
theorem value1002 (q : Snake 81) : valuation q 1002 = decide (2 ≤ count1001 (baseVal q)) := rfl
theorem value1003 (q : Snake 81) : valuation q 1003 = decide (3 ≤ count1001 (baseVal q)) := rfl
theorem value1004 (q : Snake 81) : valuation q 1004 = decide (4 ≤ count1001 (baseVal q)) := rfl
theorem value1005 (q : Snake 81) : valuation q 1005 = decide (5 ≤ count1001 (baseVal q)) := rfl
theorem value1006 (q : Snake 81) : valuation q 1006 = decide (6 ≤ count1001 (baseVal q)) := rfl
theorem value1007 (q : Snake 81) : valuation q 1007 = decide (7 ≤ count1001 (baseVal q)) := rfl
theorem value1008 (q : Snake 81) : valuation q 1008 = decide (1 ≤ count1008 (baseVal q)) := rfl
theorem value1009 (q : Snake 81) : valuation q 1009 = decide (2 ≤ count1008 (baseVal q)) := rfl
theorem value1010 (q : Snake 81) : valuation q 1010 = decide (1 ≤ count1010 (baseVal q)) := rfl
theorem value1011 (q : Snake 81) : valuation q 1011 = decide (2 ≤ count1010 (baseVal q)) := rfl
theorem value1012 (q : Snake 81) : valuation q 1012 = decide (1 ≤ count1012 (baseVal q)) := rfl
theorem value1013 (q : Snake 81) : valuation q 1013 = decide (2 ≤ count1012 (baseVal q)) := rfl
theorem value1014 (q : Snake 81) : valuation q 1014 = decide (3 ≤ count1012 (baseVal q)) := rfl
theorem value1015 (q : Snake 81) : valuation q 1015 = decide (4 ≤ count1012 (baseVal q)) := rfl
theorem value1016 (q : Snake 81) : valuation q 1016 = decide (1 ≤ count1016 (baseVal q)) := rfl
theorem value1017 (q : Snake 81) : valuation q 1017 = decide (2 ≤ count1016 (baseVal q)) := rfl
theorem value1018 (q : Snake 81) : valuation q 1018 = decide (1 ≤ count1018 (baseVal q)) := rfl
theorem value1019 (q : Snake 81) : valuation q 1019 = decide (2 ≤ count1018 (baseVal q)) := rfl
theorem value1020 (q : Snake 81) : valuation q 1020 = decide (1 ≤ count1020 (baseVal q)) := rfl
theorem value1021 (q : Snake 81) : valuation q 1021 = decide (2 ≤ count1020 (baseVal q)) := rfl
theorem value1022 (q : Snake 81) : valuation q 1022 = decide (3 ≤ count1020 (baseVal q)) := rfl
theorem value1023 (q : Snake 81) : valuation q 1023 = decide (4 ≤ count1020 (baseVal q)) := rfl
theorem value1024 (q : Snake 81) : valuation q 1024 = decide (1 ≤ count1024 (baseVal q)) := rfl
theorem value1025 (q : Snake 81) : valuation q 1025 = decide (2 ≤ count1024 (baseVal q)) := rfl
theorem value1026 (q : Snake 81) : valuation q 1026 = decide (3 ≤ count1024 (baseVal q)) := rfl
theorem value1027 (q : Snake 81) : valuation q 1027 = decide (4 ≤ count1024 (baseVal q)) := rfl
theorem value1028 (q : Snake 81) : valuation q 1028 = decide (5 ≤ count1024 (baseVal q)) := rfl
theorem value1029 (q : Snake 81) : valuation q 1029 = decide (6 ≤ count1024 (baseVal q)) := rfl
theorem value1033 (q : Snake 81) : valuation q 1033 = decide (2 ≤ count1032 (baseVal q)) := rfl
theorem value1034 (q : Snake 81) : valuation q 1034 = decide (3 ≤ count1032 (baseVal q)) := rfl
theorem value1035 (q : Snake 81) : valuation q 1035 = decide (4 ≤ count1032 (baseVal q)) := rfl
theorem value1036 (q : Snake 81) : valuation q 1036 = decide (5 ≤ count1032 (baseVal q)) := rfl
theorem value1037 (q : Snake 81) : valuation q 1037 = decide (6 ≤ count1032 (baseVal q)) := rfl
theorem value1038 (q : Snake 81) : valuation q 1038 = decide (7 ≤ count1032 (baseVal q)) := rfl
theorem value1039 (q : Snake 81) : valuation q 1039 = decide (8 ≤ count1032 (baseVal q)) := rfl
theorem value1040 (q : Snake 81) : valuation q 1040 = decide (9 ≤ count1032 (baseVal q)) := rfl
theorem value1041 (q : Snake 81) : valuation q 1041 = decide (10 ≤ count1032 (baseVal q)) := rfl
theorem value1047 (q : Snake 81) : valuation q 1047 = decide (1 ≤ count1047 (baseVal q)) := rfl
theorem value1048 (q : Snake 81) : valuation q 1048 = decide (2 ≤ count1047 (baseVal q)) := rfl
theorem value1049 (q : Snake 81) : valuation q 1049 = decide (1 ≤ count1049 (baseVal q)) := rfl
theorem value1050 (q : Snake 81) : valuation q 1050 = decide (2 ≤ count1049 (baseVal q)) := rfl
theorem value1051 (q : Snake 81) : valuation q 1051 = decide (1 ≤ count1051 (baseVal q)) := rfl
theorem value1052 (q : Snake 81) : valuation q 1052 = decide (2 ≤ count1051 (baseVal q)) := rfl
theorem value1053 (q : Snake 81) : valuation q 1053 = decide (3 ≤ count1051 (baseVal q)) := rfl
theorem value1054 (q : Snake 81) : valuation q 1054 = decide (4 ≤ count1051 (baseVal q)) := rfl
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
theorem value1065 (q : Snake 81) : valuation q 1065 = decide (3 ≤ count1063 (baseVal q)) := rfl
theorem value1066 (q : Snake 81) : valuation q 1066 = decide (4 ≤ count1063 (baseVal q)) := rfl
theorem value1067 (q : Snake 81) : valuation q 1067 = decide (5 ≤ count1063 (baseVal q)) := rfl
theorem value1068 (q : Snake 81) : valuation q 1068 = decide (6 ≤ count1063 (baseVal q)) := rfl
theorem value1069 (q : Snake 81) : valuation q 1069 = decide (7 ≤ count1063 (baseVal q)) := rfl
theorem value1071 (q : Snake 81) : valuation q 1071 = decide (1 ≤ count1071 (baseVal q)) := rfl
theorem value1072 (q : Snake 81) : valuation q 1072 = decide (2 ≤ count1071 (baseVal q)) := rfl
theorem value1073 (q : Snake 81) : valuation q 1073 = decide (1 ≤ count1073 (baseVal q)) := rfl
theorem value1074 (q : Snake 81) : valuation q 1074 = decide (2 ≤ count1073 (baseVal q)) := rfl
theorem value1075 (q : Snake 81) : valuation q 1075 = decide (1 ≤ count1075 (baseVal q)) := rfl
theorem value1076 (q : Snake 81) : valuation q 1076 = decide (2 ≤ count1075 (baseVal q)) := rfl
theorem value1077 (q : Snake 81) : valuation q 1077 = decide (3 ≤ count1075 (baseVal q)) := rfl
theorem value1079 (q : Snake 81) : valuation q 1079 = decide (1 ≤ count1079 (baseVal q)) := rfl
theorem value1080 (q : Snake 81) : valuation q 1080 = decide (2 ≤ count1079 (baseVal q)) := rfl
theorem value1081 (q : Snake 81) : valuation q 1081 = decide (1 ≤ count1081 (baseVal q)) := rfl
theorem value1082 (q : Snake 81) : valuation q 1082 = decide (2 ≤ count1081 (baseVal q)) := rfl
theorem value1083 (q : Snake 81) : valuation q 1083 = decide (1 ≤ count1083 (baseVal q)) := rfl
theorem value1084 (q : Snake 81) : valuation q 1084 = decide (2 ≤ count1083 (baseVal q)) := rfl
theorem value1085 (q : Snake 81) : valuation q 1085 = decide (3 ≤ count1083 (baseVal q)) := rfl
theorem value1086 (q : Snake 81) : valuation q 1086 = decide (4 ≤ count1083 (baseVal q)) := rfl
theorem value1087 (q : Snake 81) : valuation q 1087 = decide (1 ≤ count1087 (baseVal q)) := rfl
theorem value1088 (q : Snake 81) : valuation q 1088 = decide (2 ≤ count1087 (baseVal q)) := rfl
theorem value1089 (q : Snake 81) : valuation q 1089 = decide (3 ≤ count1087 (baseVal q)) := rfl
theorem value1090 (q : Snake 81) : valuation q 1090 = decide (4 ≤ count1087 (baseVal q)) := rfl
theorem value1091 (q : Snake 81) : valuation q 1091 = decide (5 ≤ count1087 (baseVal q)) := rfl
theorem value1092 (q : Snake 81) : valuation q 1092 = decide (6 ≤ count1087 (baseVal q)) := rfl
theorem value1095 (q : Snake 81) : valuation q 1095 = decide (1 ≤ count1095 (baseVal q)) := rfl
theorem value1096 (q : Snake 81) : valuation q 1096 = decide (2 ≤ count1095 (baseVal q)) := rfl
theorem value1097 (q : Snake 81) : valuation q 1097 = decide (3 ≤ count1095 (baseVal q)) := rfl
theorem value1098 (q : Snake 81) : valuation q 1098 = decide (4 ≤ count1095 (baseVal q)) := rfl
theorem value1099 (q : Snake 81) : valuation q 1099 = decide (5 ≤ count1095 (baseVal q)) := rfl
theorem value1100 (q : Snake 81) : valuation q 1100 = decide (6 ≤ count1095 (baseVal q)) := rfl
theorem value1101 (q : Snake 81) : valuation q 1101 = decide (7 ≤ count1095 (baseVal q)) := rfl
theorem value1102 (q : Snake 81) : valuation q 1102 = decide (8 ≤ count1095 (baseVal q)) := rfl
theorem value1103 (q : Snake 81) : valuation q 1103 = decide (9 ≤ count1095 (baseVal q)) := rfl
theorem value1104 (q : Snake 81) : valuation q 1104 = decide (10 ≤ count1095 (baseVal q)) := rfl
theorem value1115 (q : Snake 81) : valuation q 1115 = decide (5 ≤ count1111 (baseVal q)) := rfl
theorem value1116 (q : Snake 81) : valuation q 1116 = decide (6 ≤ count1111 (baseVal q)) := rfl
theorem value1117 (q : Snake 81) : valuation q 1117 = decide (7 ≤ count1111 (baseVal q)) := rfl
theorem value1118 (q : Snake 81) : valuation q 1118 = decide (8 ≤ count1111 (baseVal q)) := rfl
theorem value1119 (q : Snake 81) : valuation q 1119 = decide (9 ≤ count1111 (baseVal q)) := rfl
theorem value1120 (q : Snake 81) : valuation q 1120 = decide (10 ≤ count1111 (baseVal q)) := rfl
theorem value1121 (q : Snake 81) : valuation q 1121 = decide (11 ≤ count1111 (baseVal q)) := rfl
theorem value1122 (q : Snake 81) : valuation q 1122 = decide (12 ≤ count1111 (baseVal q)) := rfl
theorem value1123 (q : Snake 81) : valuation q 1123 = decide (13 ≤ count1111 (baseVal q)) := rfl
theorem value1124 (q : Snake 81) : valuation q 1124 = decide (14 ≤ count1111 (baseVal q)) := rfl
theorem value1152 (q : Snake 81) : valuation q 1152 = decide (21 ≤ count1132 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (2 ≤ count1529 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (2 ≤ count1533 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (2 ≤ count1539 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (2 ≤ count1541 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (4 ≤ count1545 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (2 ≤ count1555 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (2 ≤ count1557 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (1 ≤ count1561 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (1 ≤ count1565 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (3 ≤ count1569 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (7 ≤ count1577 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (2 ≤ count1593 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (1 ≤ count1595 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (3 ≤ count1597 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (1 ≤ count1601 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (1 ≤ count1605 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (4 ≤ count1609 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (1 ≤ count1619 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (1 ≤ count1621 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (1 ≤ count1625 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (1 ≤ count1627 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (2 ≤ count1629 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (3 ≤ count1632 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (4 ≤ count1637 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (8 ≤ count1646 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (15 ≤ count1663 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (2 ≤ count1689 (baseVal q)) := rfl
theorem value1694 (q : Snake 81) : valuation q 1694 = decide (2 ≤ count1693 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (1 ≤ count1699 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (2 ≤ count1699 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (1 ≤ count1701 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (2 ≤ count1701 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (3 ≤ count1705 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (4 ≤ count1705 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (1 ≤ count1715 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (2 ≤ count1715 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (1 ≤ count1717 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (2 ≤ count1717 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (1 ≤ count1721 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (2 ≤ count1721 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (1 ≤ count1723 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (2 ≤ count1725 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (3 ≤ count1725 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (3 ≤ count1729 (baseVal q)) := rfl
theorem value1732 (q : Snake 81) : valuation q 1732 = decide (4 ≤ count1729 (baseVal q)) := rfl
theorem value1743 (q : Snake 81) : valuation q 1743 = decide (7 ≤ count1737 (baseVal q)) := rfl
theorem value1755 (q : Snake 81) : valuation q 1755 = decide (1 ≤ count1755 (baseVal q)) := rfl
theorem value1757 (q : Snake 81) : valuation q 1757 = decide (1 ≤ count1757 (baseVal q)) := rfl
theorem value1761 (q : Snake 81) : valuation q 1761 = decide (1 ≤ count1761 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (1 ≤ count1763 (baseVal q)) := rfl
theorem value1766 (q : Snake 81) : valuation q 1766 = decide (2 ≤ count1765 (baseVal q)) := rfl
theorem value1771 (q : Snake 81) : valuation q 1771 = decide (3 ≤ count1769 (baseVal q)) := rfl
theorem value1779 (q : Snake 81) : valuation q 1779 = decide (1 ≤ count1779 (baseVal q)) := rfl
theorem value1781 (q : Snake 81) : valuation q 1781 = decide (1 ≤ count1781 (baseVal q)) := rfl
theorem value1797 (q : Snake 81) : valuation q 1797 = decide (1 ≤ count1797 (baseVal q)) := rfl
theorem value1809 (q : Snake 81) : valuation q 1809 = decide (4 ≤ count1806 (baseVal q)) := rfl
theorem value1833 (q : Snake 81) : valuation q 1833 = decide (11 ≤ count1823 (baseVal q)) := rfl
theorem value1874 (q : Snake 81) : valuation q 1874 = decide (26 ≤ count1849 (baseVal q)) := rfl
theorem meaningNeg126 (b : Nat → Bool) : literal (valuationOf b) (-126) = decide (1 ≤ countLit b [-126]) := by
  change literal b (-126) = decide (1 ≤ countLit b [-126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-126) <;> decide
theorem meaningNeg124 (b : Nat → Bool) : literal (valuationOf b) (-124) = decide (1 ≤ countLit b [-124]) := by
  change literal b (-124) = decide (1 ≤ countLit b [-124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-124) <;> decide
theorem meaningNeg122 (b : Nat → Bool) : literal (valuationOf b) (-122) = decide (1 ≤ countLit b [-122]) := by
  change literal b (-122) = decide (1 ≤ countLit b [-122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-122) <;> decide
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
theorem meaningNeg113 (b : Nat → Bool) : literal (valuationOf b) (-113) = decide (1 ≤ countLit b [-113]) := by
  change literal b (-113) = decide (1 ≤ countLit b [-113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-113) <;> decide
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
theorem meaningNeg103 (b : Nat → Bool) : literal (valuationOf b) (-103) = decide (1 ≤ countLit b [-103]) := by
  change literal b (-103) = decide (1 ≤ countLit b [-103])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-103) <;> decide
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
theorem meaningNeg96 (b : Nat → Bool) : literal (valuationOf b) (-96) = decide (1 ≤ countLit b [-96]) := by
  change literal b (-96) = decide (1 ≤ countLit b [-96])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-96) <;> decide
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
theorem meaningNeg49 (b : Nat → Bool) : literal (valuationOf b) (-49) = decide (1 ≤ countLit b [-49]) := by
  change literal b (-49) = decide (1 ≤ countLit b [-49])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-49) <;> decide
theorem meaningNeg47 (b : Nat → Bool) : literal (valuationOf b) (-47) = decide (1 ≤ countLit b [-47]) := by
  change literal b (-47) = decide (1 ≤ countLit b [-47])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-47) <;> decide
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
theorem meaningNeg43 (b : Nat → Bool) : literal (valuationOf b) (-43) = decide (1 ≤ countLit b [-43]) := by
  change literal b (-43) = decide (1 ≤ countLit b [-43])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-43) <;> decide
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
theorem meaningNeg30 (b : Nat → Bool) : literal (valuationOf b) (-30) = decide (1 ≤ countLit b [-30]) := by
  change literal b (-30) = decide (1 ≤ countLit b [-30])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-30) <;> decide
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
theorem meaningNeg10 (b : Nat → Bool) : literal (valuationOf b) (-10) = decide (1 ≤ countLit b [-10]) := by
  change literal b (-10) = decide (1 ≤ countLit b [-10])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-10) <;> decide
theorem meaningNeg7 (b : Nat → Bool) : literal (valuationOf b) (-7) = decide (1 ≤ countLit b [-7]) := by
  change literal b (-7) = decide (1 ≤ countLit b [-7])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-7) <;> decide
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
theorem meaning141 (b : Nat → Bool) : literal (valuationOf b) (141) = decide (1 ≤ countLit b [141]) := by
  change literal b (141) = decide (1 ≤ countLit b [141])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (141) <;> decide
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
theorem meaning146 (b : Nat → Bool) : literal (valuationOf b) (146) = decide (1 ≤ countLit b [146]) := by
  change literal b (146) = decide (1 ≤ countLit b [146])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (146) <;> decide
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
theorem meaning152 (b : Nat → Bool) : literal (valuationOf b) (152) = decide (1 ≤ countLit b [152]) := by
  change literal b (152) = decide (1 ≤ countLit b [152])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (152) <;> decide
theorem meaning155 (b : Nat → Bool) : literal (valuationOf b) (155) = decide (1 ≤ countLit b [155]) := by
  change literal b (155) = decide (1 ≤ countLit b [155])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (155) <;> decide
theorem meaning157 (b : Nat → Bool) : literal (valuationOf b) (157) = decide (1 ≤ countLit b [157]) := by
  change literal b (157) = decide (1 ≤ countLit b [157])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (157) <;> decide
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
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
theorem meaning170 (b : Nat → Bool) : literal (valuationOf b) (170) = decide (1 ≤ countLit b [170]) := by
  change literal b (170) = decide (1 ≤ countLit b [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (170) <;> decide
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
theorem meaning174 (b : Nat → Bool) : literal (valuationOf b) (174) = decide (1 ≤ countLit b [174]) := by
  change literal b (174) = decide (1 ≤ countLit b [174])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (174) <;> decide
theorem meaning176 (b : Nat → Bool) : literal (valuationOf b) (176) = decide (1 ≤ countLit b [176]) := by
  change literal b (176) = decide (1 ≤ countLit b [176])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (176) <;> decide
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
theorem meaning184 (b : Nat → Bool) : literal (valuationOf b) (184) = decide (1 ≤ countLit b [184]) := by
  change literal b (184) = decide (1 ≤ countLit b [184])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (184) <;> decide
theorem meaning185 (b : Nat → Bool) : literal (valuationOf b) (185) = decide (1 ≤ countLit b [185]) := by
  change literal b (185) = decide (1 ≤ countLit b [185])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (185) <;> decide
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
theorem meaning192 (b : Nat → Bool) : literal (valuationOf b) (192) = decide (1 ≤ countLit b [192]) := by
  change literal b (192) = decide (1 ≤ countLit b [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (192) <;> decide
theorem meaning194 (b : Nat → Bool) : literal (valuationOf b) (194) = decide (1 ≤ countLit b [194]) := by
  change literal b (194) = decide (1 ≤ countLit b [194])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (194) <;> decide
theorem meaning195 (b : Nat → Bool) : literal (valuationOf b) (195) = decide (1 ≤ countLit b [195]) := by
  change literal b (195) = decide (1 ≤ countLit b [195])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (195) <;> decide
theorem meaning197 (b : Nat → Bool) : literal (valuationOf b) (197) = decide (1 ≤ countLit b [197]) := by
  change literal b (197) = decide (1 ≤ countLit b [197])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (197) <;> decide
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
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) (211) = decide (1 ≤ countLit b [211]) := by
  change literal b (211) = decide (1 ≤ countLit b [211])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (211) <;> decide
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
theorem meaning220 (b : Nat → Bool) : literal (valuationOf b) (220) = decide (1 ≤ countLit b [220]) := by
  change literal b (220) = decide (1 ≤ countLit b [220])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (220) <;> decide
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) (223) = decide (1 ≤ countLit b [223]) := by
  change literal b (223) = decide (1 ≤ countLit b [223])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (223) <;> decide
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) (228) = decide (1 ≤ countLit b [228]) := by
  change literal b (228) = decide (1 ≤ countLit b [228])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (228) <;> decide
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) (230) = decide (1 ≤ countLit b [230]) := by
  change literal b (230) = decide (1 ≤ countLit b [230])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (230) <;> decide
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) (232) = decide (1 ≤ countLit b [232]) := by
  change literal b (232) = decide (1 ≤ countLit b [232])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (232) <;> decide
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) (233) = decide (1 ≤ countLit b [233]) := by
  change literal b (233) = decide (1 ≤ countLit b [233])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (233) <;> decide
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) (235) = decide (1 ≤ countLit b [235]) := by
  change literal b (235) = decide (1 ≤ countLit b [235])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (235) <;> decide
theorem meaning236 (b : Nat → Bool) : literal (valuationOf b) (236) = decide (1 ≤ countLit b [236]) := by
  change literal b (236) = decide (1 ≤ countLit b [236])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (236) <;> decide
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) (238) = decide (1 ≤ countLit b [238]) := by
  change literal b (238) = decide (1 ≤ countLit b [238])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (238) <;> decide
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) (240) = decide (1 ≤ countLit b [240]) := by
  change literal b (240) = decide (1 ≤ countLit b [240])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (240) <;> decide
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) (243) = decide (1 ≤ countLit b [243]) := by
  change literal b (243) = decide (1 ≤ countLit b [243])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (243) <;> decide
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) (245) = decide (1 ≤ countLit b [245]) := by
  change literal b (245) = decide (1 ≤ countLit b [245])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (245) <;> decide
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) (247) = decide (1 ≤ countLit b [247]) := by
  change literal b (247) = decide (1 ≤ countLit b [247])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (247) <;> decide
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) (249) = decide (1 ≤ countLit b [249]) := by
  change literal b (249) = decide (1 ≤ countLit b [249])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (249) <;> decide
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) (251) = decide (1 ≤ countLit b [251]) := by
  change literal b (251) = decide (1 ≤ countLit b [251])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (251) <;> decide
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) (253) = decide (1 ≤ countLit b [253]) := by
  change literal b (253) = decide (1 ≤ countLit b [253])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (253) <;> decide
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning264 (b : Nat → Bool) : literal (valuationOf b) 264 = decide (2 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning276 (b : Nat → Bool) : literal (valuationOf b) 276 = decide (2 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning278 (b : Nat → Bool) : literal (valuationOf b) 278 = decide (2 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning286 (b : Nat → Bool) : literal (valuationOf b) 286 = decide (2 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning288 (b : Nat → Bool) : literal (valuationOf b) 288 = decide (2 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
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
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning336 (b : Nat → Bool) : literal (valuationOf b) 336 = decide (2 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning364 (b : Nat → Bool) : literal (valuationOf b) 364 = decide (2 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning366 (b : Nat → Bool) : literal (valuationOf b) 366 = decide (2 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning370 (b : Nat → Bool) : literal (valuationOf b) 370 = decide (2 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning384 (b : Nat → Bool) : literal (valuationOf b) 384 = decide (2 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
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
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning452 (b : Nat → Bool) : literal (valuationOf b) 452 = decide (2 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning466 (b : Nat → Bool) : literal (valuationOf b) 466 = decide (2 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning479 (b : Nat → Bool) : literal (valuationOf b) 479 = decide (1 ≤ count479 b) := rfl
theorem meaning480 (b : Nat → Bool) : literal (valuationOf b) 480 = decide (2 ≤ count479 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning482 (b : Nat → Bool) : literal (valuationOf b) 482 = decide (2 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning487 (b : Nat → Bool) : literal (valuationOf b) 487 = decide (1 ≤ count487 b) := rfl
theorem meaning488 (b : Nat → Bool) : literal (valuationOf b) 488 = decide (2 ≤ count487 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning491 (b : Nat → Bool) : literal (valuationOf b) 491 = decide (1 ≤ count491 b) := rfl
theorem meaning493 (b : Nat → Bool) : literal (valuationOf b) 493 = decide (1 ≤ count493 b) := rfl
theorem meaning495 (b : Nat → Bool) : literal (valuationOf b) 495 = decide (1 ≤ count495 b) := rfl
theorem meaning496 (b : Nat → Bool) : literal (valuationOf b) 496 = decide (2 ≤ count495 b) := rfl
theorem meaning497 (b : Nat → Bool) : literal (valuationOf b) 497 = decide (1 ≤ count497 b) := rfl
theorem meaning498 (b : Nat → Bool) : literal (valuationOf b) 498 = decide (2 ≤ count497 b) := rfl
theorem meaning499 (b : Nat → Bool) : literal (valuationOf b) 499 = decide (1 ≤ count499 b) := rfl
theorem meaning500 (b : Nat → Bool) : literal (valuationOf b) 500 = decide (2 ≤ count499 b) := rfl
theorem meaning501 (b : Nat → Bool) : literal (valuationOf b) 501 = decide (1 ≤ count501 b) := rfl
theorem meaning502 (b : Nat → Bool) : literal (valuationOf b) 502 = decide (2 ≤ count501 b) := rfl
theorem meaning504 (b : Nat → Bool) : literal (valuationOf b) 504 = decide (2 ≤ count503 b) := rfl
theorem meaning849 (b : Nat → Bool) : literal (valuationOf b) 849 = decide (1 ≤ count849 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (2 ≤ count849 b) := rfl
theorem meaning851 (b : Nat → Bool) : literal (valuationOf b) 851 = decide (1 ≤ count851 b) := rfl
theorem meaning852 (b : Nat → Bool) : literal (valuationOf b) 852 = decide (2 ≤ count851 b) := rfl
theorem meaning853 (b : Nat → Bool) : literal (valuationOf b) 853 = decide (3 ≤ count851 b) := rfl
theorem meaning854 (b : Nat → Bool) : literal (valuationOf b) 854 = decide (1 ≤ count854 b) := rfl
theorem meaning855 (b : Nat → Bool) : literal (valuationOf b) 855 = decide (2 ≤ count854 b) := rfl
theorem meaning856 (b : Nat → Bool) : literal (valuationOf b) 856 = decide (1 ≤ count856 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (2 ≤ count856 b) := rfl
theorem meaning858 (b : Nat → Bool) : literal (valuationOf b) 858 = decide (1 ≤ count858 b) := rfl
theorem meaning859 (b : Nat → Bool) : literal (valuationOf b) 859 = decide (2 ≤ count858 b) := rfl
theorem meaning860 (b : Nat → Bool) : literal (valuationOf b) 860 = decide (3 ≤ count858 b) := rfl
theorem meaning861 (b : Nat → Bool) : literal (valuationOf b) 861 = decide (4 ≤ count858 b) := rfl
theorem meaning862 (b : Nat → Bool) : literal (valuationOf b) 862 = decide (1 ≤ count862 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (2 ≤ count862 b) := rfl
theorem meaning864 (b : Nat → Bool) : literal (valuationOf b) 864 = decide (3 ≤ count862 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (4 ≤ count862 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (5 ≤ count862 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (6 ≤ count862 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (7 ≤ count862 b) := rfl
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
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (1 ≤ count879 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (2 ≤ count879 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (1 ≤ count881 b) := rfl
theorem meaning882 (b : Nat → Bool) : literal (valuationOf b) 882 = decide (2 ≤ count881 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (3 ≤ count881 b) := rfl
theorem meaning884 (b : Nat → Bool) : literal (valuationOf b) 884 = decide (4 ≤ count881 b) := rfl
theorem meaning885 (b : Nat → Bool) : literal (valuationOf b) 885 = decide (1 ≤ count885 b) := rfl
theorem meaning886 (b : Nat → Bool) : literal (valuationOf b) 886 = decide (2 ≤ count885 b) := rfl
theorem meaning887 (b : Nat → Bool) : literal (valuationOf b) 887 = decide (3 ≤ count885 b) := rfl
theorem meaning888 (b : Nat → Bool) : literal (valuationOf b) 888 = decide (4 ≤ count885 b) := rfl
theorem meaning889 (b : Nat → Bool) : literal (valuationOf b) 889 = decide (5 ≤ count885 b) := rfl
theorem meaning890 (b : Nat → Bool) : literal (valuationOf b) 890 = decide (6 ≤ count885 b) := rfl
theorem meaning891 (b : Nat → Bool) : literal (valuationOf b) 891 = decide (7 ≤ count885 b) := rfl
theorem meaning893 (b : Nat → Bool) : literal (valuationOf b) 893 = decide (1 ≤ count893 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (2 ≤ count893 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (3 ≤ count893 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (4 ≤ count893 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (5 ≤ count893 b) := rfl
theorem meaning898 (b : Nat → Bool) : literal (valuationOf b) 898 = decide (6 ≤ count893 b) := rfl
theorem meaning899 (b : Nat → Bool) : literal (valuationOf b) 899 = decide (7 ≤ count893 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (8 ≤ count893 b) := rfl
theorem meaning901 (b : Nat → Bool) : literal (valuationOf b) 901 = decide (9 ≤ count893 b) := rfl
theorem meaning902 (b : Nat → Bool) : literal (valuationOf b) 902 = decide (10 ≤ count893 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (1 ≤ count908 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (2 ≤ count908 b) := rfl
theorem meaning910 (b : Nat → Bool) : literal (valuationOf b) 910 = decide (1 ≤ count910 b) := rfl
theorem meaning911 (b : Nat → Bool) : literal (valuationOf b) 911 = decide (2 ≤ count910 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (3 ≤ count910 b) := rfl
theorem meaning913 (b : Nat → Bool) : literal (valuationOf b) 913 = decide (1 ≤ count913 b) := rfl
theorem meaning914 (b : Nat → Bool) : literal (valuationOf b) 914 = decide (2 ≤ count913 b) := rfl
theorem meaning915 (b : Nat → Bool) : literal (valuationOf b) 915 = decide (1 ≤ count915 b) := rfl
theorem meaning916 (b : Nat → Bool) : literal (valuationOf b) 916 = decide (2 ≤ count915 b) := rfl
theorem meaning917 (b : Nat → Bool) : literal (valuationOf b) 917 = decide (1 ≤ count917 b) := rfl
theorem meaning918 (b : Nat → Bool) : literal (valuationOf b) 918 = decide (2 ≤ count917 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (3 ≤ count917 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (4 ≤ count917 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (1 ≤ count921 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (2 ≤ count921 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (3 ≤ count921 b) := rfl
theorem meaning924 (b : Nat → Bool) : literal (valuationOf b) 924 = decide (4 ≤ count921 b) := rfl
theorem meaning925 (b : Nat → Bool) : literal (valuationOf b) 925 = decide (5 ≤ count921 b) := rfl
theorem meaning926 (b : Nat → Bool) : literal (valuationOf b) 926 = decide (6 ≤ count921 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (7 ≤ count921 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (1 ≤ count928 b) := rfl
theorem meaning929 (b : Nat → Bool) : literal (valuationOf b) 929 = decide (2 ≤ count928 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (1 ≤ count930 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (2 ≤ count930 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (1 ≤ count932 b) := rfl
theorem meaning933 (b : Nat → Bool) : literal (valuationOf b) 933 = decide (2 ≤ count932 b) := rfl
theorem meaning934 (b : Nat → Bool) : literal (valuationOf b) 934 = decide (3 ≤ count932 b) := rfl
theorem meaning935 (b : Nat → Bool) : literal (valuationOf b) 935 = decide (4 ≤ count932 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (1 ≤ count936 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (2 ≤ count936 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (1 ≤ count938 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (2 ≤ count938 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (1 ≤ count940 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (2 ≤ count940 b) := rfl
theorem meaning942 (b : Nat → Bool) : literal (valuationOf b) 942 = decide (3 ≤ count940 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (4 ≤ count940 b) := rfl
theorem meaning944 (b : Nat → Bool) : literal (valuationOf b) 944 = decide (1 ≤ count944 b) := rfl
theorem meaning945 (b : Nat → Bool) : literal (valuationOf b) 945 = decide (2 ≤ count944 b) := rfl
theorem meaning946 (b : Nat → Bool) : literal (valuationOf b) 946 = decide (3 ≤ count944 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (4 ≤ count944 b) := rfl
theorem meaning948 (b : Nat → Bool) : literal (valuationOf b) 948 = decide (5 ≤ count944 b) := rfl
theorem meaning949 (b : Nat → Bool) : literal (valuationOf b) 949 = decide (6 ≤ count944 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (1 ≤ count952 b) := rfl
theorem meaning953 (b : Nat → Bool) : literal (valuationOf b) 953 = decide (2 ≤ count952 b) := rfl
theorem meaning954 (b : Nat → Bool) : literal (valuationOf b) 954 = decide (3 ≤ count952 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (4 ≤ count952 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (5 ≤ count952 b) := rfl
theorem meaning957 (b : Nat → Bool) : literal (valuationOf b) 957 = decide (6 ≤ count952 b) := rfl
theorem meaning958 (b : Nat → Bool) : literal (valuationOf b) 958 = decide (7 ≤ count952 b) := rfl
theorem meaning959 (b : Nat → Bool) : literal (valuationOf b) 959 = decide (8 ≤ count952 b) := rfl
theorem meaning960 (b : Nat → Bool) : literal (valuationOf b) 960 = decide (9 ≤ count952 b) := rfl
theorem meaning961 (b : Nat → Bool) : literal (valuationOf b) 961 = decide (10 ≤ count952 b) := rfl
theorem meaning962 (b : Nat → Bool) : literal (valuationOf b) 962 = decide (11 ≤ count952 b) := rfl
theorem meaning973 (b : Nat → Bool) : literal (valuationOf b) 973 = decide (7 ≤ count967 b) := rfl
theorem meaning974 (b : Nat → Bool) : literal (valuationOf b) 974 = decide (8 ≤ count967 b) := rfl
theorem meaning975 (b : Nat → Bool) : literal (valuationOf b) 975 = decide (9 ≤ count967 b) := rfl
theorem meaning976 (b : Nat → Bool) : literal (valuationOf b) 976 = decide (10 ≤ count967 b) := rfl
theorem meaning977 (b : Nat → Bool) : literal (valuationOf b) 977 = decide (11 ≤ count967 b) := rfl
theorem meaning978 (b : Nat → Bool) : literal (valuationOf b) 978 = decide (12 ≤ count967 b) := rfl
theorem meaning979 (b : Nat → Bool) : literal (valuationOf b) 979 = decide (13 ≤ count967 b) := rfl
theorem meaning980 (b : Nat → Bool) : literal (valuationOf b) 980 = decide (14 ≤ count967 b) := rfl
theorem meaning981 (b : Nat → Bool) : literal (valuationOf b) 981 = decide (15 ≤ count967 b) := rfl
theorem meaning982 (b : Nat → Bool) : literal (valuationOf b) 982 = decide (16 ≤ count967 b) := rfl
theorem meaning988 (b : Nat → Bool) : literal (valuationOf b) 988 = decide (1 ≤ count988 b) := rfl
theorem meaning989 (b : Nat → Bool) : literal (valuationOf b) 989 = decide (2 ≤ count988 b) := rfl
theorem meaning990 (b : Nat → Bool) : literal (valuationOf b) 990 = decide (1 ≤ count990 b) := rfl
theorem meaning991 (b : Nat → Bool) : literal (valuationOf b) 991 = decide (2 ≤ count990 b) := rfl
theorem meaning992 (b : Nat → Bool) : literal (valuationOf b) 992 = decide (3 ≤ count990 b) := rfl
theorem meaning993 (b : Nat → Bool) : literal (valuationOf b) 993 = decide (1 ≤ count993 b) := rfl
theorem meaning994 (b : Nat → Bool) : literal (valuationOf b) 994 = decide (2 ≤ count993 b) := rfl
theorem meaning995 (b : Nat → Bool) : literal (valuationOf b) 995 = decide (1 ≤ count995 b) := rfl
theorem meaning996 (b : Nat → Bool) : literal (valuationOf b) 996 = decide (2 ≤ count995 b) := rfl
theorem meaning997 (b : Nat → Bool) : literal (valuationOf b) 997 = decide (1 ≤ count997 b) := rfl
theorem meaning998 (b : Nat → Bool) : literal (valuationOf b) 998 = decide (2 ≤ count997 b) := rfl
theorem meaning999 (b : Nat → Bool) : literal (valuationOf b) 999 = decide (3 ≤ count997 b) := rfl
theorem meaning1000 (b : Nat → Bool) : literal (valuationOf b) 1000 = decide (4 ≤ count997 b) := rfl
theorem meaning1001 (b : Nat → Bool) : literal (valuationOf b) 1001 = decide (1 ≤ count1001 b) := rfl
theorem meaning1002 (b : Nat → Bool) : literal (valuationOf b) 1002 = decide (2 ≤ count1001 b) := rfl
theorem meaning1003 (b : Nat → Bool) : literal (valuationOf b) 1003 = decide (3 ≤ count1001 b) := rfl
theorem meaning1004 (b : Nat → Bool) : literal (valuationOf b) 1004 = decide (4 ≤ count1001 b) := rfl
theorem meaning1005 (b : Nat → Bool) : literal (valuationOf b) 1005 = decide (5 ≤ count1001 b) := rfl
theorem meaning1006 (b : Nat → Bool) : literal (valuationOf b) 1006 = decide (6 ≤ count1001 b) := rfl
theorem meaning1007 (b : Nat → Bool) : literal (valuationOf b) 1007 = decide (7 ≤ count1001 b) := rfl
theorem meaning1008 (b : Nat → Bool) : literal (valuationOf b) 1008 = decide (1 ≤ count1008 b) := rfl
theorem meaning1009 (b : Nat → Bool) : literal (valuationOf b) 1009 = decide (2 ≤ count1008 b) := rfl
theorem meaning1010 (b : Nat → Bool) : literal (valuationOf b) 1010 = decide (1 ≤ count1010 b) := rfl
theorem meaning1011 (b : Nat → Bool) : literal (valuationOf b) 1011 = decide (2 ≤ count1010 b) := rfl
theorem meaning1012 (b : Nat → Bool) : literal (valuationOf b) 1012 = decide (1 ≤ count1012 b) := rfl
theorem meaning1013 (b : Nat → Bool) : literal (valuationOf b) 1013 = decide (2 ≤ count1012 b) := rfl
theorem meaning1014 (b : Nat → Bool) : literal (valuationOf b) 1014 = decide (3 ≤ count1012 b) := rfl
theorem meaning1015 (b : Nat → Bool) : literal (valuationOf b) 1015 = decide (4 ≤ count1012 b) := rfl
theorem meaning1016 (b : Nat → Bool) : literal (valuationOf b) 1016 = decide (1 ≤ count1016 b) := rfl
theorem meaning1017 (b : Nat → Bool) : literal (valuationOf b) 1017 = decide (2 ≤ count1016 b) := rfl
theorem meaning1018 (b : Nat → Bool) : literal (valuationOf b) 1018 = decide (1 ≤ count1018 b) := rfl
theorem meaning1019 (b : Nat → Bool) : literal (valuationOf b) 1019 = decide (2 ≤ count1018 b) := rfl
theorem meaning1020 (b : Nat → Bool) : literal (valuationOf b) 1020 = decide (1 ≤ count1020 b) := rfl
theorem meaning1021 (b : Nat → Bool) : literal (valuationOf b) 1021 = decide (2 ≤ count1020 b) := rfl
theorem meaning1022 (b : Nat → Bool) : literal (valuationOf b) 1022 = decide (3 ≤ count1020 b) := rfl
theorem meaning1023 (b : Nat → Bool) : literal (valuationOf b) 1023 = decide (4 ≤ count1020 b) := rfl
theorem meaning1024 (b : Nat → Bool) : literal (valuationOf b) 1024 = decide (1 ≤ count1024 b) := rfl
theorem meaning1025 (b : Nat → Bool) : literal (valuationOf b) 1025 = decide (2 ≤ count1024 b) := rfl
theorem meaning1026 (b : Nat → Bool) : literal (valuationOf b) 1026 = decide (3 ≤ count1024 b) := rfl
theorem meaning1027 (b : Nat → Bool) : literal (valuationOf b) 1027 = decide (4 ≤ count1024 b) := rfl
theorem meaning1028 (b : Nat → Bool) : literal (valuationOf b) 1028 = decide (5 ≤ count1024 b) := rfl
theorem meaning1029 (b : Nat → Bool) : literal (valuationOf b) 1029 = decide (6 ≤ count1024 b) := rfl
theorem meaning1033 (b : Nat → Bool) : literal (valuationOf b) 1033 = decide (2 ≤ count1032 b) := rfl
theorem meaning1034 (b : Nat → Bool) : literal (valuationOf b) 1034 = decide (3 ≤ count1032 b) := rfl
theorem meaning1035 (b : Nat → Bool) : literal (valuationOf b) 1035 = decide (4 ≤ count1032 b) := rfl
theorem meaning1036 (b : Nat → Bool) : literal (valuationOf b) 1036 = decide (5 ≤ count1032 b) := rfl
theorem meaning1037 (b : Nat → Bool) : literal (valuationOf b) 1037 = decide (6 ≤ count1032 b) := rfl
theorem meaning1038 (b : Nat → Bool) : literal (valuationOf b) 1038 = decide (7 ≤ count1032 b) := rfl
theorem meaning1039 (b : Nat → Bool) : literal (valuationOf b) 1039 = decide (8 ≤ count1032 b) := rfl
theorem meaning1040 (b : Nat → Bool) : literal (valuationOf b) 1040 = decide (9 ≤ count1032 b) := rfl
theorem meaning1041 (b : Nat → Bool) : literal (valuationOf b) 1041 = decide (10 ≤ count1032 b) := rfl
theorem meaning1047 (b : Nat → Bool) : literal (valuationOf b) 1047 = decide (1 ≤ count1047 b) := rfl
theorem meaning1048 (b : Nat → Bool) : literal (valuationOf b) 1048 = decide (2 ≤ count1047 b) := rfl
theorem meaning1049 (b : Nat → Bool) : literal (valuationOf b) 1049 = decide (1 ≤ count1049 b) := rfl
theorem meaning1050 (b : Nat → Bool) : literal (valuationOf b) 1050 = decide (2 ≤ count1049 b) := rfl
theorem meaning1051 (b : Nat → Bool) : literal (valuationOf b) 1051 = decide (1 ≤ count1051 b) := rfl
theorem meaning1052 (b : Nat → Bool) : literal (valuationOf b) 1052 = decide (2 ≤ count1051 b) := rfl
theorem meaning1053 (b : Nat → Bool) : literal (valuationOf b) 1053 = decide (3 ≤ count1051 b) := rfl
theorem meaning1054 (b : Nat → Bool) : literal (valuationOf b) 1054 = decide (4 ≤ count1051 b) := rfl
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
theorem meaning1065 (b : Nat → Bool) : literal (valuationOf b) 1065 = decide (3 ≤ count1063 b) := rfl
theorem meaning1066 (b : Nat → Bool) : literal (valuationOf b) 1066 = decide (4 ≤ count1063 b) := rfl
theorem meaning1067 (b : Nat → Bool) : literal (valuationOf b) 1067 = decide (5 ≤ count1063 b) := rfl
theorem meaning1068 (b : Nat → Bool) : literal (valuationOf b) 1068 = decide (6 ≤ count1063 b) := rfl
theorem meaning1069 (b : Nat → Bool) : literal (valuationOf b) 1069 = decide (7 ≤ count1063 b) := rfl
theorem meaning1071 (b : Nat → Bool) : literal (valuationOf b) 1071 = decide (1 ≤ count1071 b) := rfl
theorem meaning1072 (b : Nat → Bool) : literal (valuationOf b) 1072 = decide (2 ≤ count1071 b) := rfl
theorem meaning1073 (b : Nat → Bool) : literal (valuationOf b) 1073 = decide (1 ≤ count1073 b) := rfl
theorem meaning1074 (b : Nat → Bool) : literal (valuationOf b) 1074 = decide (2 ≤ count1073 b) := rfl
theorem meaning1075 (b : Nat → Bool) : literal (valuationOf b) 1075 = decide (1 ≤ count1075 b) := rfl
theorem meaning1076 (b : Nat → Bool) : literal (valuationOf b) 1076 = decide (2 ≤ count1075 b) := rfl
theorem meaning1077 (b : Nat → Bool) : literal (valuationOf b) 1077 = decide (3 ≤ count1075 b) := rfl
theorem meaning1079 (b : Nat → Bool) : literal (valuationOf b) 1079 = decide (1 ≤ count1079 b) := rfl
theorem meaning1080 (b : Nat → Bool) : literal (valuationOf b) 1080 = decide (2 ≤ count1079 b) := rfl
theorem meaning1081 (b : Nat → Bool) : literal (valuationOf b) 1081 = decide (1 ≤ count1081 b) := rfl
theorem meaning1082 (b : Nat → Bool) : literal (valuationOf b) 1082 = decide (2 ≤ count1081 b) := rfl
theorem meaning1083 (b : Nat → Bool) : literal (valuationOf b) 1083 = decide (1 ≤ count1083 b) := rfl
theorem meaning1084 (b : Nat → Bool) : literal (valuationOf b) 1084 = decide (2 ≤ count1083 b) := rfl
theorem meaning1085 (b : Nat → Bool) : literal (valuationOf b) 1085 = decide (3 ≤ count1083 b) := rfl
theorem meaning1086 (b : Nat → Bool) : literal (valuationOf b) 1086 = decide (4 ≤ count1083 b) := rfl
theorem meaning1087 (b : Nat → Bool) : literal (valuationOf b) 1087 = decide (1 ≤ count1087 b) := rfl
theorem meaning1088 (b : Nat → Bool) : literal (valuationOf b) 1088 = decide (2 ≤ count1087 b) := rfl
theorem meaning1089 (b : Nat → Bool) : literal (valuationOf b) 1089 = decide (3 ≤ count1087 b) := rfl
theorem meaning1090 (b : Nat → Bool) : literal (valuationOf b) 1090 = decide (4 ≤ count1087 b) := rfl
theorem meaning1091 (b : Nat → Bool) : literal (valuationOf b) 1091 = decide (5 ≤ count1087 b) := rfl
theorem meaning1092 (b : Nat → Bool) : literal (valuationOf b) 1092 = decide (6 ≤ count1087 b) := rfl
theorem meaning1095 (b : Nat → Bool) : literal (valuationOf b) 1095 = decide (1 ≤ count1095 b) := rfl
theorem meaning1096 (b : Nat → Bool) : literal (valuationOf b) 1096 = decide (2 ≤ count1095 b) := rfl
theorem meaning1097 (b : Nat → Bool) : literal (valuationOf b) 1097 = decide (3 ≤ count1095 b) := rfl
theorem meaning1098 (b : Nat → Bool) : literal (valuationOf b) 1098 = decide (4 ≤ count1095 b) := rfl
theorem meaning1099 (b : Nat → Bool) : literal (valuationOf b) 1099 = decide (5 ≤ count1095 b) := rfl
theorem meaning1100 (b : Nat → Bool) : literal (valuationOf b) 1100 = decide (6 ≤ count1095 b) := rfl
theorem meaning1101 (b : Nat → Bool) : literal (valuationOf b) 1101 = decide (7 ≤ count1095 b) := rfl
theorem meaning1102 (b : Nat → Bool) : literal (valuationOf b) 1102 = decide (8 ≤ count1095 b) := rfl
theorem meaning1103 (b : Nat → Bool) : literal (valuationOf b) 1103 = decide (9 ≤ count1095 b) := rfl
theorem meaning1104 (b : Nat → Bool) : literal (valuationOf b) 1104 = decide (10 ≤ count1095 b) := rfl
theorem meaning1115 (b : Nat → Bool) : literal (valuationOf b) 1115 = decide (5 ≤ count1111 b) := rfl
theorem meaning1116 (b : Nat → Bool) : literal (valuationOf b) 1116 = decide (6 ≤ count1111 b) := rfl
theorem meaning1117 (b : Nat → Bool) : literal (valuationOf b) 1117 = decide (7 ≤ count1111 b) := rfl
theorem meaning1118 (b : Nat → Bool) : literal (valuationOf b) 1118 = decide (8 ≤ count1111 b) := rfl
theorem meaning1119 (b : Nat → Bool) : literal (valuationOf b) 1119 = decide (9 ≤ count1111 b) := rfl
theorem meaning1120 (b : Nat → Bool) : literal (valuationOf b) 1120 = decide (10 ≤ count1111 b) := rfl
theorem meaning1121 (b : Nat → Bool) : literal (valuationOf b) 1121 = decide (11 ≤ count1111 b) := rfl
theorem meaning1122 (b : Nat → Bool) : literal (valuationOf b) 1122 = decide (12 ≤ count1111 b) := rfl
theorem meaning1123 (b : Nat → Bool) : literal (valuationOf b) 1123 = decide (13 ≤ count1111 b) := rfl
theorem meaning1124 (b : Nat → Bool) : literal (valuationOf b) 1124 = decide (14 ≤ count1111 b) := rfl
theorem meaning1152 (b : Nat → Bool) : literal (valuationOf b) 1152 = decide (21 ≤ count1132 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (2 ≤ count1529 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (2 ≤ count1533 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (2 ≤ count1539 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (2 ≤ count1541 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (4 ≤ count1545 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (2 ≤ count1555 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (2 ≤ count1557 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (1 ≤ count1561 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (1 ≤ count1565 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (3 ≤ count1569 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (7 ≤ count1577 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (2 ≤ count1593 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (1 ≤ count1595 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (3 ≤ count1597 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (1 ≤ count1601 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (1 ≤ count1605 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (4 ≤ count1609 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (1 ≤ count1619 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (1 ≤ count1621 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (1 ≤ count1625 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (1 ≤ count1627 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (2 ≤ count1629 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (3 ≤ count1632 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (4 ≤ count1637 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (8 ≤ count1646 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (15 ≤ count1663 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (2 ≤ count1689 b) := rfl
theorem meaning1694 (b : Nat → Bool) : literal (valuationOf b) 1694 = decide (2 ≤ count1693 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (1 ≤ count1699 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (2 ≤ count1699 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (1 ≤ count1701 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (2 ≤ count1701 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (3 ≤ count1705 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (4 ≤ count1705 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (1 ≤ count1715 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (2 ≤ count1715 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (1 ≤ count1717 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (2 ≤ count1717 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (1 ≤ count1721 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (2 ≤ count1721 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (1 ≤ count1723 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (2 ≤ count1725 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (3 ≤ count1725 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (3 ≤ count1729 b) := rfl
theorem meaning1732 (b : Nat → Bool) : literal (valuationOf b) 1732 = decide (4 ≤ count1729 b) := rfl
theorem meaning1743 (b : Nat → Bool) : literal (valuationOf b) 1743 = decide (7 ≤ count1737 b) := rfl
theorem meaning1755 (b : Nat → Bool) : literal (valuationOf b) 1755 = decide (1 ≤ count1755 b) := rfl
theorem meaning1757 (b : Nat → Bool) : literal (valuationOf b) 1757 = decide (1 ≤ count1757 b) := rfl
theorem meaning1761 (b : Nat → Bool) : literal (valuationOf b) 1761 = decide (1 ≤ count1761 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (1 ≤ count1763 b) := rfl
theorem meaning1766 (b : Nat → Bool) : literal (valuationOf b) 1766 = decide (2 ≤ count1765 b) := rfl
theorem meaning1771 (b : Nat → Bool) : literal (valuationOf b) 1771 = decide (3 ≤ count1769 b) := rfl
theorem meaning1779 (b : Nat → Bool) : literal (valuationOf b) 1779 = decide (1 ≤ count1779 b) := rfl
theorem meaning1781 (b : Nat → Bool) : literal (valuationOf b) 1781 = decide (1 ≤ count1781 b) := rfl
theorem meaning1797 (b : Nat → Bool) : literal (valuationOf b) 1797 = decide (1 ≤ count1797 b) := rfl
theorem meaning1809 (b : Nat → Bool) : literal (valuationOf b) 1809 = decide (4 ≤ count1806 b) := rfl
theorem meaning1833 (b : Nat → Bool) : literal (valuationOf b) 1833 = decide (11 ≤ count1823 b) := rfl
theorem meaning1874 (b : Nat → Bool) : literal (valuationOf b) 1874 = decide (26 ≤ count1849 b) := rfl
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
end Snake9.Regrowth.E112256
