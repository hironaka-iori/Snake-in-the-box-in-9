import E112186Data
namespace Snake9.Regrowth.E112186
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 124 then (if i < 62 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (69 : Vertex)) else decide (InPath q (72 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (74 : Vertex)) else decide (InPath q (75 : Vertex))) else (if i < 6 then decide (InPath q (76 : Vertex)) else decide (InPath q (84 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (85 : Vertex)) else decide (InPath q (87 : Vertex))) else (if i < 10 then decide (InPath q (89 : Vertex)) else decide (InPath q (91 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (95 : Vertex)) else decide (InPath q (130 : Vertex))) else (if i < 14 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex)))))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then decide (InPath q (133 : Vertex)) else decide (InPath q (137 : Vertex))) else (if i < 18 then decide (InPath q (138 : Vertex)) else decide (InPath q (139 : Vertex)))) else (if i < 21 then (if i < 20 then decide (InPath q (140 : Vertex)) else decide (InPath q (142 : Vertex))) else (if i < 22 then decide (InPath q (144 : Vertex)) else decide (InPath q (148 : Vertex))))) else (if i < 27 then (if i < 25 then (if i < 24 then decide (InPath q (149 : Vertex)) else decide (InPath q (150 : Vertex))) else (if i < 26 then decide (InPath q (151 : Vertex)) else decide (InPath q (152 : Vertex)))) else (if i < 29 then (if i < 28 then decide (InPath q (153 : Vertex)) else decide (InPath q (155 : Vertex))) else (if i < 30 then decide (InPath q (159 : Vertex)) else decide (InPath q (192 : Vertex))))))) else (if i < 46 then (if i < 38 then (if i < 34 then (if i < 32 then decide (InPath q (193 : Vertex)) else (if i < 33 then decide (InPath q (197 : Vertex)) else decide (InPath q (199 : Vertex)))) else (if i < 36 then (if i < 35 then decide (InPath q (200 : Vertex)) else decide (InPath q (201 : Vertex))) else (if i < 37 then decide (InPath q (203 : Vertex)) else decide (InPath q (205 : Vertex))))) else (if i < 42 then (if i < 40 then (if i < 39 then decide (InPath q (207 : Vertex)) else decide (InPath q (209 : Vertex))) else (if i < 41 then decide (InPath q (210 : Vertex)) else decide (InPath q (211 : Vertex)))) else (if i < 44 then (if i < 43 then decide (InPath q (214 : Vertex)) else decide (InPath q (218 : Vertex))) else (if i < 45 then decide (InPath q (220 : Vertex)) else decide (InPath q (221 : Vertex)))))) else (if i < 54 then (if i < 50 then (if i < 48 then (if i < 47 then decide (InPath q (222 : Vertex)) else decide (InPath q (258 : Vertex))) else (if i < 49 then decide (InPath q (259 : Vertex)) else decide (InPath q (260 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (261 : Vertex)) else decide (InPath q (265 : Vertex))) else (if i < 53 then decide (InPath q (266 : Vertex)) else decide (InPath q (267 : Vertex))))) else (if i < 58 then (if i < 56 then (if i < 55 then decide (InPath q (268 : Vertex)) else decide (InPath q (270 : Vertex))) else (if i < 57 then decide (InPath q (272 : Vertex)) else decide (InPath q (276 : Vertex)))) else (if i < 60 then (if i < 59 then decide (InPath q (277 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 61 then decide (InPath q (280 : Vertex)) else decide (InPath q (281 : Vertex)))))))) else (if i < 93 then (if i < 77 then (if i < 69 then (if i < 65 then (if i < 63 then decide (InPath q (283 : Vertex)) else (if i < 64 then decide (InPath q (287 : Vertex)) else decide (InPath q (320 : Vertex)))) else (if i < 67 then (if i < 66 then decide (InPath q (321 : Vertex)) else decide (InPath q (322 : Vertex))) else (if i < 68 then decide (InPath q (323 : Vertex)) else decide (InPath q (325 : Vertex))))) else (if i < 73 then (if i < 71 then (if i < 70 then decide (InPath q (328 : Vertex)) else decide (InPath q (331 : Vertex))) else (if i < 72 then decide (InPath q (333 : Vertex)) else decide (InPath q (335 : Vertex)))) else (if i < 75 then (if i < 74 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex))) else (if i < 76 then decide (InPath q (339 : Vertex)) else decide (InPath q (342 : Vertex)))))) else (if i < 85 then (if i < 81 then (if i < 79 then (if i < 78 then decide (InPath q (344 : Vertex)) else decide (InPath q (348 : Vertex))) else (if i < 80 then decide (InPath q (349 : Vertex)) else decide (InPath q (350 : Vertex)))) else (if i < 83 then (if i < 82 then decide (InPath q (351 : Vertex)) else decide (InPath q (384 : Vertex))) else (if i < 84 then decide (InPath q (385 : Vertex)) else decide (InPath q (386 : Vertex))))) else (if i < 89 then (if i < 87 then (if i < 86 then decide (InPath q (387 : Vertex)) else decide (InPath q (389 : Vertex))) else (if i < 88 then decide (InPath q (391 : Vertex)) else decide (InPath q (393 : Vertex)))) else (if i < 91 then (if i < 90 then decide (InPath q (394 : Vertex)) else decide (InPath q (396 : Vertex))) else (if i < 92 then decide (InPath q (397 : Vertex)) else decide (InPath q (398 : Vertex))))))) else (if i < 108 then (if i < 100 then (if i < 96 then (if i < 94 then decide (InPath q (399 : Vertex)) else (if i < 95 then decide (InPath q (400 : Vertex)) else decide (InPath q (401 : Vertex)))) else (if i < 98 then (if i < 97 then decide (InPath q (402 : Vertex)) else decide (InPath q (403 : Vertex))) else (if i < 99 then decide (InPath q (406 : Vertex)) else decide (InPath q (408 : Vertex))))) else (if i < 104 then (if i < 102 then (if i < 101 then decide (InPath q (409 : Vertex)) else decide (InPath q (410 : Vertex))) else (if i < 103 then decide (InPath q (412 : Vertex)) else decide (InPath q (413 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (414 : Vertex)) else decide (InPath q (448 : Vertex))) else (if i < 107 then decide (InPath q (450 : Vertex)) else decide (InPath q (451 : Vertex)))))) else (if i < 116 then (if i < 112 then (if i < 110 then (if i < 109 then decide (InPath q (452 : Vertex)) else decide (InPath q (454 : Vertex))) else (if i < 111 then decide (InPath q (455 : Vertex)) else decide (InPath q (456 : Vertex)))) else (if i < 114 then (if i < 113 then decide (InPath q (457 : Vertex)) else decide (InPath q (458 : Vertex))) else (if i < 115 then decide (InPath q (460 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 120 then (if i < 118 then (if i < 117 then decide (InPath q (464 : Vertex)) else decide (InPath q (468 : Vertex))) else (if i < 119 then decide (InPath q (469 : Vertex)) else decide (InPath q (471 : Vertex)))) else (if i < 122 then (if i < 121 then decide (InPath q (473 : Vertex)) else decide (InPath q (474 : Vertex))) else (if i < 123 then decide (InPath q (475 : Vertex)) else decide (InPath q (477 : Vertex))))))))) else (if i < 186 then (if i < 155 then (if i < 139 then (if i < 131 then (if i < 127 then (if i < 125 then decide (InPath q (479 : Vertex)) else (if i < 126 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else decide (BallClauseLogic.Endpoint q (72 : Vertex)))) else (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (74 : Vertex)) else decide (BallClauseLogic.Endpoint q (75 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (76 : Vertex)) else decide (BallClauseLogic.Endpoint q (84 : Vertex))))) else (if i < 135 then (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (85 : Vertex)) else decide (BallClauseLogic.Endpoint q (87 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (89 : Vertex)) else decide (BallClauseLogic.Endpoint q (91 : Vertex)))) else (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex)))))) else (if i < 147 then (if i < 143 then (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (137 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex)))) else (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (142 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))))) else (if i < 151 then (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else decide (BallClauseLogic.Endpoint q (150 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (152 : Vertex)))) else (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (153 : Vertex)) else decide (BallClauseLogic.Endpoint q (155 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (159 : Vertex)) else decide (BallClauseLogic.Endpoint q (192 : Vertex))))))) else (if i < 170 then (if i < 162 then (if i < 158 then (if i < 156 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else (if i < 157 then decide (BallClauseLogic.Endpoint q (197 : Vertex)) else decide (BallClauseLogic.Endpoint q (199 : Vertex)))) else (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else decide (BallClauseLogic.Endpoint q (201 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (203 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex))))) else (if i < 166 then (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else decide (BallClauseLogic.Endpoint q (209 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (210 : Vertex)) else decide (BallClauseLogic.Endpoint q (211 : Vertex)))) else (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex)))))) else (if i < 178 then (if i < 174 then (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else decide (BallClauseLogic.Endpoint q (258 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex)))) else (if i < 176 then (if i < 175 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (265 : Vertex))) else (if i < 177 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex))))) else (if i < 182 then (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (270 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else decide (BallClauseLogic.Endpoint q (279 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else decide (BallClauseLogic.Endpoint q (281 : Vertex)))))))) else (if i < 217 then (if i < 201 then (if i < 193 then (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex)))) else (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (322 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (323 : Vertex)) else decide (BallClauseLogic.Endpoint q (325 : Vertex))))) else (if i < 197 then (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (328 : Vertex)) else decide (BallClauseLogic.Endpoint q (331 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (335 : Vertex)))) else (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (338 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (339 : Vertex)) else decide (BallClauseLogic.Endpoint q (342 : Vertex)))))) else (if i < 209 then (if i < 205 then (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (344 : Vertex)) else decide (BallClauseLogic.Endpoint q (348 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (351 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (386 : Vertex))))) else (if i < 213 then (if i < 211 then (if i < 210 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (389 : Vertex))) else (if i < 212 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (393 : Vertex)))) else (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (394 : Vertex)) else decide (BallClauseLogic.Endpoint q (396 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else decide (BallClauseLogic.Endpoint q (398 : Vertex))))))) else (if i < 233 then (if i < 225 then (if i < 221 then (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (399 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (402 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (406 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (408 : Vertex)) else decide (BallClauseLogic.Endpoint q (409 : Vertex))))) else (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (410 : Vertex)) else decide (BallClauseLogic.Endpoint q (412 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (448 : Vertex)) else decide (BallClauseLogic.Endpoint q (450 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (451 : Vertex)) else decide (BallClauseLogic.Endpoint q (452 : Vertex)))))) else (if i < 241 then (if i < 237 then (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (454 : Vertex)) else decide (BallClauseLogic.Endpoint q (455 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (456 : Vertex)) else decide (BallClauseLogic.Endpoint q (457 : Vertex)))) else (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (458 : Vertex)) else decide (BallClauseLogic.Endpoint q (460 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 245 then (if i < 243 then (if i < 242 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else decide (BallClauseLogic.Endpoint q (469 : Vertex))) else (if i < 244 then decide (BallClauseLogic.Endpoint q (471 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex)))) else (if i < 247 then (if i < 246 then decide (BallClauseLogic.Endpoint q (474 : Vertex)) else decide (BallClauseLogic.Endpoint q (475 : Vertex))) else (if i < 248 then decide (BallClauseLogic.Endpoint q (477 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [128, 129, 131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count271 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count359 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186]
def count361 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]
def count367 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count371 (b : Nat → Bool) : Nat := countLit b [187, 188, 189]
def count373 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193]
def count379 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193]
def count381 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197, 198, 199, 200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208, 209]
def count411 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count419 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count421 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217]
def count423 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213, 214, 215, 216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
def count427 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
def count429 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [218, 219, 220]
def count433 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224]
def count441 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count443 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count451 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]
def count457 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236]
def count463 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236, 237, 238, 239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count475 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244]
def count477 (b : Nat → Bool) : Nat := countLit b [245, 246]
def count479 (b : Nat → Bool) : Nat := countLit b [247, 248]
def count481 (b : Nat → Bool) : Nat := countLit b [245, 246, 247, 248]
def count483 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244, 245, 246, 247, 248]
def count485 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count487 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count489 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count491 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count493 (b : Nat → Bool) : Nat := countLit b [4, 7]
def count495 (b : Nat → Bool) : Nat := countLit b [2, 4, 7]
def count498 (b : Nat → Bool) : Nat := countLit b [9, 11]
def count500 (b : Nat → Bool) : Nat := countLit b [12, 14]
def count502 (b : Nat → Bool) : Nat := countLit b [9, 11, 12, 14]
def count506 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 11, 12, 14]
def count513 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count515 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count517 (b : Nat → Bool) : Nat := countLit b [18, 20, 21, 23]
def count521 (b : Nat → Bool) : Nat := countLit b [24, 27]
def count523 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count525 (b : Nat → Bool) : Nat := countLit b [24, 27, 29, 30]
def count529 (b : Nat → Bool) : Nat := countLit b [18, 20, 21, 23, 24, 27, 29, 30]
def count537 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 11, 12, 14, 18, 20, 21, 23, 24, 27, 29, 30]
def count552 (b : Nat → Bool) : Nat := countLit b [35, 38]
def count554 (b : Nat → Bool) : Nat := countLit b [32, 35, 38]
def count557 (b : Nat → Bool) : Nat := countLit b [39, 40]
def count559 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count561 (b : Nat → Bool) : Nat := countLit b [39, 40, 45, 46]
def count565 (b : Nat → Bool) : Nat := countLit b [32, 35, 38, 39, 40, 45, 46]
def count572 (b : Nat → Bool) : Nat := countLit b [47, 49]
def count574 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count576 (b : Nat → Bool) : Nat := countLit b [47, 49, 53, 55]
def count580 (b : Nat → Bool) : Nat := countLit b [56, 58]
def count582 (b : Nat → Bool) : Nat := countLit b [61, 63]
def count584 (b : Nat → Bool) : Nat := countLit b [56, 58, 61, 63]
def count588 (b : Nat → Bool) : Nat := countLit b [47, 49, 53, 55, 56, 58, 61, 63]
def count596 (b : Nat → Bool) : Nat := countLit b [32, 35, 38, 39, 40, 45, 46, 47, 49, 53, 55, 56, 58, 61, 63]
def count611 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 11, 12, 14, 18, 20, 21, 23, 24, 27, 29, 30, 32, 35, 38, 39, 40, 45, 46, 47, 49, 53, 55, 56, 58, 61, 63]
def count641 (b : Nat → Bool) : Nat := countLit b [67, 68]
def count643 (b : Nat → Bool) : Nat := countLit b [64, 67, 68]
def count646 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count648 (b : Nat → Bool) : Nat := countLit b [74, 77]
def count650 (b : Nat → Bool) : Nat := countLit b [72, 73, 74, 77]
def count654 (b : Nat → Bool) : Nat := countLit b [64, 67, 68, 72, 73, 74, 77]
def count661 (b : Nat → Bool) : Nat := countLit b [79, 80]
def count663 (b : Nat → Bool) : Nat := countLit b [82, 85]
def count665 (b : Nat → Bool) : Nat := countLit b [79, 80, 82, 85]
def count669 (b : Nat → Bool) : Nat := countLit b [86, 88]
def count671 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count673 (b : Nat → Bool) : Nat := countLit b [86, 88, 89, 90]
def count677 (b : Nat → Bool) : Nat := countLit b [79, 80, 82, 85, 86, 88, 89, 90]
def count685 (b : Nat → Bool) : Nat := countLit b [64, 67, 68, 72, 73, 74, 77, 79, 80, 82, 85, 86, 88, 89, 90]
def count700 (b : Nat → Bool) : Nat := countLit b [93, 95]
def count702 (b : Nat → Bool) : Nat := countLit b [96, 99]
def count704 (b : Nat → Bool) : Nat := countLit b [93, 95, 96, 99]
def count708 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count710 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count712 (b : Nat → Bool) : Nat := countLit b [103, 104, 106, 108]
def count716 (b : Nat → Bool) : Nat := countLit b [93, 95, 96, 99, 103, 104, 106, 108]
def count724 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count726 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count728 (b : Nat → Bool) : Nat := countLit b [110, 111, 115, 116]
def count732 (b : Nat → Bool) : Nat := countLit b [118, 120]
def count734 (b : Nat → Bool) : Nat := countLit b [121, 124]
def count736 (b : Nat → Bool) : Nat := countLit b [118, 120, 121, 124]
def count740 (b : Nat → Bool) : Nat := countLit b [110, 111, 115, 116, 118, 120, 121, 124]
def count748 (b : Nat → Bool) : Nat := countLit b [93, 95, 96, 99, 103, 104, 106, 108, 110, 111, 115, 116, 118, 120, 121, 124]
def count764 (b : Nat → Bool) : Nat := countLit b [64, 67, 68, 72, 73, 74, 77, 79, 80, 82, 85, 86, 88, 89, 90, 93, 95, 96, 99, 103, 104, 106, 108, 110, 111, 115, 116, 118, 120, 121, 124]
def count795 (b : Nat → Bool) : Nat := countLit b [2, 4, 7, 9, 11, 12, 14, 18, 20, 21, 23, 24, 27, 29, 30, 32, 35, 38, 39, 40, 45, 46, 47, 49, 53, 55, 56, 58, 61, 63, 64, 67, 68, 72, 73, 74, 77, 79, 80, 82, 85, 86, 88, 89, 90, 93, 95, 96, 99, 103, 104, 106, 108, 110, 111, 115, 116, 118, 120, 121, 124]
def count837 (b : Nat → Bool) : Nat := countLit b [-4, -7]
def count839 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7]
def count842 (b : Nat → Bool) : Nat := countLit b [-9, -11]
def count844 (b : Nat → Bool) : Nat := countLit b [-12, -14]
def count846 (b : Nat → Bool) : Nat := countLit b [-9, -11, -12, -14]
def count850 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -11, -12, -14]
def count857 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count859 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count861 (b : Nat → Bool) : Nat := countLit b [-18, -20, -21, -23]
def count865 (b : Nat → Bool) : Nat := countLit b [-24, -27]
def count867 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count869 (b : Nat → Bool) : Nat := countLit b [-24, -27, -29, -30]
def count873 (b : Nat → Bool) : Nat := countLit b [-18, -20, -21, -23, -24, -27, -29, -30]
def count881 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -30]
def count896 (b : Nat → Bool) : Nat := countLit b [-35, -38]
def count898 (b : Nat → Bool) : Nat := countLit b [-32, -35, -38]
def count901 (b : Nat → Bool) : Nat := countLit b [-39, -40]
def count903 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count905 (b : Nat → Bool) : Nat := countLit b [-39, -40, -45, -46]
def count909 (b : Nat → Bool) : Nat := countLit b [-32, -35, -38, -39, -40, -45, -46]
def count916 (b : Nat → Bool) : Nat := countLit b [-47, -49]
def count918 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count920 (b : Nat → Bool) : Nat := countLit b [-47, -49, -53, -55]
def count924 (b : Nat → Bool) : Nat := countLit b [-56, -58]
def count926 (b : Nat → Bool) : Nat := countLit b [-61, -63]
def count928 (b : Nat → Bool) : Nat := countLit b [-56, -58, -61, -63]
def count932 (b : Nat → Bool) : Nat := countLit b [-47, -49, -53, -55, -56, -58, -61, -63]
def count940 (b : Nat → Bool) : Nat := countLit b [-32, -35, -38, -39, -40, -45, -46, -47, -49, -53, -55, -56, -58, -61, -63]
def count955 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -30, -32, -35, -38, -39, -40, -45, -46, -47, -49, -53, -55, -56, -58, -61, -63]
def count976 (b : Nat → Bool) : Nat := countLit b [-67, -68]
def count978 (b : Nat → Bool) : Nat := countLit b [-64, -67, -68]
def count981 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count983 (b : Nat → Bool) : Nat := countLit b [-74, -77]
def count985 (b : Nat → Bool) : Nat := countLit b [-72, -73, -74, -77]
def count989 (b : Nat → Bool) : Nat := countLit b [-64, -67, -68, -72, -73, -74, -77]
def count996 (b : Nat → Bool) : Nat := countLit b [-79, -80]
def count998 (b : Nat → Bool) : Nat := countLit b [-82, -85]
def count1000 (b : Nat → Bool) : Nat := countLit b [-79, -80, -82, -85]
def count1004 (b : Nat → Bool) : Nat := countLit b [-86, -88]
def count1006 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count1008 (b : Nat → Bool) : Nat := countLit b [-86, -88, -89, -90]
def count1012 (b : Nat → Bool) : Nat := countLit b [-79, -80, -82, -85, -86, -88, -89, -90]
def count1020 (b : Nat → Bool) : Nat := countLit b [-64, -67, -68, -72, -73, -74, -77, -79, -80, -82, -85, -86, -88, -89, -90]
def count1035 (b : Nat → Bool) : Nat := countLit b [-93, -95]
def count1037 (b : Nat → Bool) : Nat := countLit b [-96, -99]
def count1039 (b : Nat → Bool) : Nat := countLit b [-93, -95, -96, -99]
def count1043 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1045 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count1047 (b : Nat → Bool) : Nat := countLit b [-103, -104, -106, -108]
def count1051 (b : Nat → Bool) : Nat := countLit b [-93, -95, -96, -99, -103, -104, -106, -108]
def count1059 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1061 (b : Nat → Bool) : Nat := countLit b [-115, -116]
def count1063 (b : Nat → Bool) : Nat := countLit b [-110, -111, -115, -116]
def count1067 (b : Nat → Bool) : Nat := countLit b [-118, -120]
def count1069 (b : Nat → Bool) : Nat := countLit b [-121, -124]
def count1071 (b : Nat → Bool) : Nat := countLit b [-118, -120, -121, -124]
def count1075 (b : Nat → Bool) : Nat := countLit b [-110, -111, -115, -116, -118, -120, -121, -124]
def count1083 (b : Nat → Bool) : Nat := countLit b [-93, -95, -96, -99, -103, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -124]
def count1099 (b : Nat → Bool) : Nat := countLit b [-64, -67, -68, -72, -73, -74, -77, -79, -80, -82, -85, -86, -88, -89, -90, -93, -95, -96, -99, -103, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -124]
def count1120 (b : Nat → Bool) : Nat := countLit b [-2, -4, -7, -9, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -30, -32, -35, -38, -39, -40, -45, -46, -47, -49, -53, -55, -56, -58, -61, -63, -64, -67, -68, -72, -73, -74, -77, -79, -80, -82, -85, -86, -88, -89, -90, -93, -95, -96, -99, -103, -104, -106, -108, -110, -111, -115, -116, -118, -120, -121, -124]
def count1141 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count1143 (b : Nat → Bool) : Nat := countLit b [1, 3, 5]
def count1146 (b : Nat → Bool) : Nat := countLit b [6, 8]
def count1148 (b : Nat → Bool) : Nat := countLit b [10, 13]
def count1150 (b : Nat → Bool) : Nat := countLit b [6, 8, 10, 13]
def count1154 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 13]
def count1161 (b : Nat → Bool) : Nat := countLit b [15, 16]
def count1163 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count1165 (b : Nat → Bool) : Nat := countLit b [15, 16, 17, 19]
def count1169 (b : Nat → Bool) : Nat := countLit b [22, 25]
def count1171 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count1173 (b : Nat → Bool) : Nat := countLit b [22, 25, 26, 28]
def count1177 (b : Nat → Bool) : Nat := countLit b [15, 16, 17, 19, 22, 25, 26, 28]
def count1185 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 13, 15, 16, 17, 19, 22, 25, 26, 28]
def count1200 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count1202 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count1204 (b : Nat → Bool) : Nat := countLit b [31, 33, 34, 36]
def count1208 (b : Nat → Bool) : Nat := countLit b [37, 41]
def count1210 (b : Nat → Bool) : Nat := countLit b [42, 43]
def count1212 (b : Nat → Bool) : Nat := countLit b [37, 41, 42, 43]
def count1216 (b : Nat → Bool) : Nat := countLit b [31, 33, 34, 36, 37, 41, 42, 43]
def count1224 (b : Nat → Bool) : Nat := countLit b [44, 48]
def count1226 (b : Nat → Bool) : Nat := countLit b [50, 51]
def count1228 (b : Nat → Bool) : Nat := countLit b [44, 48, 50, 51]
def count1232 (b : Nat → Bool) : Nat := countLit b [52, 54]
def count1234 (b : Nat → Bool) : Nat := countLit b [57, 59]
def count1236 (b : Nat → Bool) : Nat := countLit b [52, 54, 57, 59]
def count1240 (b : Nat → Bool) : Nat := countLit b [44, 48, 50, 51, 52, 54, 57, 59]
def count1248 (b : Nat → Bool) : Nat := countLit b [31, 33, 34, 36, 37, 41, 42, 43, 44, 48, 50, 51, 52, 54, 57, 59]
def count1264 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 13, 15, 16, 17, 19, 22, 25, 26, 28, 31, 33, 34, 36, 37, 41, 42, 43, 44, 48, 50, 51, 52, 54, 57, 59]
def count1295 (b : Nat → Bool) : Nat := countLit b [60, 62]
def count1297 (b : Nat → Bool) : Nat := countLit b [65, 66]
def count1299 (b : Nat → Bool) : Nat := countLit b [60, 62, 65, 66]
def count1303 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count1305 (b : Nat → Bool) : Nat := countLit b [71, 75]
def count1307 (b : Nat → Bool) : Nat := countLit b [69, 70, 71, 75]
def count1311 (b : Nat → Bool) : Nat := countLit b [60, 62, 65, 66, 69, 70, 71, 75]
def count1319 (b : Nat → Bool) : Nat := countLit b [76, 78]
def count1321 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count1323 (b : Nat → Bool) : Nat := countLit b [76, 78, 81, 83]
def count1327 (b : Nat → Bool) : Nat := countLit b [84, 87]
def count1329 (b : Nat → Bool) : Nat := countLit b [91, 92]
def count1331 (b : Nat → Bool) : Nat := countLit b [84, 87, 91, 92]
def count1335 (b : Nat → Bool) : Nat := countLit b [76, 78, 81, 83, 84, 87, 91, 92]
def count1343 (b : Nat → Bool) : Nat := countLit b [60, 62, 65, 66, 69, 70, 71, 75, 76, 78, 81, 83, 84, 87, 91, 92]
def count1359 (b : Nat → Bool) : Nat := countLit b [94, 97]
def count1361 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count1363 (b : Nat → Bool) : Nat := countLit b [94, 97, 98, 100]
def count1367 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count1369 (b : Nat → Bool) : Nat := countLit b [105, 107]
def count1371 (b : Nat → Bool) : Nat := countLit b [101, 102, 105, 107]
def count1375 (b : Nat → Bool) : Nat := countLit b [94, 97, 98, 100, 101, 102, 105, 107]
def count1383 (b : Nat → Bool) : Nat := countLit b [109, 112]
def count1385 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count1387 (b : Nat → Bool) : Nat := countLit b [109, 112, 113, 114]
def count1391 (b : Nat → Bool) : Nat := countLit b [117, 119]
def count1393 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count1395 (b : Nat → Bool) : Nat := countLit b [117, 119, 122, 123]
def count1399 (b : Nat → Bool) : Nat := countLit b [109, 112, 113, 114, 117, 119, 122, 123]
def count1407 (b : Nat → Bool) : Nat := countLit b [94, 97, 98, 100, 101, 102, 105, 107, 109, 112, 113, 114, 117, 119, 122, 123]
def count1423 (b : Nat → Bool) : Nat := countLit b [60, 62, 65, 66, 69, 70, 71, 75, 76, 78, 81, 83, 84, 87, 91, 92, 94, 97, 98, 100, 101, 102, 105, 107, 109, 112, 113, 114, 117, 119, 122, 123]
def count1455 (b : Nat → Bool) : Nat := countLit b [1, 3, 5, 6, 8, 10, 13, 15, 16, 17, 19, 22, 25, 26, 28, 31, 33, 34, 36, 37, 41, 42, 43, 44, 48, 50, 51, 52, 54, 57, 59, 60, 62, 65, 66, 69, 70, 71, 75, 76, 78, 81, 83, 84, 87, 91, 92, 94, 97, 98, 100, 101, 102, 105, 107, 109, 112, 113, 114, 117, 119, 122, 123]
def count1497 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1499 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5]
def count1502 (b : Nat → Bool) : Nat := countLit b [-6, -8]
def count1504 (b : Nat → Bool) : Nat := countLit b [-10, -13]
def count1506 (b : Nat → Bool) : Nat := countLit b [-6, -8, -10, -13]
def count1510 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -13]
def count1517 (b : Nat → Bool) : Nat := countLit b [-15, -16]
def count1519 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count1521 (b : Nat → Bool) : Nat := countLit b [-15, -16, -17, -19]
def count1525 (b : Nat → Bool) : Nat := countLit b [-22, -25]
def count1527 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count1529 (b : Nat → Bool) : Nat := countLit b [-22, -25, -26, -28]
def count1533 (b : Nat → Bool) : Nat := countLit b [-15, -16, -17, -19, -22, -25, -26, -28]
def count1541 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28]
def count1556 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count1558 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count1560 (b : Nat → Bool) : Nat := countLit b [-31, -33, -34, -36]
def count1564 (b : Nat → Bool) : Nat := countLit b [-37, -41]
def count1566 (b : Nat → Bool) : Nat := countLit b [-42, -43]
def count1568 (b : Nat → Bool) : Nat := countLit b [-37, -41, -42, -43]
def count1572 (b : Nat → Bool) : Nat := countLit b [-31, -33, -34, -36, -37, -41, -42, -43]
def count1580 (b : Nat → Bool) : Nat := countLit b [-44, -48]
def count1582 (b : Nat → Bool) : Nat := countLit b [-50, -51]
def count1584 (b : Nat → Bool) : Nat := countLit b [-44, -48, -50, -51]
def count1588 (b : Nat → Bool) : Nat := countLit b [-52, -54]
def count1590 (b : Nat → Bool) : Nat := countLit b [-57, -59]
def count1592 (b : Nat → Bool) : Nat := countLit b [-52, -54, -57, -59]
def count1596 (b : Nat → Bool) : Nat := countLit b [-44, -48, -50, -51, -52, -54, -57, -59]
def count1604 (b : Nat → Bool) : Nat := countLit b [-31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]
def count1620 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]
def count1643 (b : Nat → Bool) : Nat := countLit b [-60, -62]
def count1645 (b : Nat → Bool) : Nat := countLit b [-65, -66]
def count1647 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65, -66]
def count1651 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count1653 (b : Nat → Bool) : Nat := countLit b [-71, -75]
def count1655 (b : Nat → Bool) : Nat := countLit b [-69, -70, -71, -75]
def count1659 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65, -66, -69, -70, -71, -75]
def count1667 (b : Nat → Bool) : Nat := countLit b [-76, -78]
def count1669 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count1671 (b : Nat → Bool) : Nat := countLit b [-76, -78, -81, -83]
def count1675 (b : Nat → Bool) : Nat := countLit b [-84, -87]
def count1677 (b : Nat → Bool) : Nat := countLit b [-91, -92]
def count1679 (b : Nat → Bool) : Nat := countLit b [-84, -87, -91, -92]
def count1683 (b : Nat → Bool) : Nat := countLit b [-76, -78, -81, -83, -84, -87, -91, -92]
def count1691 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]
def count1707 (b : Nat → Bool) : Nat := countLit b [-94, -97]
def count1709 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count1711 (b : Nat → Bool) : Nat := countLit b [-94, -97, -98, -100]
def count1715 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count1717 (b : Nat → Bool) : Nat := countLit b [-105, -107]
def count1719 (b : Nat → Bool) : Nat := countLit b [-101, -102, -105, -107]
def count1723 (b : Nat → Bool) : Nat := countLit b [-94, -97, -98, -100, -101, -102, -105, -107]
def count1731 (b : Nat → Bool) : Nat := countLit b [-109, -112]
def count1733 (b : Nat → Bool) : Nat := countLit b [-113, -114]
def count1735 (b : Nat → Bool) : Nat := countLit b [-109, -112, -113, -114]
def count1739 (b : Nat → Bool) : Nat := countLit b [-117, -119]
def count1741 (b : Nat → Bool) : Nat := countLit b [-122, -123]
def count1743 (b : Nat → Bool) : Nat := countLit b [-117, -119, -122, -123]
def count1747 (b : Nat → Bool) : Nat := countLit b [-109, -112, -113, -114, -117, -119, -122, -123]
def count1755 (b : Nat → Bool) : Nat := countLit b [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]
def count1771 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]
def count1794 (b : Nat → Bool) : Nat := countLit b [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59, -60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 908 then (if i < 454 then (if i < 227 then (if i < 113 then (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 24 then (if i < 22 then b 21 else (if i < 23 then b 22 else b 23)) else (if i < 26 then (if i < 25 then b 24 else b 25) else (if i < 27 then b 26 else b 27))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 33 then (if i < 32 then b 31 else b 32) else (if i < 34 then b 33 else b 34))) else (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 40 then (if i < 39 then b 38 else b 39) else (if i < 41 then b 40 else b 41)))) else (if i < 49 then (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else b 48))) else (if i < 52 then (if i < 50 then b 49 else (if i < 51 then b 50 else b 51)) else (if i < 54 then (if i < 53 then b 52 else b 53) else (if i < 55 then b 54 else b 55)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then b 56 else (if i < 58 then b 57 else b 58)) else (if i < 61 then (if i < 60 then b 59 else b 60) else (if i < 62 then b 61 else b 62))) else (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 68 then (if i < 67 then b 66 else b 67) else (if i < 69 then b 68 else b 69)))) else (if i < 77 then (if i < 73 then (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)) else (if i < 75 then (if i < 74 then b 73 else b 74) else (if i < 76 then b 75 else b 76))) else (if i < 80 then (if i < 78 then b 77 else (if i < 79 then b 78 else b 79)) else (if i < 82 then (if i < 81 then b 80 else b 81) else (if i < 83 then b 82 else b 83))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90))) else (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else b 97)))) else (if i < 105 then (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else b 104))) else (if i < 109 then (if i < 107 then (if i < 106 then b 105 else b 106) else (if i < 108 then b 107 else b 108)) else (if i < 111 then (if i < 110 then b 109 else b 110) else (if i < 112 then b 111 else b 112))))))) else (if i < 170 then (if i < 141 then (if i < 127 then (if i < 120 then (if i < 116 then (if i < 114 then b 113 else (if i < 115 then b 114 else b 115)) else (if i < 118 then (if i < 117 then b 116 else b 117) else (if i < 119 then b 118 else b 119))) else (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 125 then (if i < 124 then b 123 else b 124) else (if i < 126 then b 125 else b 126)))) else (if i < 134 then (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 132 then (if i < 131 then b 130 else b 131) else (if i < 133 then b 132 else b 133))) else (if i < 137 then (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)) else (if i < 139 then (if i < 138 then b 137 else b 138) else (if i < 140 then b 139 else b 140))))) else (if i < 155 then (if i < 148 then (if i < 144 then (if i < 142 then b 141 else (if i < 143 then b 142 else b 143)) else (if i < 146 then (if i < 145 then b 144 else b 145) else (if i < 147 then b 146 else b 147))) else (if i < 151 then (if i < 149 then b 148 else (if i < 150 then b 149 else b 150)) else (if i < 153 then (if i < 152 then b 151 else b 152) else (if i < 154 then b 153 else b 154)))) else (if i < 162 then (if i < 158 then (if i < 156 then b 155 else (if i < 157 then b 156 else b 157)) else (if i < 160 then (if i < 159 then b 158 else b 159) else (if i < 161 then b 160 else b 161))) else (if i < 166 then (if i < 164 then (if i < 163 then b 162 else b 163) else (if i < 165 then b 164 else b 165)) else (if i < 168 then (if i < 167 then b 166 else b 167) else (if i < 169 then b 168 else b 169)))))) else (if i < 198 then (if i < 184 then (if i < 177 then (if i < 173 then (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)) else (if i < 175 then (if i < 174 then b 173 else b 174) else (if i < 176 then b 175 else b 176))) else (if i < 180 then (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)) else (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else b 183)))) else (if i < 191 then (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 189 then (if i < 188 then b 187 else b 188) else (if i < 190 then b 189 else b 190))) else (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else b 197))))) else (if i < 212 then (if i < 205 then (if i < 201 then (if i < 199 then b 198 else (if i < 200 then b 199 else b 200)) else (if i < 203 then (if i < 202 then b 201 else b 202) else (if i < 204 then b 203 else b 204))) else (if i < 208 then (if i < 206 then b 205 else (if i < 207 then b 206 else b 207)) else (if i < 210 then (if i < 209 then b 208 else b 209) else (if i < 211 then b 210 else b 211)))) else (if i < 219 then (if i < 215 then (if i < 213 then b 212 else (if i < 214 then b 213 else b 214)) else (if i < 217 then (if i < 216 then b 215 else b 216) else (if i < 218 then b 217 else b 218))) else (if i < 223 then (if i < 221 then (if i < 220 then b 219 else b 220) else (if i < 222 then b 221 else b 222)) else (if i < 225 then (if i < 224 then b 223 else b 224) else (if i < 226 then b 225 else b 226)))))))) else (if i < 340 then (if i < 283 then (if i < 255 then (if i < 241 then (if i < 234 then (if i < 230 then (if i < 228 then b 227 else (if i < 229 then b 228 else b 229)) else (if i < 232 then (if i < 231 then b 230 else b 231) else (if i < 233 then b 232 else b 233))) else (if i < 237 then (if i < 235 then b 234 else (if i < 236 then b 235 else b 236)) else (if i < 239 then (if i < 238 then b 237 else b 238) else (if i < 240 then b 239 else b 240)))) else (if i < 248 then (if i < 244 then (if i < 242 then b 241 else (if i < 243 then b 242 else b 243)) else (if i < 246 then (if i < 245 then b 244 else b 245) else (if i < 247 then b 246 else b 247))) else (if i < 251 then (if i < 249 then b 248 else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 253 then (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b)))))) else (if i < 269 then (if i < 262 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 260 then (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))) else (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 267 then (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b))))) else (if i < 276 then (if i < 272 then (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))) else (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)))) else (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 281 then (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))))))) else (if i < 311 then (if i < 297 then (if i < 290 then (if i < 286 then (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b))) else (if i < 288 then (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b)) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)))) else (if i < 293 then (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))) else (if i < 295 then (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b))))) else (if i < 304 then (if i < 300 then (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))) else (if i < 302 then (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)))) else (if i < 307 then (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))) else (if i < 309 then (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)))))) else (if i < 325 then (if i < 318 then (if i < 314 then (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b))) else (if i < 316 then (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)))) else (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 323 then (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))) else (if i < 332 then (if i < 328 then (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))) else (if i < 330 then (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 336 then (if i < 334 then (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 338 then (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)))))))) else (if i < 397 then (if i < 368 then (if i < 354 then (if i < 347 then (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))) else (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))))) else (if i < 361 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))) else (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)))))) else (if i < 382 then (if i < 375 then (if i < 371 then (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))) else (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 378 then (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))) else (if i < 380 then (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))))) else (if i < 389 then (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 387 then (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 393 then (if i < 391 then (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))) else (if i < 395 then (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))))))) else (if i < 425 then (if i < 411 then (if i < 404 then (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))) else (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))))) else (if i < 418 then (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 416 then (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)))) else (if i < 421 then (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))) else (if i < 423 then (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b)) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b)))))) else (if i < 439 then (if i < 432 then (if i < 428 then (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b))) else (if i < 430 then (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b)) else (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)))) else (if i < 435 then (if i < 433 then decide (2 ≤ count431 b) else (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b))) else (if i < 437 then (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b))))) else (if i < 446 then (if i < 442 then (if i < 440 then decide (1 ≤ count439 b) else (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b))) else (if i < 444 then (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)) else (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)))) else (if i < 450 then (if i < 448 then (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b)) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b))) else (if i < 452 then (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)) else (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b)))))))))) else (if i < 681 then (if i < 567 then (if i < 510 then (if i < 482 then (if i < 468 then (if i < 461 then (if i < 457 then (if i < 455 then decide (2 ≤ count453 b) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))) else (if i < 459 then (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)))) else (if i < 464 then (if i < 462 then decide (1 ≤ count461 b) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b))) else (if i < 466 then (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b)) else (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b))))) else (if i < 475 then (if i < 471 then (if i < 469 then decide (2 ≤ count467 b) else (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b))) else (if i < 473 then (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b)) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)))) else (if i < 478 then (if i < 476 then decide (1 ≤ count475 b) else (if i < 477 then decide (2 ≤ count475 b) else decide (1 ≤ count477 b))) else (if i < 480 then (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b)) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b)))))) else (if i < 496 then (if i < 489 then (if i < 485 then (if i < 483 then decide (2 ≤ count481 b) else (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b))) else (if i < 487 then (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b)) else (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b)))) else (if i < 492 then (if i < 490 then decide (1 ≤ count489 b) else (if i < 491 then decide (2 ≤ count489 b) else decide (1 ≤ count491 b))) else (if i < 494 then (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b)) else (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b))))) else (if i < 503 then (if i < 499 then (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (3 ≤ count495 b) else decide (1 ≤ count498 b))) else (if i < 501 then (if i < 500 then decide (2 ≤ count498 b) else decide (1 ≤ count500 b)) else (if i < 502 then decide (2 ≤ count500 b) else decide (1 ≤ count502 b)))) else (if i < 506 then (if i < 504 then decide (2 ≤ count502 b) else (if i < 505 then decide (3 ≤ count502 b) else decide (4 ≤ count502 b))) else (if i < 508 then (if i < 507 then decide (1 ≤ count506 b) else decide (2 ≤ count506 b)) else (if i < 509 then decide (3 ≤ count506 b) else decide (4 ≤ count506 b))))))) else (if i < 538 then (if i < 524 then (if i < 517 then (if i < 513 then (if i < 511 then decide (5 ≤ count506 b) else (if i < 512 then decide (6 ≤ count506 b) else decide (7 ≤ count506 b))) else (if i < 515 then (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b)) else (if i < 516 then decide (1 ≤ count515 b) else decide (2 ≤ count515 b)))) else (if i < 520 then (if i < 518 then decide (1 ≤ count517 b) else (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b))) else (if i < 522 then (if i < 521 then decide (4 ≤ count517 b) else decide (1 ≤ count521 b)) else (if i < 523 then decide (2 ≤ count521 b) else decide (1 ≤ count523 b))))) else (if i < 531 then (if i < 527 then (if i < 525 then decide (2 ≤ count523 b) else (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b))) else (if i < 529 then (if i < 528 then decide (3 ≤ count525 b) else decide (4 ≤ count525 b)) else (if i < 530 then decide (1 ≤ count529 b) else decide (2 ≤ count529 b)))) else (if i < 534 then (if i < 532 then decide (3 ≤ count529 b) else (if i < 533 then decide (4 ≤ count529 b) else decide (5 ≤ count529 b))) else (if i < 536 then (if i < 535 then decide (6 ≤ count529 b) else decide (7 ≤ count529 b)) else (if i < 537 then decide (8 ≤ count529 b) else decide (1 ≤ count537 b)))))) else (if i < 552 then (if i < 545 then (if i < 541 then (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (3 ≤ count537 b) else decide (4 ≤ count537 b))) else (if i < 543 then (if i < 542 then decide (5 ≤ count537 b) else decide (6 ≤ count537 b)) else (if i < 544 then decide (7 ≤ count537 b) else decide (8 ≤ count537 b)))) else (if i < 548 then (if i < 546 then decide (9 ≤ count537 b) else (if i < 547 then decide (10 ≤ count537 b) else decide (11 ≤ count537 b))) else (if i < 550 then (if i < 549 then decide (12 ≤ count537 b) else decide (13 ≤ count537 b)) else (if i < 551 then decide (14 ≤ count537 b) else decide (15 ≤ count537 b))))) else (if i < 559 then (if i < 555 then (if i < 553 then decide (1 ≤ count552 b) else (if i < 554 then decide (2 ≤ count552 b) else decide (1 ≤ count554 b))) else (if i < 557 then (if i < 556 then decide (2 ≤ count554 b) else decide (3 ≤ count554 b)) else (if i < 558 then decide (1 ≤ count557 b) else decide (2 ≤ count557 b)))) else (if i < 563 then (if i < 561 then (if i < 560 then decide (1 ≤ count559 b) else decide (2 ≤ count559 b)) else (if i < 562 then decide (1 ≤ count561 b) else decide (2 ≤ count561 b))) else (if i < 565 then (if i < 564 then decide (3 ≤ count561 b) else decide (4 ≤ count561 b)) else (if i < 566 then decide (1 ≤ count565 b) else decide (2 ≤ count565 b)))))))) else (if i < 624 then (if i < 595 then (if i < 581 then (if i < 574 then (if i < 570 then (if i < 568 then decide (3 ≤ count565 b) else (if i < 569 then decide (4 ≤ count565 b) else decide (5 ≤ count565 b))) else (if i < 572 then (if i < 571 then decide (6 ≤ count565 b) else decide (7 ≤ count565 b)) else (if i < 573 then decide (1 ≤ count572 b) else decide (2 ≤ count572 b)))) else (if i < 577 then (if i < 575 then decide (1 ≤ count574 b) else (if i < 576 then decide (2 ≤ count574 b) else decide (1 ≤ count576 b))) else (if i < 579 then (if i < 578 then decide (2 ≤ count576 b) else decide (3 ≤ count576 b)) else (if i < 580 then decide (4 ≤ count576 b) else decide (1 ≤ count580 b))))) else (if i < 588 then (if i < 584 then (if i < 582 then decide (2 ≤ count580 b) else (if i < 583 then decide (1 ≤ count582 b) else decide (2 ≤ count582 b))) else (if i < 586 then (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b)) else (if i < 587 then decide (3 ≤ count584 b) else decide (4 ≤ count584 b)))) else (if i < 591 then (if i < 589 then decide (1 ≤ count588 b) else (if i < 590 then decide (2 ≤ count588 b) else decide (3 ≤ count588 b))) else (if i < 593 then (if i < 592 then decide (4 ≤ count588 b) else decide (5 ≤ count588 b)) else (if i < 594 then decide (6 ≤ count588 b) else decide (7 ≤ count588 b)))))) else (if i < 609 then (if i < 602 then (if i < 598 then (if i < 596 then decide (8 ≤ count588 b) else (if i < 597 then decide (1 ≤ count596 b) else decide (2 ≤ count596 b))) else (if i < 600 then (if i < 599 then decide (3 ≤ count596 b) else decide (4 ≤ count596 b)) else (if i < 601 then decide (5 ≤ count596 b) else decide (6 ≤ count596 b)))) else (if i < 605 then (if i < 603 then decide (7 ≤ count596 b) else (if i < 604 then decide (8 ≤ count596 b) else decide (9 ≤ count596 b))) else (if i < 607 then (if i < 606 then decide (10 ≤ count596 b) else decide (11 ≤ count596 b)) else (if i < 608 then decide (12 ≤ count596 b) else decide (13 ≤ count596 b))))) else (if i < 616 then (if i < 612 then (if i < 610 then decide (14 ≤ count596 b) else (if i < 611 then decide (15 ≤ count596 b) else decide (1 ≤ count611 b))) else (if i < 614 then (if i < 613 then decide (2 ≤ count611 b) else decide (3 ≤ count611 b)) else (if i < 615 then decide (4 ≤ count611 b) else decide (5 ≤ count611 b)))) else (if i < 620 then (if i < 618 then (if i < 617 then decide (6 ≤ count611 b) else decide (7 ≤ count611 b)) else (if i < 619 then decide (8 ≤ count611 b) else decide (9 ≤ count611 b))) else (if i < 622 then (if i < 621 then decide (10 ≤ count611 b) else decide (11 ≤ count611 b)) else (if i < 623 then decide (12 ≤ count611 b) else decide (13 ≤ count611 b))))))) else (if i < 652 then (if i < 638 then (if i < 631 then (if i < 627 then (if i < 625 then decide (14 ≤ count611 b) else (if i < 626 then decide (15 ≤ count611 b) else decide (16 ≤ count611 b))) else (if i < 629 then (if i < 628 then decide (17 ≤ count611 b) else decide (18 ≤ count611 b)) else (if i < 630 then decide (19 ≤ count611 b) else decide (20 ≤ count611 b)))) else (if i < 634 then (if i < 632 then decide (21 ≤ count611 b) else (if i < 633 then decide (22 ≤ count611 b) else decide (23 ≤ count611 b))) else (if i < 636 then (if i < 635 then decide (24 ≤ count611 b) else decide (25 ≤ count611 b)) else (if i < 637 then decide (26 ≤ count611 b) else decide (27 ≤ count611 b))))) else (if i < 645 then (if i < 641 then (if i < 639 then decide (28 ≤ count611 b) else (if i < 640 then decide (29 ≤ count611 b) else decide (30 ≤ count611 b))) else (if i < 643 then (if i < 642 then decide (1 ≤ count641 b) else decide (2 ≤ count641 b)) else (if i < 644 then decide (1 ≤ count643 b) else decide (2 ≤ count643 b)))) else (if i < 648 then (if i < 646 then decide (3 ≤ count643 b) else (if i < 647 then decide (1 ≤ count646 b) else decide (2 ≤ count646 b))) else (if i < 650 then (if i < 649 then decide (1 ≤ count648 b) else decide (2 ≤ count648 b)) else (if i < 651 then decide (1 ≤ count650 b) else decide (2 ≤ count650 b)))))) else (if i < 666 then (if i < 659 then (if i < 655 then (if i < 653 then decide (3 ≤ count650 b) else (if i < 654 then decide (4 ≤ count650 b) else decide (1 ≤ count654 b))) else (if i < 657 then (if i < 656 then decide (2 ≤ count654 b) else decide (3 ≤ count654 b)) else (if i < 658 then decide (4 ≤ count654 b) else decide (5 ≤ count654 b)))) else (if i < 662 then (if i < 660 then decide (6 ≤ count654 b) else (if i < 661 then decide (7 ≤ count654 b) else decide (1 ≤ count661 b))) else (if i < 664 then (if i < 663 then decide (2 ≤ count661 b) else decide (1 ≤ count663 b)) else (if i < 665 then decide (2 ≤ count663 b) else decide (1 ≤ count665 b))))) else (if i < 673 then (if i < 669 then (if i < 667 then decide (2 ≤ count665 b) else (if i < 668 then decide (3 ≤ count665 b) else decide (4 ≤ count665 b))) else (if i < 671 then (if i < 670 then decide (1 ≤ count669 b) else decide (2 ≤ count669 b)) else (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b)))) else (if i < 677 then (if i < 675 then (if i < 674 then decide (1 ≤ count673 b) else decide (2 ≤ count673 b)) else (if i < 676 then decide (3 ≤ count673 b) else decide (4 ≤ count673 b))) else (if i < 679 then (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b)) else (if i < 680 then decide (3 ≤ count677 b) else decide (4 ≤ count677 b))))))))) else (if i < 794 then (if i < 737 then (if i < 709 then (if i < 695 then (if i < 688 then (if i < 684 then (if i < 682 then decide (5 ≤ count677 b) else (if i < 683 then decide (6 ≤ count677 b) else decide (7 ≤ count677 b))) else (if i < 686 then (if i < 685 then decide (8 ≤ count677 b) else decide (1 ≤ count685 b)) else (if i < 687 then decide (2 ≤ count685 b) else decide (3 ≤ count685 b)))) else (if i < 691 then (if i < 689 then decide (4 ≤ count685 b) else (if i < 690 then decide (5 ≤ count685 b) else decide (6 ≤ count685 b))) else (if i < 693 then (if i < 692 then decide (7 ≤ count685 b) else decide (8 ≤ count685 b)) else (if i < 694 then decide (9 ≤ count685 b) else decide (10 ≤ count685 b))))) else (if i < 702 then (if i < 698 then (if i < 696 then decide (11 ≤ count685 b) else (if i < 697 then decide (12 ≤ count685 b) else decide (13 ≤ count685 b))) else (if i < 700 then (if i < 699 then decide (14 ≤ count685 b) else decide (15 ≤ count685 b)) else (if i < 701 then decide (1 ≤ count700 b) else decide (2 ≤ count700 b)))) else (if i < 705 then (if i < 703 then decide (1 ≤ count702 b) else (if i < 704 then decide (2 ≤ count702 b) else decide (1 ≤ count704 b))) else (if i < 707 then (if i < 706 then decide (2 ≤ count704 b) else decide (3 ≤ count704 b)) else (if i < 708 then decide (4 ≤ count704 b) else decide (1 ≤ count708 b)))))) else (if i < 723 then (if i < 716 then (if i < 712 then (if i < 710 then decide (2 ≤ count708 b) else (if i < 711 then decide (1 ≤ count710 b) else decide (2 ≤ count710 b))) else (if i < 714 then (if i < 713 then decide (1 ≤ count712 b) else decide (2 ≤ count712 b)) else (if i < 715 then decide (3 ≤ count712 b) else decide (4 ≤ count712 b)))) else (if i < 719 then (if i < 717 then decide (1 ≤ count716 b) else (if i < 718 then decide (2 ≤ count716 b) else decide (3 ≤ count716 b))) else (if i < 721 then (if i < 720 then decide (4 ≤ count716 b) else decide (5 ≤ count716 b)) else (if i < 722 then decide (6 ≤ count716 b) else decide (7 ≤ count716 b))))) else (if i < 730 then (if i < 726 then (if i < 724 then decide (8 ≤ count716 b) else (if i < 725 then decide (1 ≤ count724 b) else decide (2 ≤ count724 b))) else (if i < 728 then (if i < 727 then decide (1 ≤ count726 b) else decide (2 ≤ count726 b)) else (if i < 729 then decide (1 ≤ count728 b) else decide (2 ≤ count728 b)))) else (if i < 733 then (if i < 731 then decide (3 ≤ count728 b) else (if i < 732 then decide (4 ≤ count728 b) else decide (1 ≤ count732 b))) else (if i < 735 then (if i < 734 then decide (2 ≤ count732 b) else decide (1 ≤ count734 b)) else (if i < 736 then decide (2 ≤ count734 b) else decide (1 ≤ count736 b))))))) else (if i < 765 then (if i < 751 then (if i < 744 then (if i < 740 then (if i < 738 then decide (2 ≤ count736 b) else (if i < 739 then decide (3 ≤ count736 b) else decide (4 ≤ count736 b))) else (if i < 742 then (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b)) else (if i < 743 then decide (3 ≤ count740 b) else decide (4 ≤ count740 b)))) else (if i < 747 then (if i < 745 then decide (5 ≤ count740 b) else (if i < 746 then decide (6 ≤ count740 b) else decide (7 ≤ count740 b))) else (if i < 749 then (if i < 748 then decide (8 ≤ count740 b) else decide (1 ≤ count748 b)) else (if i < 750 then decide (2 ≤ count748 b) else decide (3 ≤ count748 b))))) else (if i < 758 then (if i < 754 then (if i < 752 then decide (4 ≤ count748 b) else (if i < 753 then decide (5 ≤ count748 b) else decide (6 ≤ count748 b))) else (if i < 756 then (if i < 755 then decide (7 ≤ count748 b) else decide (8 ≤ count748 b)) else (if i < 757 then decide (9 ≤ count748 b) else decide (10 ≤ count748 b)))) else (if i < 761 then (if i < 759 then decide (11 ≤ count748 b) else (if i < 760 then decide (12 ≤ count748 b) else decide (13 ≤ count748 b))) else (if i < 763 then (if i < 762 then decide (14 ≤ count748 b) else decide (15 ≤ count748 b)) else (if i < 764 then decide (16 ≤ count748 b) else decide (1 ≤ count764 b)))))) else (if i < 779 then (if i < 772 then (if i < 768 then (if i < 766 then decide (2 ≤ count764 b) else (if i < 767 then decide (3 ≤ count764 b) else decide (4 ≤ count764 b))) else (if i < 770 then (if i < 769 then decide (5 ≤ count764 b) else decide (6 ≤ count764 b)) else (if i < 771 then decide (7 ≤ count764 b) else decide (8 ≤ count764 b)))) else (if i < 775 then (if i < 773 then decide (9 ≤ count764 b) else (if i < 774 then decide (10 ≤ count764 b) else decide (11 ≤ count764 b))) else (if i < 777 then (if i < 776 then decide (12 ≤ count764 b) else decide (13 ≤ count764 b)) else (if i < 778 then decide (14 ≤ count764 b) else decide (15 ≤ count764 b))))) else (if i < 786 then (if i < 782 then (if i < 780 then decide (16 ≤ count764 b) else (if i < 781 then decide (17 ≤ count764 b) else decide (18 ≤ count764 b))) else (if i < 784 then (if i < 783 then decide (19 ≤ count764 b) else decide (20 ≤ count764 b)) else (if i < 785 then decide (21 ≤ count764 b) else decide (22 ≤ count764 b)))) else (if i < 790 then (if i < 788 then (if i < 787 then decide (23 ≤ count764 b) else decide (24 ≤ count764 b)) else (if i < 789 then decide (25 ≤ count764 b) else decide (26 ≤ count764 b))) else (if i < 792 then (if i < 791 then decide (27 ≤ count764 b) else decide (28 ≤ count764 b)) else (if i < 793 then decide (29 ≤ count764 b) else decide (30 ≤ count764 b)))))))) else (if i < 851 then (if i < 822 then (if i < 808 then (if i < 801 then (if i < 797 then (if i < 795 then decide (31 ≤ count764 b) else (if i < 796 then decide (1 ≤ count795 b) else decide (2 ≤ count795 b))) else (if i < 799 then (if i < 798 then decide (3 ≤ count795 b) else decide (4 ≤ count795 b)) else (if i < 800 then decide (5 ≤ count795 b) else decide (6 ≤ count795 b)))) else (if i < 804 then (if i < 802 then decide (7 ≤ count795 b) else (if i < 803 then decide (8 ≤ count795 b) else decide (9 ≤ count795 b))) else (if i < 806 then (if i < 805 then decide (10 ≤ count795 b) else decide (11 ≤ count795 b)) else (if i < 807 then decide (12 ≤ count795 b) else decide (13 ≤ count795 b))))) else (if i < 815 then (if i < 811 then (if i < 809 then decide (14 ≤ count795 b) else (if i < 810 then decide (15 ≤ count795 b) else decide (16 ≤ count795 b))) else (if i < 813 then (if i < 812 then decide (17 ≤ count795 b) else decide (18 ≤ count795 b)) else (if i < 814 then decide (19 ≤ count795 b) else decide (20 ≤ count795 b)))) else (if i < 818 then (if i < 816 then decide (21 ≤ count795 b) else (if i < 817 then decide (22 ≤ count795 b) else decide (23 ≤ count795 b))) else (if i < 820 then (if i < 819 then decide (24 ≤ count795 b) else decide (25 ≤ count795 b)) else (if i < 821 then decide (26 ≤ count795 b) else decide (27 ≤ count795 b)))))) else (if i < 836 then (if i < 829 then (if i < 825 then (if i < 823 then decide (28 ≤ count795 b) else (if i < 824 then decide (29 ≤ count795 b) else decide (30 ≤ count795 b))) else (if i < 827 then (if i < 826 then decide (31 ≤ count795 b) else decide (32 ≤ count795 b)) else (if i < 828 then decide (33 ≤ count795 b) else decide (34 ≤ count795 b)))) else (if i < 832 then (if i < 830 then decide (35 ≤ count795 b) else (if i < 831 then decide (36 ≤ count795 b) else decide (37 ≤ count795 b))) else (if i < 834 then (if i < 833 then decide (38 ≤ count795 b) else decide (39 ≤ count795 b)) else (if i < 835 then decide (40 ≤ count795 b) else decide (41 ≤ count795 b))))) else (if i < 843 then (if i < 839 then (if i < 837 then decide (42 ≤ count795 b) else (if i < 838 then decide (1 ≤ count837 b) else decide (2 ≤ count837 b))) else (if i < 841 then (if i < 840 then decide (1 ≤ count839 b) else decide (2 ≤ count839 b)) else (if i < 842 then decide (3 ≤ count839 b) else decide (1 ≤ count842 b)))) else (if i < 847 then (if i < 845 then (if i < 844 then decide (2 ≤ count842 b) else decide (1 ≤ count844 b)) else (if i < 846 then decide (2 ≤ count844 b) else decide (1 ≤ count846 b))) else (if i < 849 then (if i < 848 then decide (2 ≤ count846 b) else decide (3 ≤ count846 b)) else (if i < 850 then decide (4 ≤ count846 b) else decide (1 ≤ count850 b))))))) else (if i < 879 then (if i < 865 then (if i < 858 then (if i < 854 then (if i < 852 then decide (2 ≤ count850 b) else (if i < 853 then decide (3 ≤ count850 b) else decide (4 ≤ count850 b))) else (if i < 856 then (if i < 855 then decide (5 ≤ count850 b) else decide (6 ≤ count850 b)) else (if i < 857 then decide (7 ≤ count850 b) else decide (1 ≤ count857 b)))) else (if i < 861 then (if i < 859 then decide (2 ≤ count857 b) else (if i < 860 then decide (1 ≤ count859 b) else decide (2 ≤ count859 b))) else (if i < 863 then (if i < 862 then decide (1 ≤ count861 b) else decide (2 ≤ count861 b)) else (if i < 864 then decide (3 ≤ count861 b) else decide (4 ≤ count861 b))))) else (if i < 872 then (if i < 868 then (if i < 866 then decide (1 ≤ count865 b) else (if i < 867 then decide (2 ≤ count865 b) else decide (1 ≤ count867 b))) else (if i < 870 then (if i < 869 then decide (2 ≤ count867 b) else decide (1 ≤ count869 b)) else (if i < 871 then decide (2 ≤ count869 b) else decide (3 ≤ count869 b)))) else (if i < 875 then (if i < 873 then decide (4 ≤ count869 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b))) else (if i < 877 then (if i < 876 then decide (3 ≤ count873 b) else decide (4 ≤ count873 b)) else (if i < 878 then decide (5 ≤ count873 b) else decide (6 ≤ count873 b)))))) else (if i < 893 then (if i < 886 then (if i < 882 then (if i < 880 then decide (7 ≤ count873 b) else (if i < 881 then decide (8 ≤ count873 b) else decide (1 ≤ count881 b))) else (if i < 884 then (if i < 883 then decide (2 ≤ count881 b) else decide (3 ≤ count881 b)) else (if i < 885 then decide (4 ≤ count881 b) else decide (5 ≤ count881 b)))) else (if i < 889 then (if i < 887 then decide (6 ≤ count881 b) else (if i < 888 then decide (7 ≤ count881 b) else decide (8 ≤ count881 b))) else (if i < 891 then (if i < 890 then decide (9 ≤ count881 b) else decide (10 ≤ count881 b)) else (if i < 892 then decide (11 ≤ count881 b) else decide (12 ≤ count881 b))))) else (if i < 900 then (if i < 896 then (if i < 894 then decide (13 ≤ count881 b) else (if i < 895 then decide (14 ≤ count881 b) else decide (15 ≤ count881 b))) else (if i < 898 then (if i < 897 then decide (1 ≤ count896 b) else decide (2 ≤ count896 b)) else (if i < 899 then decide (1 ≤ count898 b) else decide (2 ≤ count898 b)))) else (if i < 904 then (if i < 902 then (if i < 901 then decide (3 ≤ count898 b) else decide (1 ≤ count901 b)) else (if i < 903 then decide (2 ≤ count901 b) else decide (1 ≤ count903 b))) else (if i < 906 then (if i < 905 then decide (2 ≤ count903 b) else decide (1 ≤ count905 b)) else (if i < 907 then decide (2 ≤ count905 b) else decide (3 ≤ count905 b))))))))))) else (if i < 1362 then (if i < 1135 then (if i < 1021 then (if i < 964 then (if i < 936 then (if i < 922 then (if i < 915 then (if i < 911 then (if i < 909 then decide (4 ≤ count905 b) else (if i < 910 then decide (1 ≤ count909 b) else decide (2 ≤ count909 b))) else (if i < 913 then (if i < 912 then decide (3 ≤ count909 b) else decide (4 ≤ count909 b)) else (if i < 914 then decide (5 ≤ count909 b) else decide (6 ≤ count909 b)))) else (if i < 918 then (if i < 916 then decide (7 ≤ count909 b) else (if i < 917 then decide (1 ≤ count916 b) else decide (2 ≤ count916 b))) else (if i < 920 then (if i < 919 then decide (1 ≤ count918 b) else decide (2 ≤ count918 b)) else (if i < 921 then decide (1 ≤ count920 b) else decide (2 ≤ count920 b))))) else (if i < 929 then (if i < 925 then (if i < 923 then decide (3 ≤ count920 b) else (if i < 924 then decide (4 ≤ count920 b) else decide (1 ≤ count924 b))) else (if i < 927 then (if i < 926 then decide (2 ≤ count924 b) else decide (1 ≤ count926 b)) else (if i < 928 then decide (2 ≤ count926 b) else decide (1 ≤ count928 b)))) else (if i < 932 then (if i < 930 then decide (2 ≤ count928 b) else (if i < 931 then decide (3 ≤ count928 b) else decide (4 ≤ count928 b))) else (if i < 934 then (if i < 933 then decide (1 ≤ count932 b) else decide (2 ≤ count932 b)) else (if i < 935 then decide (3 ≤ count932 b) else decide (4 ≤ count932 b)))))) else (if i < 950 then (if i < 943 then (if i < 939 then (if i < 937 then decide (5 ≤ count932 b) else (if i < 938 then decide (6 ≤ count932 b) else decide (7 ≤ count932 b))) else (if i < 941 then (if i < 940 then decide (8 ≤ count932 b) else decide (1 ≤ count940 b)) else (if i < 942 then decide (2 ≤ count940 b) else decide (3 ≤ count940 b)))) else (if i < 946 then (if i < 944 then decide (4 ≤ count940 b) else (if i < 945 then decide (5 ≤ count940 b) else decide (6 ≤ count940 b))) else (if i < 948 then (if i < 947 then decide (7 ≤ count940 b) else decide (8 ≤ count940 b)) else (if i < 949 then decide (9 ≤ count940 b) else decide (10 ≤ count940 b))))) else (if i < 957 then (if i < 953 then (if i < 951 then decide (11 ≤ count940 b) else (if i < 952 then decide (12 ≤ count940 b) else decide (13 ≤ count940 b))) else (if i < 955 then (if i < 954 then decide (14 ≤ count940 b) else decide (15 ≤ count940 b)) else (if i < 956 then decide (1 ≤ count955 b) else decide (2 ≤ count955 b)))) else (if i < 960 then (if i < 958 then decide (3 ≤ count955 b) else (if i < 959 then decide (4 ≤ count955 b) else decide (5 ≤ count955 b))) else (if i < 962 then (if i < 961 then decide (6 ≤ count955 b) else decide (7 ≤ count955 b)) else (if i < 963 then decide (8 ≤ count955 b) else decide (9 ≤ count955 b))))))) else (if i < 992 then (if i < 978 then (if i < 971 then (if i < 967 then (if i < 965 then decide (10 ≤ count955 b) else (if i < 966 then decide (11 ≤ count955 b) else decide (12 ≤ count955 b))) else (if i < 969 then (if i < 968 then decide (13 ≤ count955 b) else decide (14 ≤ count955 b)) else (if i < 970 then decide (15 ≤ count955 b) else decide (16 ≤ count955 b)))) else (if i < 974 then (if i < 972 then decide (17 ≤ count955 b) else (if i < 973 then decide (18 ≤ count955 b) else decide (19 ≤ count955 b))) else (if i < 976 then (if i < 975 then decide (20 ≤ count955 b) else decide (21 ≤ count955 b)) else (if i < 977 then decide (1 ≤ count976 b) else decide (2 ≤ count976 b))))) else (if i < 985 then (if i < 981 then (if i < 979 then decide (1 ≤ count978 b) else (if i < 980 then decide (2 ≤ count978 b) else decide (3 ≤ count978 b))) else (if i < 983 then (if i < 982 then decide (1 ≤ count981 b) else decide (2 ≤ count981 b)) else (if i < 984 then decide (1 ≤ count983 b) else decide (2 ≤ count983 b)))) else (if i < 988 then (if i < 986 then decide (1 ≤ count985 b) else (if i < 987 then decide (2 ≤ count985 b) else decide (3 ≤ count985 b))) else (if i < 990 then (if i < 989 then decide (4 ≤ count985 b) else decide (1 ≤ count989 b)) else (if i < 991 then decide (2 ≤ count989 b) else decide (3 ≤ count989 b)))))) else (if i < 1006 then (if i < 999 then (if i < 995 then (if i < 993 then decide (4 ≤ count989 b) else (if i < 994 then decide (5 ≤ count989 b) else decide (6 ≤ count989 b))) else (if i < 997 then (if i < 996 then decide (7 ≤ count989 b) else decide (1 ≤ count996 b)) else (if i < 998 then decide (2 ≤ count996 b) else decide (1 ≤ count998 b)))) else (if i < 1002 then (if i < 1000 then decide (2 ≤ count998 b) else (if i < 1001 then decide (1 ≤ count1000 b) else decide (2 ≤ count1000 b))) else (if i < 1004 then (if i < 1003 then decide (3 ≤ count1000 b) else decide (4 ≤ count1000 b)) else (if i < 1005 then decide (1 ≤ count1004 b) else decide (2 ≤ count1004 b))))) else (if i < 1013 then (if i < 1009 then (if i < 1007 then decide (1 ≤ count1006 b) else (if i < 1008 then decide (2 ≤ count1006 b) else decide (1 ≤ count1008 b))) else (if i < 1011 then (if i < 1010 then decide (2 ≤ count1008 b) else decide (3 ≤ count1008 b)) else (if i < 1012 then decide (4 ≤ count1008 b) else decide (1 ≤ count1012 b)))) else (if i < 1017 then (if i < 1015 then (if i < 1014 then decide (2 ≤ count1012 b) else decide (3 ≤ count1012 b)) else (if i < 1016 then decide (4 ≤ count1012 b) else decide (5 ≤ count1012 b))) else (if i < 1019 then (if i < 1018 then decide (6 ≤ count1012 b) else decide (7 ≤ count1012 b)) else (if i < 1020 then decide (8 ≤ count1012 b) else decide (1 ≤ count1020 b)))))))) else (if i < 1078 then (if i < 1049 then (if i < 1035 then (if i < 1028 then (if i < 1024 then (if i < 1022 then decide (2 ≤ count1020 b) else (if i < 1023 then decide (3 ≤ count1020 b) else decide (4 ≤ count1020 b))) else (if i < 1026 then (if i < 1025 then decide (5 ≤ count1020 b) else decide (6 ≤ count1020 b)) else (if i < 1027 then decide (7 ≤ count1020 b) else decide (8 ≤ count1020 b)))) else (if i < 1031 then (if i < 1029 then decide (9 ≤ count1020 b) else (if i < 1030 then decide (10 ≤ count1020 b) else decide (11 ≤ count1020 b))) else (if i < 1033 then (if i < 1032 then decide (12 ≤ count1020 b) else decide (13 ≤ count1020 b)) else (if i < 1034 then decide (14 ≤ count1020 b) else decide (15 ≤ count1020 b))))) else (if i < 1042 then (if i < 1038 then (if i < 1036 then decide (1 ≤ count1035 b) else (if i < 1037 then decide (2 ≤ count1035 b) else decide (1 ≤ count1037 b))) else (if i < 1040 then (if i < 1039 then decide (2 ≤ count1037 b) else decide (1 ≤ count1039 b)) else (if i < 1041 then decide (2 ≤ count1039 b) else decide (3 ≤ count1039 b)))) else (if i < 1045 then (if i < 1043 then decide (4 ≤ count1039 b) else (if i < 1044 then decide (1 ≤ count1043 b) else decide (2 ≤ count1043 b))) else (if i < 1047 then (if i < 1046 then decide (1 ≤ count1045 b) else decide (2 ≤ count1045 b)) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b)))))) else (if i < 1063 then (if i < 1056 then (if i < 1052 then (if i < 1050 then decide (3 ≤ count1047 b) else (if i < 1051 then decide (4 ≤ count1047 b) else decide (1 ≤ count1051 b))) else (if i < 1054 then (if i < 1053 then decide (2 ≤ count1051 b) else decide (3 ≤ count1051 b)) else (if i < 1055 then decide (4 ≤ count1051 b) else decide (5 ≤ count1051 b)))) else (if i < 1059 then (if i < 1057 then decide (6 ≤ count1051 b) else (if i < 1058 then decide (7 ≤ count1051 b) else decide (8 ≤ count1051 b))) else (if i < 1061 then (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b)) else (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b))))) else (if i < 1070 then (if i < 1066 then (if i < 1064 then decide (1 ≤ count1063 b) else (if i < 1065 then decide (2 ≤ count1063 b) else decide (3 ≤ count1063 b))) else (if i < 1068 then (if i < 1067 then decide (4 ≤ count1063 b) else decide (1 ≤ count1067 b)) else (if i < 1069 then decide (2 ≤ count1067 b) else decide (1 ≤ count1069 b)))) else (if i < 1074 then (if i < 1072 then (if i < 1071 then decide (2 ≤ count1069 b) else decide (1 ≤ count1071 b)) else (if i < 1073 then decide (2 ≤ count1071 b) else decide (3 ≤ count1071 b))) else (if i < 1076 then (if i < 1075 then decide (4 ≤ count1071 b) else decide (1 ≤ count1075 b)) else (if i < 1077 then decide (2 ≤ count1075 b) else decide (3 ≤ count1075 b))))))) else (if i < 1106 then (if i < 1092 then (if i < 1085 then (if i < 1081 then (if i < 1079 then decide (4 ≤ count1075 b) else (if i < 1080 then decide (5 ≤ count1075 b) else decide (6 ≤ count1075 b))) else (if i < 1083 then (if i < 1082 then decide (7 ≤ count1075 b) else decide (8 ≤ count1075 b)) else (if i < 1084 then decide (1 ≤ count1083 b) else decide (2 ≤ count1083 b)))) else (if i < 1088 then (if i < 1086 then decide (3 ≤ count1083 b) else (if i < 1087 then decide (4 ≤ count1083 b) else decide (5 ≤ count1083 b))) else (if i < 1090 then (if i < 1089 then decide (6 ≤ count1083 b) else decide (7 ≤ count1083 b)) else (if i < 1091 then decide (8 ≤ count1083 b) else decide (9 ≤ count1083 b))))) else (if i < 1099 then (if i < 1095 then (if i < 1093 then decide (10 ≤ count1083 b) else (if i < 1094 then decide (11 ≤ count1083 b) else decide (12 ≤ count1083 b))) else (if i < 1097 then (if i < 1096 then decide (13 ≤ count1083 b) else decide (14 ≤ count1083 b)) else (if i < 1098 then decide (15 ≤ count1083 b) else decide (16 ≤ count1083 b)))) else (if i < 1102 then (if i < 1100 then decide (1 ≤ count1099 b) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (3 ≤ count1099 b))) else (if i < 1104 then (if i < 1103 then decide (4 ≤ count1099 b) else decide (5 ≤ count1099 b)) else (if i < 1105 then decide (6 ≤ count1099 b) else decide (7 ≤ count1099 b)))))) else (if i < 1120 then (if i < 1113 then (if i < 1109 then (if i < 1107 then decide (8 ≤ count1099 b) else (if i < 1108 then decide (9 ≤ count1099 b) else decide (10 ≤ count1099 b))) else (if i < 1111 then (if i < 1110 then decide (11 ≤ count1099 b) else decide (12 ≤ count1099 b)) else (if i < 1112 then decide (13 ≤ count1099 b) else decide (14 ≤ count1099 b)))) else (if i < 1116 then (if i < 1114 then decide (15 ≤ count1099 b) else (if i < 1115 then decide (16 ≤ count1099 b) else decide (17 ≤ count1099 b))) else (if i < 1118 then (if i < 1117 then decide (18 ≤ count1099 b) else decide (19 ≤ count1099 b)) else (if i < 1119 then decide (20 ≤ count1099 b) else decide (21 ≤ count1099 b))))) else (if i < 1127 then (if i < 1123 then (if i < 1121 then decide (1 ≤ count1120 b) else (if i < 1122 then decide (2 ≤ count1120 b) else decide (3 ≤ count1120 b))) else (if i < 1125 then (if i < 1124 then decide (4 ≤ count1120 b) else decide (5 ≤ count1120 b)) else (if i < 1126 then decide (6 ≤ count1120 b) else decide (7 ≤ count1120 b)))) else (if i < 1131 then (if i < 1129 then (if i < 1128 then decide (8 ≤ count1120 b) else decide (9 ≤ count1120 b)) else (if i < 1130 then decide (10 ≤ count1120 b) else decide (11 ≤ count1120 b))) else (if i < 1133 then (if i < 1132 then decide (12 ≤ count1120 b) else decide (13 ≤ count1120 b)) else (if i < 1134 then decide (14 ≤ count1120 b) else decide (15 ≤ count1120 b))))))))) else (if i < 1248 then (if i < 1191 then (if i < 1163 then (if i < 1149 then (if i < 1142 then (if i < 1138 then (if i < 1136 then decide (16 ≤ count1120 b) else (if i < 1137 then decide (17 ≤ count1120 b) else decide (18 ≤ count1120 b))) else (if i < 1140 then (if i < 1139 then decide (19 ≤ count1120 b) else decide (20 ≤ count1120 b)) else (if i < 1141 then decide (21 ≤ count1120 b) else decide (1 ≤ count1141 b)))) else (if i < 1145 then (if i < 1143 then decide (2 ≤ count1141 b) else (if i < 1144 then decide (1 ≤ count1143 b) else decide (2 ≤ count1143 b))) else (if i < 1147 then (if i < 1146 then decide (3 ≤ count1143 b) else decide (1 ≤ count1146 b)) else (if i < 1148 then decide (2 ≤ count1146 b) else decide (1 ≤ count1148 b))))) else (if i < 1156 then (if i < 1152 then (if i < 1150 then decide (2 ≤ count1148 b) else (if i < 1151 then decide (1 ≤ count1150 b) else decide (2 ≤ count1150 b))) else (if i < 1154 then (if i < 1153 then decide (3 ≤ count1150 b) else decide (4 ≤ count1150 b)) else (if i < 1155 then decide (1 ≤ count1154 b) else decide (2 ≤ count1154 b)))) else (if i < 1159 then (if i < 1157 then decide (3 ≤ count1154 b) else (if i < 1158 then decide (4 ≤ count1154 b) else decide (5 ≤ count1154 b))) else (if i < 1161 then (if i < 1160 then decide (6 ≤ count1154 b) else decide (7 ≤ count1154 b)) else (if i < 1162 then decide (1 ≤ count1161 b) else decide (2 ≤ count1161 b)))))) else (if i < 1177 then (if i < 1170 then (if i < 1166 then (if i < 1164 then decide (1 ≤ count1163 b) else (if i < 1165 then decide (2 ≤ count1163 b) else decide (1 ≤ count1165 b))) else (if i < 1168 then (if i < 1167 then decide (2 ≤ count1165 b) else decide (3 ≤ count1165 b)) else (if i < 1169 then decide (4 ≤ count1165 b) else decide (1 ≤ count1169 b)))) else (if i < 1173 then (if i < 1171 then decide (2 ≤ count1169 b) else (if i < 1172 then decide (1 ≤ count1171 b) else decide (2 ≤ count1171 b))) else (if i < 1175 then (if i < 1174 then decide (1 ≤ count1173 b) else decide (2 ≤ count1173 b)) else (if i < 1176 then decide (3 ≤ count1173 b) else decide (4 ≤ count1173 b))))) else (if i < 1184 then (if i < 1180 then (if i < 1178 then decide (1 ≤ count1177 b) else (if i < 1179 then decide (2 ≤ count1177 b) else decide (3 ≤ count1177 b))) else (if i < 1182 then (if i < 1181 then decide (4 ≤ count1177 b) else decide (5 ≤ count1177 b)) else (if i < 1183 then decide (6 ≤ count1177 b) else decide (7 ≤ count1177 b)))) else (if i < 1187 then (if i < 1185 then decide (8 ≤ count1177 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))) else (if i < 1189 then (if i < 1188 then decide (3 ≤ count1185 b) else decide (4 ≤ count1185 b)) else (if i < 1190 then decide (5 ≤ count1185 b) else decide (6 ≤ count1185 b))))))) else (if i < 1219 then (if i < 1205 then (if i < 1198 then (if i < 1194 then (if i < 1192 then decide (7 ≤ count1185 b) else (if i < 1193 then decide (8 ≤ count1185 b) else decide (9 ≤ count1185 b))) else (if i < 1196 then (if i < 1195 then decide (10 ≤ count1185 b) else decide (11 ≤ count1185 b)) else (if i < 1197 then decide (12 ≤ count1185 b) else decide (13 ≤ count1185 b)))) else (if i < 1201 then (if i < 1199 then decide (14 ≤ count1185 b) else (if i < 1200 then decide (15 ≤ count1185 b) else decide (1 ≤ count1200 b))) else (if i < 1203 then (if i < 1202 then decide (2 ≤ count1200 b) else decide (1 ≤ count1202 b)) else (if i < 1204 then decide (2 ≤ count1202 b) else decide (1 ≤ count1204 b))))) else (if i < 1212 then (if i < 1208 then (if i < 1206 then decide (2 ≤ count1204 b) else (if i < 1207 then decide (3 ≤ count1204 b) else decide (4 ≤ count1204 b))) else (if i < 1210 then (if i < 1209 then decide (1 ≤ count1208 b) else decide (2 ≤ count1208 b)) else (if i < 1211 then decide (1 ≤ count1210 b) else decide (2 ≤ count1210 b)))) else (if i < 1215 then (if i < 1213 then decide (1 ≤ count1212 b) else (if i < 1214 then decide (2 ≤ count1212 b) else decide (3 ≤ count1212 b))) else (if i < 1217 then (if i < 1216 then decide (4 ≤ count1212 b) else decide (1 ≤ count1216 b)) else (if i < 1218 then decide (2 ≤ count1216 b) else decide (3 ≤ count1216 b)))))) else (if i < 1233 then (if i < 1226 then (if i < 1222 then (if i < 1220 then decide (4 ≤ count1216 b) else (if i < 1221 then decide (5 ≤ count1216 b) else decide (6 ≤ count1216 b))) else (if i < 1224 then (if i < 1223 then decide (7 ≤ count1216 b) else decide (8 ≤ count1216 b)) else (if i < 1225 then decide (1 ≤ count1224 b) else decide (2 ≤ count1224 b)))) else (if i < 1229 then (if i < 1227 then decide (1 ≤ count1226 b) else (if i < 1228 then decide (2 ≤ count1226 b) else decide (1 ≤ count1228 b))) else (if i < 1231 then (if i < 1230 then decide (2 ≤ count1228 b) else decide (3 ≤ count1228 b)) else (if i < 1232 then decide (4 ≤ count1228 b) else decide (1 ≤ count1232 b))))) else (if i < 1240 then (if i < 1236 then (if i < 1234 then decide (2 ≤ count1232 b) else (if i < 1235 then decide (1 ≤ count1234 b) else decide (2 ≤ count1234 b))) else (if i < 1238 then (if i < 1237 then decide (1 ≤ count1236 b) else decide (2 ≤ count1236 b)) else (if i < 1239 then decide (3 ≤ count1236 b) else decide (4 ≤ count1236 b)))) else (if i < 1244 then (if i < 1242 then (if i < 1241 then decide (1 ≤ count1240 b) else decide (2 ≤ count1240 b)) else (if i < 1243 then decide (3 ≤ count1240 b) else decide (4 ≤ count1240 b))) else (if i < 1246 then (if i < 1245 then decide (5 ≤ count1240 b) else decide (6 ≤ count1240 b)) else (if i < 1247 then decide (7 ≤ count1240 b) else decide (8 ≤ count1240 b)))))))) else (if i < 1305 then (if i < 1276 then (if i < 1262 then (if i < 1255 then (if i < 1251 then (if i < 1249 then decide (1 ≤ count1248 b) else (if i < 1250 then decide (2 ≤ count1248 b) else decide (3 ≤ count1248 b))) else (if i < 1253 then (if i < 1252 then decide (4 ≤ count1248 b) else decide (5 ≤ count1248 b)) else (if i < 1254 then decide (6 ≤ count1248 b) else decide (7 ≤ count1248 b)))) else (if i < 1258 then (if i < 1256 then decide (8 ≤ count1248 b) else (if i < 1257 then decide (9 ≤ count1248 b) else decide (10 ≤ count1248 b))) else (if i < 1260 then (if i < 1259 then decide (11 ≤ count1248 b) else decide (12 ≤ count1248 b)) else (if i < 1261 then decide (13 ≤ count1248 b) else decide (14 ≤ count1248 b))))) else (if i < 1269 then (if i < 1265 then (if i < 1263 then decide (15 ≤ count1248 b) else (if i < 1264 then decide (16 ≤ count1248 b) else decide (1 ≤ count1264 b))) else (if i < 1267 then (if i < 1266 then decide (2 ≤ count1264 b) else decide (3 ≤ count1264 b)) else (if i < 1268 then decide (4 ≤ count1264 b) else decide (5 ≤ count1264 b)))) else (if i < 1272 then (if i < 1270 then decide (6 ≤ count1264 b) else (if i < 1271 then decide (7 ≤ count1264 b) else decide (8 ≤ count1264 b))) else (if i < 1274 then (if i < 1273 then decide (9 ≤ count1264 b) else decide (10 ≤ count1264 b)) else (if i < 1275 then decide (11 ≤ count1264 b) else decide (12 ≤ count1264 b)))))) else (if i < 1290 then (if i < 1283 then (if i < 1279 then (if i < 1277 then decide (13 ≤ count1264 b) else (if i < 1278 then decide (14 ≤ count1264 b) else decide (15 ≤ count1264 b))) else (if i < 1281 then (if i < 1280 then decide (16 ≤ count1264 b) else decide (17 ≤ count1264 b)) else (if i < 1282 then decide (18 ≤ count1264 b) else decide (19 ≤ count1264 b)))) else (if i < 1286 then (if i < 1284 then decide (20 ≤ count1264 b) else (if i < 1285 then decide (21 ≤ count1264 b) else decide (22 ≤ count1264 b))) else (if i < 1288 then (if i < 1287 then decide (23 ≤ count1264 b) else decide (24 ≤ count1264 b)) else (if i < 1289 then decide (25 ≤ count1264 b) else decide (26 ≤ count1264 b))))) else (if i < 1297 then (if i < 1293 then (if i < 1291 then decide (27 ≤ count1264 b) else (if i < 1292 then decide (28 ≤ count1264 b) else decide (29 ≤ count1264 b))) else (if i < 1295 then (if i < 1294 then decide (30 ≤ count1264 b) else decide (31 ≤ count1264 b)) else (if i < 1296 then decide (1 ≤ count1295 b) else decide (2 ≤ count1295 b)))) else (if i < 1301 then (if i < 1299 then (if i < 1298 then decide (1 ≤ count1297 b) else decide (2 ≤ count1297 b)) else (if i < 1300 then decide (1 ≤ count1299 b) else decide (2 ≤ count1299 b))) else (if i < 1303 then (if i < 1302 then decide (3 ≤ count1299 b) else decide (4 ≤ count1299 b)) else (if i < 1304 then decide (1 ≤ count1303 b) else decide (2 ≤ count1303 b))))))) else (if i < 1333 then (if i < 1319 then (if i < 1312 then (if i < 1308 then (if i < 1306 then decide (1 ≤ count1305 b) else (if i < 1307 then decide (2 ≤ count1305 b) else decide (1 ≤ count1307 b))) else (if i < 1310 then (if i < 1309 then decide (2 ≤ count1307 b) else decide (3 ≤ count1307 b)) else (if i < 1311 then decide (4 ≤ count1307 b) else decide (1 ≤ count1311 b)))) else (if i < 1315 then (if i < 1313 then decide (2 ≤ count1311 b) else (if i < 1314 then decide (3 ≤ count1311 b) else decide (4 ≤ count1311 b))) else (if i < 1317 then (if i < 1316 then decide (5 ≤ count1311 b) else decide (6 ≤ count1311 b)) else (if i < 1318 then decide (7 ≤ count1311 b) else decide (8 ≤ count1311 b))))) else (if i < 1326 then (if i < 1322 then (if i < 1320 then decide (1 ≤ count1319 b) else (if i < 1321 then decide (2 ≤ count1319 b) else decide (1 ≤ count1321 b))) else (if i < 1324 then (if i < 1323 then decide (2 ≤ count1321 b) else decide (1 ≤ count1323 b)) else (if i < 1325 then decide (2 ≤ count1323 b) else decide (3 ≤ count1323 b)))) else (if i < 1329 then (if i < 1327 then decide (4 ≤ count1323 b) else (if i < 1328 then decide (1 ≤ count1327 b) else decide (2 ≤ count1327 b))) else (if i < 1331 then (if i < 1330 then decide (1 ≤ count1329 b) else decide (2 ≤ count1329 b)) else (if i < 1332 then decide (1 ≤ count1331 b) else decide (2 ≤ count1331 b)))))) else (if i < 1347 then (if i < 1340 then (if i < 1336 then (if i < 1334 then decide (3 ≤ count1331 b) else (if i < 1335 then decide (4 ≤ count1331 b) else decide (1 ≤ count1335 b))) else (if i < 1338 then (if i < 1337 then decide (2 ≤ count1335 b) else decide (3 ≤ count1335 b)) else (if i < 1339 then decide (4 ≤ count1335 b) else decide (5 ≤ count1335 b)))) else (if i < 1343 then (if i < 1341 then decide (6 ≤ count1335 b) else (if i < 1342 then decide (7 ≤ count1335 b) else decide (8 ≤ count1335 b))) else (if i < 1345 then (if i < 1344 then decide (1 ≤ count1343 b) else decide (2 ≤ count1343 b)) else (if i < 1346 then decide (3 ≤ count1343 b) else decide (4 ≤ count1343 b))))) else (if i < 1354 then (if i < 1350 then (if i < 1348 then decide (5 ≤ count1343 b) else (if i < 1349 then decide (6 ≤ count1343 b) else decide (7 ≤ count1343 b))) else (if i < 1352 then (if i < 1351 then decide (8 ≤ count1343 b) else decide (9 ≤ count1343 b)) else (if i < 1353 then decide (10 ≤ count1343 b) else decide (11 ≤ count1343 b)))) else (if i < 1358 then (if i < 1356 then (if i < 1355 then decide (12 ≤ count1343 b) else decide (13 ≤ count1343 b)) else (if i < 1357 then decide (14 ≤ count1343 b) else decide (15 ≤ count1343 b))) else (if i < 1360 then (if i < 1359 then decide (16 ≤ count1343 b) else decide (1 ≤ count1359 b)) else (if i < 1361 then decide (2 ≤ count1359 b) else decide (1 ≤ count1361 b)))))))))) else (if i < 1589 then (if i < 1475 then (if i < 1418 then (if i < 1390 then (if i < 1376 then (if i < 1369 then (if i < 1365 then (if i < 1363 then decide (2 ≤ count1361 b) else (if i < 1364 then decide (1 ≤ count1363 b) else decide (2 ≤ count1363 b))) else (if i < 1367 then (if i < 1366 then decide (3 ≤ count1363 b) else decide (4 ≤ count1363 b)) else (if i < 1368 then decide (1 ≤ count1367 b) else decide (2 ≤ count1367 b)))) else (if i < 1372 then (if i < 1370 then decide (1 ≤ count1369 b) else (if i < 1371 then decide (2 ≤ count1369 b) else decide (1 ≤ count1371 b))) else (if i < 1374 then (if i < 1373 then decide (2 ≤ count1371 b) else decide (3 ≤ count1371 b)) else (if i < 1375 then decide (4 ≤ count1371 b) else decide (1 ≤ count1375 b))))) else (if i < 1383 then (if i < 1379 then (if i < 1377 then decide (2 ≤ count1375 b) else (if i < 1378 then decide (3 ≤ count1375 b) else decide (4 ≤ count1375 b))) else (if i < 1381 then (if i < 1380 then decide (5 ≤ count1375 b) else decide (6 ≤ count1375 b)) else (if i < 1382 then decide (7 ≤ count1375 b) else decide (8 ≤ count1375 b)))) else (if i < 1386 then (if i < 1384 then decide (1 ≤ count1383 b) else (if i < 1385 then decide (2 ≤ count1383 b) else decide (1 ≤ count1385 b))) else (if i < 1388 then (if i < 1387 then decide (2 ≤ count1385 b) else decide (1 ≤ count1387 b)) else (if i < 1389 then decide (2 ≤ count1387 b) else decide (3 ≤ count1387 b)))))) else (if i < 1404 then (if i < 1397 then (if i < 1393 then (if i < 1391 then decide (4 ≤ count1387 b) else (if i < 1392 then decide (1 ≤ count1391 b) else decide (2 ≤ count1391 b))) else (if i < 1395 then (if i < 1394 then decide (1 ≤ count1393 b) else decide (2 ≤ count1393 b)) else (if i < 1396 then decide (1 ≤ count1395 b) else decide (2 ≤ count1395 b)))) else (if i < 1400 then (if i < 1398 then decide (3 ≤ count1395 b) else (if i < 1399 then decide (4 ≤ count1395 b) else decide (1 ≤ count1399 b))) else (if i < 1402 then (if i < 1401 then decide (2 ≤ count1399 b) else decide (3 ≤ count1399 b)) else (if i < 1403 then decide (4 ≤ count1399 b) else decide (5 ≤ count1399 b))))) else (if i < 1411 then (if i < 1407 then (if i < 1405 then decide (6 ≤ count1399 b) else (if i < 1406 then decide (7 ≤ count1399 b) else decide (8 ≤ count1399 b))) else (if i < 1409 then (if i < 1408 then decide (1 ≤ count1407 b) else decide (2 ≤ count1407 b)) else (if i < 1410 then decide (3 ≤ count1407 b) else decide (4 ≤ count1407 b)))) else (if i < 1414 then (if i < 1412 then decide (5 ≤ count1407 b) else (if i < 1413 then decide (6 ≤ count1407 b) else decide (7 ≤ count1407 b))) else (if i < 1416 then (if i < 1415 then decide (8 ≤ count1407 b) else decide (9 ≤ count1407 b)) else (if i < 1417 then decide (10 ≤ count1407 b) else decide (11 ≤ count1407 b))))))) else (if i < 1446 then (if i < 1432 then (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (12 ≤ count1407 b) else (if i < 1420 then decide (13 ≤ count1407 b) else decide (14 ≤ count1407 b))) else (if i < 1423 then (if i < 1422 then decide (15 ≤ count1407 b) else decide (16 ≤ count1407 b)) else (if i < 1424 then decide (1 ≤ count1423 b) else decide (2 ≤ count1423 b)))) else (if i < 1428 then (if i < 1426 then decide (3 ≤ count1423 b) else (if i < 1427 then decide (4 ≤ count1423 b) else decide (5 ≤ count1423 b))) else (if i < 1430 then (if i < 1429 then decide (6 ≤ count1423 b) else decide (7 ≤ count1423 b)) else (if i < 1431 then decide (8 ≤ count1423 b) else decide (9 ≤ count1423 b))))) else (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (10 ≤ count1423 b) else (if i < 1434 then decide (11 ≤ count1423 b) else decide (12 ≤ count1423 b))) else (if i < 1437 then (if i < 1436 then decide (13 ≤ count1423 b) else decide (14 ≤ count1423 b)) else (if i < 1438 then decide (15 ≤ count1423 b) else decide (16 ≤ count1423 b)))) else (if i < 1442 then (if i < 1440 then decide (17 ≤ count1423 b) else (if i < 1441 then decide (18 ≤ count1423 b) else decide (19 ≤ count1423 b))) else (if i < 1444 then (if i < 1443 then decide (20 ≤ count1423 b) else decide (21 ≤ count1423 b)) else (if i < 1445 then decide (22 ≤ count1423 b) else decide (23 ≤ count1423 b)))))) else (if i < 1460 then (if i < 1453 then (if i < 1449 then (if i < 1447 then decide (24 ≤ count1423 b) else (if i < 1448 then decide (25 ≤ count1423 b) else decide (26 ≤ count1423 b))) else (if i < 1451 then (if i < 1450 then decide (27 ≤ count1423 b) else decide (28 ≤ count1423 b)) else (if i < 1452 then decide (29 ≤ count1423 b) else decide (30 ≤ count1423 b)))) else (if i < 1456 then (if i < 1454 then decide (31 ≤ count1423 b) else (if i < 1455 then decide (32 ≤ count1423 b) else decide (1 ≤ count1455 b))) else (if i < 1458 then (if i < 1457 then decide (2 ≤ count1455 b) else decide (3 ≤ count1455 b)) else (if i < 1459 then decide (4 ≤ count1455 b) else decide (5 ≤ count1455 b))))) else (if i < 1467 then (if i < 1463 then (if i < 1461 then decide (6 ≤ count1455 b) else (if i < 1462 then decide (7 ≤ count1455 b) else decide (8 ≤ count1455 b))) else (if i < 1465 then (if i < 1464 then decide (9 ≤ count1455 b) else decide (10 ≤ count1455 b)) else (if i < 1466 then decide (11 ≤ count1455 b) else decide (12 ≤ count1455 b)))) else (if i < 1471 then (if i < 1469 then (if i < 1468 then decide (13 ≤ count1455 b) else decide (14 ≤ count1455 b)) else (if i < 1470 then decide (15 ≤ count1455 b) else decide (16 ≤ count1455 b))) else (if i < 1473 then (if i < 1472 then decide (17 ≤ count1455 b) else decide (18 ≤ count1455 b)) else (if i < 1474 then decide (19 ≤ count1455 b) else decide (20 ≤ count1455 b)))))))) else (if i < 1532 then (if i < 1503 then (if i < 1489 then (if i < 1482 then (if i < 1478 then (if i < 1476 then decide (21 ≤ count1455 b) else (if i < 1477 then decide (22 ≤ count1455 b) else decide (23 ≤ count1455 b))) else (if i < 1480 then (if i < 1479 then decide (24 ≤ count1455 b) else decide (25 ≤ count1455 b)) else (if i < 1481 then decide (26 ≤ count1455 b) else decide (27 ≤ count1455 b)))) else (if i < 1485 then (if i < 1483 then decide (28 ≤ count1455 b) else (if i < 1484 then decide (29 ≤ count1455 b) else decide (30 ≤ count1455 b))) else (if i < 1487 then (if i < 1486 then decide (31 ≤ count1455 b) else decide (32 ≤ count1455 b)) else (if i < 1488 then decide (33 ≤ count1455 b) else decide (34 ≤ count1455 b))))) else (if i < 1496 then (if i < 1492 then (if i < 1490 then decide (35 ≤ count1455 b) else (if i < 1491 then decide (36 ≤ count1455 b) else decide (37 ≤ count1455 b))) else (if i < 1494 then (if i < 1493 then decide (38 ≤ count1455 b) else decide (39 ≤ count1455 b)) else (if i < 1495 then decide (40 ≤ count1455 b) else decide (41 ≤ count1455 b)))) else (if i < 1499 then (if i < 1497 then decide (42 ≤ count1455 b) else (if i < 1498 then decide (1 ≤ count1497 b) else decide (2 ≤ count1497 b))) else (if i < 1501 then (if i < 1500 then decide (1 ≤ count1499 b) else decide (2 ≤ count1499 b)) else (if i < 1502 then decide (3 ≤ count1499 b) else decide (1 ≤ count1502 b)))))) else (if i < 1517 then (if i < 1510 then (if i < 1506 then (if i < 1504 then decide (2 ≤ count1502 b) else (if i < 1505 then decide (1 ≤ count1504 b) else decide (2 ≤ count1504 b))) else (if i < 1508 then (if i < 1507 then decide (1 ≤ count1506 b) else decide (2 ≤ count1506 b)) else (if i < 1509 then decide (3 ≤ count1506 b) else decide (4 ≤ count1506 b)))) else (if i < 1513 then (if i < 1511 then decide (1 ≤ count1510 b) else (if i < 1512 then decide (2 ≤ count1510 b) else decide (3 ≤ count1510 b))) else (if i < 1515 then (if i < 1514 then decide (4 ≤ count1510 b) else decide (5 ≤ count1510 b)) else (if i < 1516 then decide (6 ≤ count1510 b) else decide (7 ≤ count1510 b))))) else (if i < 1524 then (if i < 1520 then (if i < 1518 then decide (1 ≤ count1517 b) else (if i < 1519 then decide (2 ≤ count1517 b) else decide (1 ≤ count1519 b))) else (if i < 1522 then (if i < 1521 then decide (2 ≤ count1519 b) else decide (1 ≤ count1521 b)) else (if i < 1523 then decide (2 ≤ count1521 b) else decide (3 ≤ count1521 b)))) else (if i < 1528 then (if i < 1526 then (if i < 1525 then decide (4 ≤ count1521 b) else decide (1 ≤ count1525 b)) else (if i < 1527 then decide (2 ≤ count1525 b) else decide (1 ≤ count1527 b))) else (if i < 1530 then (if i < 1529 then decide (2 ≤ count1527 b) else decide (1 ≤ count1529 b)) else (if i < 1531 then decide (2 ≤ count1529 b) else decide (3 ≤ count1529 b))))))) else (if i < 1560 then (if i < 1546 then (if i < 1539 then (if i < 1535 then (if i < 1533 then decide (4 ≤ count1529 b) else (if i < 1534 then decide (1 ≤ count1533 b) else decide (2 ≤ count1533 b))) else (if i < 1537 then (if i < 1536 then decide (3 ≤ count1533 b) else decide (4 ≤ count1533 b)) else (if i < 1538 then decide (5 ≤ count1533 b) else decide (6 ≤ count1533 b)))) else (if i < 1542 then (if i < 1540 then decide (7 ≤ count1533 b) else (if i < 1541 then decide (8 ≤ count1533 b) else decide (1 ≤ count1541 b))) else (if i < 1544 then (if i < 1543 then decide (2 ≤ count1541 b) else decide (3 ≤ count1541 b)) else (if i < 1545 then decide (4 ≤ count1541 b) else decide (5 ≤ count1541 b))))) else (if i < 1553 then (if i < 1549 then (if i < 1547 then decide (6 ≤ count1541 b) else (if i < 1548 then decide (7 ≤ count1541 b) else decide (8 ≤ count1541 b))) else (if i < 1551 then (if i < 1550 then decide (9 ≤ count1541 b) else decide (10 ≤ count1541 b)) else (if i < 1552 then decide (11 ≤ count1541 b) else decide (12 ≤ count1541 b)))) else (if i < 1556 then (if i < 1554 then decide (13 ≤ count1541 b) else (if i < 1555 then decide (14 ≤ count1541 b) else decide (15 ≤ count1541 b))) else (if i < 1558 then (if i < 1557 then decide (1 ≤ count1556 b) else decide (2 ≤ count1556 b)) else (if i < 1559 then decide (1 ≤ count1558 b) else decide (2 ≤ count1558 b)))))) else (if i < 1574 then (if i < 1567 then (if i < 1563 then (if i < 1561 then decide (1 ≤ count1560 b) else (if i < 1562 then decide (2 ≤ count1560 b) else decide (3 ≤ count1560 b))) else (if i < 1565 then (if i < 1564 then decide (4 ≤ count1560 b) else decide (1 ≤ count1564 b)) else (if i < 1566 then decide (2 ≤ count1564 b) else decide (1 ≤ count1566 b)))) else (if i < 1570 then (if i < 1568 then decide (2 ≤ count1566 b) else (if i < 1569 then decide (1 ≤ count1568 b) else decide (2 ≤ count1568 b))) else (if i < 1572 then (if i < 1571 then decide (3 ≤ count1568 b) else decide (4 ≤ count1568 b)) else (if i < 1573 then decide (1 ≤ count1572 b) else decide (2 ≤ count1572 b))))) else (if i < 1581 then (if i < 1577 then (if i < 1575 then decide (3 ≤ count1572 b) else (if i < 1576 then decide (4 ≤ count1572 b) else decide (5 ≤ count1572 b))) else (if i < 1579 then (if i < 1578 then decide (6 ≤ count1572 b) else decide (7 ≤ count1572 b)) else (if i < 1580 then decide (8 ≤ count1572 b) else decide (1 ≤ count1580 b)))) else (if i < 1585 then (if i < 1583 then (if i < 1582 then decide (2 ≤ count1580 b) else decide (1 ≤ count1582 b)) else (if i < 1584 then decide (2 ≤ count1582 b) else decide (1 ≤ count1584 b))) else (if i < 1587 then (if i < 1586 then decide (2 ≤ count1584 b) else decide (3 ≤ count1584 b)) else (if i < 1588 then decide (4 ≤ count1584 b) else decide (1 ≤ count1588 b))))))))) else (if i < 1703 then (if i < 1646 then (if i < 1617 then (if i < 1603 then (if i < 1596 then (if i < 1592 then (if i < 1590 then decide (2 ≤ count1588 b) else (if i < 1591 then decide (1 ≤ count1590 b) else decide (2 ≤ count1590 b))) else (if i < 1594 then (if i < 1593 then decide (1 ≤ count1592 b) else decide (2 ≤ count1592 b)) else (if i < 1595 then decide (3 ≤ count1592 b) else decide (4 ≤ count1592 b)))) else (if i < 1599 then (if i < 1597 then decide (1 ≤ count1596 b) else (if i < 1598 then decide (2 ≤ count1596 b) else decide (3 ≤ count1596 b))) else (if i < 1601 then (if i < 1600 then decide (4 ≤ count1596 b) else decide (5 ≤ count1596 b)) else (if i < 1602 then decide (6 ≤ count1596 b) else decide (7 ≤ count1596 b))))) else (if i < 1610 then (if i < 1606 then (if i < 1604 then decide (8 ≤ count1596 b) else (if i < 1605 then decide (1 ≤ count1604 b) else decide (2 ≤ count1604 b))) else (if i < 1608 then (if i < 1607 then decide (3 ≤ count1604 b) else decide (4 ≤ count1604 b)) else (if i < 1609 then decide (5 ≤ count1604 b) else decide (6 ≤ count1604 b)))) else (if i < 1613 then (if i < 1611 then decide (7 ≤ count1604 b) else (if i < 1612 then decide (8 ≤ count1604 b) else decide (9 ≤ count1604 b))) else (if i < 1615 then (if i < 1614 then decide (10 ≤ count1604 b) else decide (11 ≤ count1604 b)) else (if i < 1616 then decide (12 ≤ count1604 b) else decide (13 ≤ count1604 b)))))) else (if i < 1631 then (if i < 1624 then (if i < 1620 then (if i < 1618 then decide (14 ≤ count1604 b) else (if i < 1619 then decide (15 ≤ count1604 b) else decide (16 ≤ count1604 b))) else (if i < 1622 then (if i < 1621 then decide (1 ≤ count1620 b) else decide (2 ≤ count1620 b)) else (if i < 1623 then decide (3 ≤ count1620 b) else decide (4 ≤ count1620 b)))) else (if i < 1627 then (if i < 1625 then decide (5 ≤ count1620 b) else (if i < 1626 then decide (6 ≤ count1620 b) else decide (7 ≤ count1620 b))) else (if i < 1629 then (if i < 1628 then decide (8 ≤ count1620 b) else decide (9 ≤ count1620 b)) else (if i < 1630 then decide (10 ≤ count1620 b) else decide (11 ≤ count1620 b))))) else (if i < 1638 then (if i < 1634 then (if i < 1632 then decide (12 ≤ count1620 b) else (if i < 1633 then decide (13 ≤ count1620 b) else decide (14 ≤ count1620 b))) else (if i < 1636 then (if i < 1635 then decide (15 ≤ count1620 b) else decide (16 ≤ count1620 b)) else (if i < 1637 then decide (17 ≤ count1620 b) else decide (18 ≤ count1620 b)))) else (if i < 1642 then (if i < 1640 then (if i < 1639 then decide (19 ≤ count1620 b) else decide (20 ≤ count1620 b)) else (if i < 1641 then decide (21 ≤ count1620 b) else decide (22 ≤ count1620 b))) else (if i < 1644 then (if i < 1643 then decide (23 ≤ count1620 b) else decide (1 ≤ count1643 b)) else (if i < 1645 then decide (2 ≤ count1643 b) else decide (1 ≤ count1645 b))))))) else (if i < 1674 then (if i < 1660 then (if i < 1653 then (if i < 1649 then (if i < 1647 then decide (2 ≤ count1645 b) else (if i < 1648 then decide (1 ≤ count1647 b) else decide (2 ≤ count1647 b))) else (if i < 1651 then (if i < 1650 then decide (3 ≤ count1647 b) else decide (4 ≤ count1647 b)) else (if i < 1652 then decide (1 ≤ count1651 b) else decide (2 ≤ count1651 b)))) else (if i < 1656 then (if i < 1654 then decide (1 ≤ count1653 b) else (if i < 1655 then decide (2 ≤ count1653 b) else decide (1 ≤ count1655 b))) else (if i < 1658 then (if i < 1657 then decide (2 ≤ count1655 b) else decide (3 ≤ count1655 b)) else (if i < 1659 then decide (4 ≤ count1655 b) else decide (1 ≤ count1659 b))))) else (if i < 1667 then (if i < 1663 then (if i < 1661 then decide (2 ≤ count1659 b) else (if i < 1662 then decide (3 ≤ count1659 b) else decide (4 ≤ count1659 b))) else (if i < 1665 then (if i < 1664 then decide (5 ≤ count1659 b) else decide (6 ≤ count1659 b)) else (if i < 1666 then decide (7 ≤ count1659 b) else decide (8 ≤ count1659 b)))) else (if i < 1670 then (if i < 1668 then decide (1 ≤ count1667 b) else (if i < 1669 then decide (2 ≤ count1667 b) else decide (1 ≤ count1669 b))) else (if i < 1672 then (if i < 1671 then decide (2 ≤ count1669 b) else decide (1 ≤ count1671 b)) else (if i < 1673 then decide (2 ≤ count1671 b) else decide (3 ≤ count1671 b)))))) else (if i < 1688 then (if i < 1681 then (if i < 1677 then (if i < 1675 then decide (4 ≤ count1671 b) else (if i < 1676 then decide (1 ≤ count1675 b) else decide (2 ≤ count1675 b))) else (if i < 1679 then (if i < 1678 then decide (1 ≤ count1677 b) else decide (2 ≤ count1677 b)) else (if i < 1680 then decide (1 ≤ count1679 b) else decide (2 ≤ count1679 b)))) else (if i < 1684 then (if i < 1682 then decide (3 ≤ count1679 b) else (if i < 1683 then decide (4 ≤ count1679 b) else decide (1 ≤ count1683 b))) else (if i < 1686 then (if i < 1685 then decide (2 ≤ count1683 b) else decide (3 ≤ count1683 b)) else (if i < 1687 then decide (4 ≤ count1683 b) else decide (5 ≤ count1683 b))))) else (if i < 1695 then (if i < 1691 then (if i < 1689 then decide (6 ≤ count1683 b) else (if i < 1690 then decide (7 ≤ count1683 b) else decide (8 ≤ count1683 b))) else (if i < 1693 then (if i < 1692 then decide (1 ≤ count1691 b) else decide (2 ≤ count1691 b)) else (if i < 1694 then decide (3 ≤ count1691 b) else decide (4 ≤ count1691 b)))) else (if i < 1699 then (if i < 1697 then (if i < 1696 then decide (5 ≤ count1691 b) else decide (6 ≤ count1691 b)) else (if i < 1698 then decide (7 ≤ count1691 b) else decide (8 ≤ count1691 b))) else (if i < 1701 then (if i < 1700 then decide (9 ≤ count1691 b) else decide (10 ≤ count1691 b)) else (if i < 1702 then decide (11 ≤ count1691 b) else decide (12 ≤ count1691 b)))))))) else (if i < 1760 then (if i < 1731 then (if i < 1717 then (if i < 1710 then (if i < 1706 then (if i < 1704 then decide (13 ≤ count1691 b) else (if i < 1705 then decide (14 ≤ count1691 b) else decide (15 ≤ count1691 b))) else (if i < 1708 then (if i < 1707 then decide (16 ≤ count1691 b) else decide (1 ≤ count1707 b)) else (if i < 1709 then decide (2 ≤ count1707 b) else decide (1 ≤ count1709 b)))) else (if i < 1713 then (if i < 1711 then decide (2 ≤ count1709 b) else (if i < 1712 then decide (1 ≤ count1711 b) else decide (2 ≤ count1711 b))) else (if i < 1715 then (if i < 1714 then decide (3 ≤ count1711 b) else decide (4 ≤ count1711 b)) else (if i < 1716 then decide (1 ≤ count1715 b) else decide (2 ≤ count1715 b))))) else (if i < 1724 then (if i < 1720 then (if i < 1718 then decide (1 ≤ count1717 b) else (if i < 1719 then decide (2 ≤ count1717 b) else decide (1 ≤ count1719 b))) else (if i < 1722 then (if i < 1721 then decide (2 ≤ count1719 b) else decide (3 ≤ count1719 b)) else (if i < 1723 then decide (4 ≤ count1719 b) else decide (1 ≤ count1723 b)))) else (if i < 1727 then (if i < 1725 then decide (2 ≤ count1723 b) else (if i < 1726 then decide (3 ≤ count1723 b) else decide (4 ≤ count1723 b))) else (if i < 1729 then (if i < 1728 then decide (5 ≤ count1723 b) else decide (6 ≤ count1723 b)) else (if i < 1730 then decide (7 ≤ count1723 b) else decide (8 ≤ count1723 b)))))) else (if i < 1745 then (if i < 1738 then (if i < 1734 then (if i < 1732 then decide (1 ≤ count1731 b) else (if i < 1733 then decide (2 ≤ count1731 b) else decide (1 ≤ count1733 b))) else (if i < 1736 then (if i < 1735 then decide (2 ≤ count1733 b) else decide (1 ≤ count1735 b)) else (if i < 1737 then decide (2 ≤ count1735 b) else decide (3 ≤ count1735 b)))) else (if i < 1741 then (if i < 1739 then decide (4 ≤ count1735 b) else (if i < 1740 then decide (1 ≤ count1739 b) else decide (2 ≤ count1739 b))) else (if i < 1743 then (if i < 1742 then decide (1 ≤ count1741 b) else decide (2 ≤ count1741 b)) else (if i < 1744 then decide (1 ≤ count1743 b) else decide (2 ≤ count1743 b))))) else (if i < 1752 then (if i < 1748 then (if i < 1746 then decide (3 ≤ count1743 b) else (if i < 1747 then decide (4 ≤ count1743 b) else decide (1 ≤ count1747 b))) else (if i < 1750 then (if i < 1749 then decide (2 ≤ count1747 b) else decide (3 ≤ count1747 b)) else (if i < 1751 then decide (4 ≤ count1747 b) else decide (5 ≤ count1747 b)))) else (if i < 1756 then (if i < 1754 then (if i < 1753 then decide (6 ≤ count1747 b) else decide (7 ≤ count1747 b)) else (if i < 1755 then decide (8 ≤ count1747 b) else decide (1 ≤ count1755 b))) else (if i < 1758 then (if i < 1757 then decide (2 ≤ count1755 b) else decide (3 ≤ count1755 b)) else (if i < 1759 then decide (4 ≤ count1755 b) else decide (5 ≤ count1755 b))))))) else (if i < 1788 then (if i < 1774 then (if i < 1767 then (if i < 1763 then (if i < 1761 then decide (6 ≤ count1755 b) else (if i < 1762 then decide (7 ≤ count1755 b) else decide (8 ≤ count1755 b))) else (if i < 1765 then (if i < 1764 then decide (9 ≤ count1755 b) else decide (10 ≤ count1755 b)) else (if i < 1766 then decide (11 ≤ count1755 b) else decide (12 ≤ count1755 b)))) else (if i < 1770 then (if i < 1768 then decide (13 ≤ count1755 b) else (if i < 1769 then decide (14 ≤ count1755 b) else decide (15 ≤ count1755 b))) else (if i < 1772 then (if i < 1771 then decide (16 ≤ count1755 b) else decide (1 ≤ count1771 b)) else (if i < 1773 then decide (2 ≤ count1771 b) else decide (3 ≤ count1771 b))))) else (if i < 1781 then (if i < 1777 then (if i < 1775 then decide (4 ≤ count1771 b) else (if i < 1776 then decide (5 ≤ count1771 b) else decide (6 ≤ count1771 b))) else (if i < 1779 then (if i < 1778 then decide (7 ≤ count1771 b) else decide (8 ≤ count1771 b)) else (if i < 1780 then decide (9 ≤ count1771 b) else decide (10 ≤ count1771 b)))) else (if i < 1784 then (if i < 1782 then decide (11 ≤ count1771 b) else (if i < 1783 then decide (12 ≤ count1771 b) else decide (13 ≤ count1771 b))) else (if i < 1786 then (if i < 1785 then decide (14 ≤ count1771 b) else decide (15 ≤ count1771 b)) else (if i < 1787 then decide (16 ≤ count1771 b) else decide (17 ≤ count1771 b)))))) else (if i < 1802 then (if i < 1795 then (if i < 1791 then (if i < 1789 then decide (18 ≤ count1771 b) else (if i < 1790 then decide (19 ≤ count1771 b) else decide (20 ≤ count1771 b))) else (if i < 1793 then (if i < 1792 then decide (21 ≤ count1771 b) else decide (22 ≤ count1771 b)) else (if i < 1794 then decide (23 ≤ count1771 b) else decide (1 ≤ count1794 b)))) else (if i < 1798 then (if i < 1796 then decide (2 ≤ count1794 b) else (if i < 1797 then decide (3 ≤ count1794 b) else decide (4 ≤ count1794 b))) else (if i < 1800 then (if i < 1799 then decide (5 ≤ count1794 b) else decide (6 ≤ count1794 b)) else (if i < 1801 then decide (7 ≤ count1794 b) else decide (8 ≤ count1794 b))))) else (if i < 1809 then (if i < 1805 then (if i < 1803 then decide (9 ≤ count1794 b) else (if i < 1804 then decide (10 ≤ count1794 b) else decide (11 ≤ count1794 b))) else (if i < 1807 then (if i < 1806 then decide (12 ≤ count1794 b) else decide (13 ≤ count1794 b)) else (if i < 1808 then decide (14 ≤ count1794 b) else decide (15 ≤ count1794 b)))) else (if i < 1813 then (if i < 1811 then (if i < 1810 then decide (16 ≤ count1794 b) else decide (17 ≤ count1794 b)) else (if i < 1812 then decide (18 ≤ count1794 b) else decide (19 ≤ count1794 b))) else (if i < 1815 then (if i < 1814 then decide (20 ≤ count1794 b) else decide (21 ≤ count1794 b)) else (if i < 1816 then decide (22 ≤ count1794 b) else decide (23 ≤ count1794 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (69 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (72 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (74 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (75 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (76 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (84 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (85 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (87 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (89 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (91 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (95 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (130 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (131 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (132 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (133 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (137 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (138 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (139 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (140 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (142 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (144 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (148 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (149 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (150 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (151 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (152 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (153 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (155 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (159 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (192 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (193 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (197 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (199 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (200 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (201 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (203 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (205 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (207 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (209 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (210 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (211 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (214 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (218 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (220 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (221 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (222 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (258 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (259 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (260 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (261 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (265 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (266 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (267 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (268 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (270 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (272 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (276 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (277 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (279 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (280 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (281 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (283 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (287 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (320 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (321 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (322 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (323 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (325 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (328 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (331 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (333 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (335 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (337 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (338 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (339 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (342 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (344 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (348 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (349 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (350 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (351 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (384 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (385 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (386 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (387 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (389 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (391 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (393 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (394 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (396 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (397 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (398 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (399 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (400 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (401 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (402 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (403 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (406 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (408 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (409 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (410 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (412 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (413 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (414 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (448 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (450 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (451 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (452 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (454 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (455 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (456 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (457 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (458 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (460 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (462 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (464 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (468 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (469 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (471 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (473 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (474 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (475 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (477 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (479 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (74 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (85 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (89 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (91 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (153 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (203 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (209 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (210 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (322 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (325 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (387 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (454 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (469 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (471 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value332 (q : Snake 81) : valuation q 332 = decide (2 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value334 (q : Snake 81) : valuation q 334 = decide (2 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value366 (q : Snake 81) : valuation q 366 = decide (2 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value384 (q : Snake 81) : valuation q 384 = decide (2 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value396 (q : Snake 81) : valuation q 396 = decide (2 ≤ count395 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value487 (q : Snake 81) : valuation q 487 = decide (1 ≤ count487 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value490 (q : Snake 81) : valuation q 490 = decide (2 ≤ count489 (baseVal q)) := rfl
theorem value492 (q : Snake 81) : valuation q 492 = decide (2 ≤ count491 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (1 ≤ count1497 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (2 ≤ count1497 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (1 ≤ count1499 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (2 ≤ count1499 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (3 ≤ count1499 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (1 ≤ count1502 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (1 ≤ count1504 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (2 ≤ count1504 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (1 ≤ count1506 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (2 ≤ count1506 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (3 ≤ count1506 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (2 ≤ count1510 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (3 ≤ count1510 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (4 ≤ count1510 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (5 ≤ count1510 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (1 ≤ count1517 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (2 ≤ count1517 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (1 ≤ count1519 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (2 ≤ count1519 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (1 ≤ count1521 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (2 ≤ count1521 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (3 ≤ count1521 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (4 ≤ count1521 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (1 ≤ count1525 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (2 ≤ count1525 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (1 ≤ count1527 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (2 ≤ count1527 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (1 ≤ count1529 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (2 ≤ count1529 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (3 ≤ count1529 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (1 ≤ count1533 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (2 ≤ count1533 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (3 ≤ count1533 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (4 ≤ count1533 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (5 ≤ count1533 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (3 ≤ count1541 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (4 ≤ count1541 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (5 ≤ count1541 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (6 ≤ count1541 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (7 ≤ count1541 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (8 ≤ count1541 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (1 ≤ count1556 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (2 ≤ count1556 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (1 ≤ count1558 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (2 ≤ count1558 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (1 ≤ count1560 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (2 ≤ count1560 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (3 ≤ count1560 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (4 ≤ count1560 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (1 ≤ count1566 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (2 ≤ count1566 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (1 ≤ count1568 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (2 ≤ count1568 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (3 ≤ count1568 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (1 ≤ count1572 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (2 ≤ count1572 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (3 ≤ count1572 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (4 ≤ count1572 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (5 ≤ count1572 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (6 ≤ count1572 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (7 ≤ count1572 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (1 ≤ count1582 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (2 ≤ count1582 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (1 ≤ count1584 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (2 ≤ count1584 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (3 ≤ count1584 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (4 ≤ count1584 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (1 ≤ count1588 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (2 ≤ count1588 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (1 ≤ count1590 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (2 ≤ count1590 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (1 ≤ count1592 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (2 ≤ count1592 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (3 ≤ count1592 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (1 ≤ count1596 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (2 ≤ count1596 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (3 ≤ count1596 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (4 ≤ count1596 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (5 ≤ count1596 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (3 ≤ count1604 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (4 ≤ count1604 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (5 ≤ count1604 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (6 ≤ count1604 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (7 ≤ count1604 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (8 ≤ count1604 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (9 ≤ count1604 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (10 ≤ count1604 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (7 ≤ count1620 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (8 ≤ count1620 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (9 ≤ count1620 (baseVal q)) := rfl
theorem value1629 (q : Snake 81) : valuation q 1629 = decide (10 ≤ count1620 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (11 ≤ count1620 (baseVal q)) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (12 ≤ count1620 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (13 ≤ count1620 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (14 ≤ count1620 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (15 ≤ count1620 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (1 ≤ count1643 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (2 ≤ count1643 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (1 ≤ count1645 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (2 ≤ count1645 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (1 ≤ count1647 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (2 ≤ count1647 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (3 ≤ count1647 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (4 ≤ count1647 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (1 ≤ count1651 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (2 ≤ count1651 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (1 ≤ count1653 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (2 ≤ count1653 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (1 ≤ count1655 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (2 ≤ count1655 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (3 ≤ count1655 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (4 ≤ count1655 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (1 ≤ count1659 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (2 ≤ count1659 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (3 ≤ count1659 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (4 ≤ count1659 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (5 ≤ count1659 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (6 ≤ count1659 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (1 ≤ count1667 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (2 ≤ count1667 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (1 ≤ count1669 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (2 ≤ count1669 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (1 ≤ count1671 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (2 ≤ count1671 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (3 ≤ count1671 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (4 ≤ count1671 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (1 ≤ count1675 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (2 ≤ count1675 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (1 ≤ count1677 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (2 ≤ count1677 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (1 ≤ count1679 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (2 ≤ count1679 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (3 ≤ count1679 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (4 ≤ count1679 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (1 ≤ count1683 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (2 ≤ count1683 (baseVal q)) := rfl
theorem value1685 (q : Snake 81) : valuation q 1685 = decide (3 ≤ count1683 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (4 ≤ count1683 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (5 ≤ count1683 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (6 ≤ count1683 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (7 ≤ count1683 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (1 ≤ count1691 (baseVal q)) := rfl
theorem value1692 (q : Snake 81) : valuation q 1692 = decide (2 ≤ count1691 (baseVal q)) := rfl
theorem value1693 (q : Snake 81) : valuation q 1693 = decide (3 ≤ count1691 (baseVal q)) := rfl
theorem value1694 (q : Snake 81) : valuation q 1694 = decide (4 ≤ count1691 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (5 ≤ count1691 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (6 ≤ count1691 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (7 ≤ count1691 (baseVal q)) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (8 ≤ count1691 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (9 ≤ count1691 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (10 ≤ count1691 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (1 ≤ count1707 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (2 ≤ count1707 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (1 ≤ count1709 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (2 ≤ count1709 (baseVal q)) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (1 ≤ count1711 (baseVal q)) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (2 ≤ count1711 (baseVal q)) := rfl
theorem value1713 (q : Snake 81) : valuation q 1713 = decide (3 ≤ count1711 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (4 ≤ count1711 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (1 ≤ count1715 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (2 ≤ count1715 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (1 ≤ count1717 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (2 ≤ count1717 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (1 ≤ count1719 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (2 ≤ count1719 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (3 ≤ count1719 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (4 ≤ count1719 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (1 ≤ count1723 (baseVal q)) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (2 ≤ count1723 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (3 ≤ count1723 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (4 ≤ count1723 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (5 ≤ count1723 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (6 ≤ count1723 (baseVal q)) := rfl
theorem value1729 (q : Snake 81) : valuation q 1729 = decide (7 ≤ count1723 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (1 ≤ count1731 (baseVal q)) := rfl
theorem value1732 (q : Snake 81) : valuation q 1732 = decide (2 ≤ count1731 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (1 ≤ count1733 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (2 ≤ count1733 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (1 ≤ count1735 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (2 ≤ count1735 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (3 ≤ count1735 (baseVal q)) := rfl
theorem value1738 (q : Snake 81) : valuation q 1738 = decide (4 ≤ count1735 (baseVal q)) := rfl
theorem value1739 (q : Snake 81) : valuation q 1739 = decide (1 ≤ count1739 (baseVal q)) := rfl
theorem value1740 (q : Snake 81) : valuation q 1740 = decide (2 ≤ count1739 (baseVal q)) := rfl
theorem value1741 (q : Snake 81) : valuation q 1741 = decide (1 ≤ count1741 (baseVal q)) := rfl
theorem value1742 (q : Snake 81) : valuation q 1742 = decide (2 ≤ count1741 (baseVal q)) := rfl
theorem value1743 (q : Snake 81) : valuation q 1743 = decide (1 ≤ count1743 (baseVal q)) := rfl
theorem value1744 (q : Snake 81) : valuation q 1744 = decide (2 ≤ count1743 (baseVal q)) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (3 ≤ count1743 (baseVal q)) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (4 ≤ count1743 (baseVal q)) := rfl
theorem value1747 (q : Snake 81) : valuation q 1747 = decide (1 ≤ count1747 (baseVal q)) := rfl
theorem value1748 (q : Snake 81) : valuation q 1748 = decide (2 ≤ count1747 (baseVal q)) := rfl
theorem value1749 (q : Snake 81) : valuation q 1749 = decide (3 ≤ count1747 (baseVal q)) := rfl
theorem value1750 (q : Snake 81) : valuation q 1750 = decide (4 ≤ count1747 (baseVal q)) := rfl
theorem value1751 (q : Snake 81) : valuation q 1751 = decide (5 ≤ count1747 (baseVal q)) := rfl
theorem value1757 (q : Snake 81) : valuation q 1757 = decide (3 ≤ count1755 (baseVal q)) := rfl
theorem value1758 (q : Snake 81) : valuation q 1758 = decide (4 ≤ count1755 (baseVal q)) := rfl
theorem value1759 (q : Snake 81) : valuation q 1759 = decide (5 ≤ count1755 (baseVal q)) := rfl
theorem value1760 (q : Snake 81) : valuation q 1760 = decide (6 ≤ count1755 (baseVal q)) := rfl
theorem value1761 (q : Snake 81) : valuation q 1761 = decide (7 ≤ count1755 (baseVal q)) := rfl
theorem value1762 (q : Snake 81) : valuation q 1762 = decide (8 ≤ count1755 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (9 ≤ count1755 (baseVal q)) := rfl
theorem value1764 (q : Snake 81) : valuation q 1764 = decide (10 ≤ count1755 (baseVal q)) := rfl
theorem value1778 (q : Snake 81) : valuation q 1778 = decide (8 ≤ count1771 (baseVal q)) := rfl
theorem value1779 (q : Snake 81) : valuation q 1779 = decide (9 ≤ count1771 (baseVal q)) := rfl
theorem value1780 (q : Snake 81) : valuation q 1780 = decide (10 ≤ count1771 (baseVal q)) := rfl
theorem value1781 (q : Snake 81) : valuation q 1781 = decide (11 ≤ count1771 (baseVal q)) := rfl
theorem value1782 (q : Snake 81) : valuation q 1782 = decide (12 ≤ count1771 (baseVal q)) := rfl
theorem value1783 (q : Snake 81) : valuation q 1783 = decide (13 ≤ count1771 (baseVal q)) := rfl
theorem value1784 (q : Snake 81) : valuation q 1784 = decide (14 ≤ count1771 (baseVal q)) := rfl
theorem value1785 (q : Snake 81) : valuation q 1785 = decide (15 ≤ count1771 (baseVal q)) := rfl
theorem value1786 (q : Snake 81) : valuation q 1786 = decide (16 ≤ count1771 (baseVal q)) := rfl
theorem value1816 (q : Snake 81) : valuation q 1816 = decide (23 ≤ count1794 (baseVal q)) := rfl
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
theorem meaningNeg119 (b : Nat → Bool) : literal (valuationOf b) (-119) = decide (1 ≤ countLit b [-119]) := by
  change literal b (-119) = decide (1 ≤ countLit b [-119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-119) <;> decide
theorem meaningNeg117 (b : Nat → Bool) : literal (valuationOf b) (-117) = decide (1 ≤ countLit b [-117]) := by
  change literal b (-117) = decide (1 ≤ countLit b [-117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-117) <;> decide
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
theorem meaningNeg87 (b : Nat → Bool) : literal (valuationOf b) (-87) = decide (1 ≤ countLit b [-87]) := by
  change literal b (-87) = decide (1 ≤ countLit b [-87])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-87) <;> decide
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
theorem meaningNeg75 (b : Nat → Bool) : literal (valuationOf b) (-75) = decide (1 ≤ countLit b [-75]) := by
  change literal b (-75) = decide (1 ≤ countLit b [-75])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-75) <;> decide
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
theorem meaningNeg62 (b : Nat → Bool) : literal (valuationOf b) (-62) = decide (1 ≤ countLit b [-62]) := by
  change literal b (-62) = decide (1 ≤ countLit b [-62])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-62) <;> decide
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
theorem meaningNeg57 (b : Nat → Bool) : literal (valuationOf b) (-57) = decide (1 ≤ countLit b [-57]) := by
  change literal b (-57) = decide (1 ≤ countLit b [-57])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-57) <;> decide
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
theorem meaningNeg22 (b : Nat → Bool) : literal (valuationOf b) (-22) = decide (1 ≤ countLit b [-22]) := by
  change literal b (-22) = decide (1 ≤ countLit b [-22])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-22) <;> decide
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
theorem meaningNeg13 (b : Nat → Bool) : literal (valuationOf b) (-13) = decide (1 ≤ countLit b [-13]) := by
  change literal b (-13) = decide (1 ≤ countLit b [-13])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-13) <;> decide
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
theorem meaningNeg5 (b : Nat → Bool) : literal (valuationOf b) (-5) = decide (1 ≤ countLit b [-5]) := by
  change literal b (-5) = decide (1 ≤ countLit b [-5])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-5) <;> decide
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
theorem meaning131 (b : Nat → Bool) : literal (valuationOf b) (131) = decide (1 ≤ countLit b [131]) := by
  change literal b (131) = decide (1 ≤ countLit b [131])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (131) <;> decide
theorem meaning133 (b : Nat → Bool) : literal (valuationOf b) (133) = decide (1 ≤ countLit b [133]) := by
  change literal b (133) = decide (1 ≤ countLit b [133])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (133) <;> decide
theorem meaning135 (b : Nat → Bool) : literal (valuationOf b) (135) = decide (1 ≤ countLit b [135]) := by
  change literal b (135) = decide (1 ≤ countLit b [135])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (135) <;> decide
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
theorem meaning162 (b : Nat → Bool) : literal (valuationOf b) (162) = decide (1 ≤ countLit b [162]) := by
  change literal b (162) = decide (1 ≤ countLit b [162])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (162) <;> decide
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
theorem meaning164 (b : Nat → Bool) : literal (valuationOf b) (164) = decide (1 ≤ countLit b [164]) := by
  change literal b (164) = decide (1 ≤ countLit b [164])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (164) <;> decide
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
theorem meaning192 (b : Nat → Bool) : literal (valuationOf b) (192) = decide (1 ≤ countLit b [192]) := by
  change literal b (192) = decide (1 ≤ countLit b [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (192) <;> decide
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
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
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
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) (217) = decide (1 ≤ countLit b [217]) := by
  change literal b (217) = decide (1 ≤ countLit b [217])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (217) <;> decide
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) (219) = decide (1 ≤ countLit b [219]) := by
  change literal b (219) = decide (1 ≤ countLit b [219])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (219) <;> decide
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) (227) = decide (1 ≤ countLit b [227]) := by
  change literal b (227) = decide (1 ≤ countLit b [227])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (227) <;> decide
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) (228) = decide (1 ≤ countLit b [228]) := by
  change literal b (228) = decide (1 ≤ countLit b [228])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (228) <;> decide
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) (242) = decide (1 ≤ countLit b [242]) := by
  change literal b (242) = decide (1 ≤ countLit b [242])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (242) <;> decide
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning332 (b : Nat → Bool) : literal (valuationOf b) 332 = decide (2 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning334 (b : Nat → Bool) : literal (valuationOf b) 334 = decide (2 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning366 (b : Nat → Bool) : literal (valuationOf b) 366 = decide (2 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning384 (b : Nat → Bool) : literal (valuationOf b) 384 = decide (2 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning396 (b : Nat → Bool) : literal (valuationOf b) 396 = decide (2 ≤ count395 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning487 (b : Nat → Bool) : literal (valuationOf b) 487 = decide (1 ≤ count487 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning490 (b : Nat → Bool) : literal (valuationOf b) 490 = decide (2 ≤ count489 b) := rfl
theorem meaning492 (b : Nat → Bool) : literal (valuationOf b) 492 = decide (2 ≤ count491 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (1 ≤ count1497 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (2 ≤ count1497 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (1 ≤ count1499 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (2 ≤ count1499 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (3 ≤ count1499 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (1 ≤ count1502 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (1 ≤ count1504 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (2 ≤ count1504 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (1 ≤ count1506 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (2 ≤ count1506 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (3 ≤ count1506 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (2 ≤ count1510 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (3 ≤ count1510 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (4 ≤ count1510 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (5 ≤ count1510 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (1 ≤ count1517 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (2 ≤ count1517 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (1 ≤ count1519 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (2 ≤ count1519 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (1 ≤ count1521 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (2 ≤ count1521 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (3 ≤ count1521 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (4 ≤ count1521 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (1 ≤ count1525 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (2 ≤ count1525 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (1 ≤ count1527 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (2 ≤ count1527 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (1 ≤ count1529 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (2 ≤ count1529 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (3 ≤ count1529 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (1 ≤ count1533 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (2 ≤ count1533 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (3 ≤ count1533 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (4 ≤ count1533 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (5 ≤ count1533 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (3 ≤ count1541 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (4 ≤ count1541 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (5 ≤ count1541 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (6 ≤ count1541 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (7 ≤ count1541 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (8 ≤ count1541 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (1 ≤ count1556 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (2 ≤ count1556 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (1 ≤ count1558 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (2 ≤ count1558 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (1 ≤ count1560 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (2 ≤ count1560 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (3 ≤ count1560 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (4 ≤ count1560 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (1 ≤ count1566 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (2 ≤ count1566 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (1 ≤ count1568 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (2 ≤ count1568 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (3 ≤ count1568 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (1 ≤ count1572 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (2 ≤ count1572 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (3 ≤ count1572 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (4 ≤ count1572 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (5 ≤ count1572 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (6 ≤ count1572 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (7 ≤ count1572 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (1 ≤ count1582 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (2 ≤ count1582 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (1 ≤ count1584 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (2 ≤ count1584 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (3 ≤ count1584 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (4 ≤ count1584 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (1 ≤ count1588 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (2 ≤ count1588 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (1 ≤ count1590 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (2 ≤ count1590 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (1 ≤ count1592 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (2 ≤ count1592 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (3 ≤ count1592 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (1 ≤ count1596 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (2 ≤ count1596 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (3 ≤ count1596 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (4 ≤ count1596 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (5 ≤ count1596 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (3 ≤ count1604 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (4 ≤ count1604 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (5 ≤ count1604 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (6 ≤ count1604 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (7 ≤ count1604 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (8 ≤ count1604 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (9 ≤ count1604 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (10 ≤ count1604 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (7 ≤ count1620 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (8 ≤ count1620 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (9 ≤ count1620 b) := rfl
theorem meaning1629 (b : Nat → Bool) : literal (valuationOf b) 1629 = decide (10 ≤ count1620 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (11 ≤ count1620 b) := rfl
theorem meaning1631 (b : Nat → Bool) : literal (valuationOf b) 1631 = decide (12 ≤ count1620 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (13 ≤ count1620 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (14 ≤ count1620 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (15 ≤ count1620 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (1 ≤ count1643 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (2 ≤ count1643 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (1 ≤ count1645 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (2 ≤ count1645 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (1 ≤ count1647 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (2 ≤ count1647 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (3 ≤ count1647 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (4 ≤ count1647 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (1 ≤ count1651 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (2 ≤ count1651 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (1 ≤ count1653 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (2 ≤ count1653 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (1 ≤ count1655 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (2 ≤ count1655 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (3 ≤ count1655 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (4 ≤ count1655 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (1 ≤ count1659 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (2 ≤ count1659 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (3 ≤ count1659 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (4 ≤ count1659 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (5 ≤ count1659 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (6 ≤ count1659 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (1 ≤ count1667 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (2 ≤ count1667 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (1 ≤ count1669 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (2 ≤ count1669 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (1 ≤ count1671 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (2 ≤ count1671 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (3 ≤ count1671 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (4 ≤ count1671 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (1 ≤ count1675 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (2 ≤ count1675 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (1 ≤ count1677 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (2 ≤ count1677 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (1 ≤ count1679 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (2 ≤ count1679 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (3 ≤ count1679 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (4 ≤ count1679 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (1 ≤ count1683 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (2 ≤ count1683 b) := rfl
theorem meaning1685 (b : Nat → Bool) : literal (valuationOf b) 1685 = decide (3 ≤ count1683 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (4 ≤ count1683 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (5 ≤ count1683 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (6 ≤ count1683 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (7 ≤ count1683 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (1 ≤ count1691 b) := rfl
theorem meaning1692 (b : Nat → Bool) : literal (valuationOf b) 1692 = decide (2 ≤ count1691 b) := rfl
theorem meaning1693 (b : Nat → Bool) : literal (valuationOf b) 1693 = decide (3 ≤ count1691 b) := rfl
theorem meaning1694 (b : Nat → Bool) : literal (valuationOf b) 1694 = decide (4 ≤ count1691 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (5 ≤ count1691 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (6 ≤ count1691 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (7 ≤ count1691 b) := rfl
theorem meaning1698 (b : Nat → Bool) : literal (valuationOf b) 1698 = decide (8 ≤ count1691 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (9 ≤ count1691 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (10 ≤ count1691 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (1 ≤ count1707 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (2 ≤ count1707 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (1 ≤ count1709 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (2 ≤ count1709 b) := rfl
theorem meaning1711 (b : Nat → Bool) : literal (valuationOf b) 1711 = decide (1 ≤ count1711 b) := rfl
theorem meaning1712 (b : Nat → Bool) : literal (valuationOf b) 1712 = decide (2 ≤ count1711 b) := rfl
theorem meaning1713 (b : Nat → Bool) : literal (valuationOf b) 1713 = decide (3 ≤ count1711 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (4 ≤ count1711 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (1 ≤ count1715 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (2 ≤ count1715 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (1 ≤ count1717 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (2 ≤ count1717 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (1 ≤ count1719 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (2 ≤ count1719 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (3 ≤ count1719 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (4 ≤ count1719 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (1 ≤ count1723 b) := rfl
theorem meaning1724 (b : Nat → Bool) : literal (valuationOf b) 1724 = decide (2 ≤ count1723 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (3 ≤ count1723 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (4 ≤ count1723 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (5 ≤ count1723 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (6 ≤ count1723 b) := rfl
theorem meaning1729 (b : Nat → Bool) : literal (valuationOf b) 1729 = decide (7 ≤ count1723 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (1 ≤ count1731 b) := rfl
theorem meaning1732 (b : Nat → Bool) : literal (valuationOf b) 1732 = decide (2 ≤ count1731 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (1 ≤ count1733 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (2 ≤ count1733 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (1 ≤ count1735 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (2 ≤ count1735 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (3 ≤ count1735 b) := rfl
theorem meaning1738 (b : Nat → Bool) : literal (valuationOf b) 1738 = decide (4 ≤ count1735 b) := rfl
theorem meaning1739 (b : Nat → Bool) : literal (valuationOf b) 1739 = decide (1 ≤ count1739 b) := rfl
theorem meaning1740 (b : Nat → Bool) : literal (valuationOf b) 1740 = decide (2 ≤ count1739 b) := rfl
theorem meaning1741 (b : Nat → Bool) : literal (valuationOf b) 1741 = decide (1 ≤ count1741 b) := rfl
theorem meaning1742 (b : Nat → Bool) : literal (valuationOf b) 1742 = decide (2 ≤ count1741 b) := rfl
theorem meaning1743 (b : Nat → Bool) : literal (valuationOf b) 1743 = decide (1 ≤ count1743 b) := rfl
theorem meaning1744 (b : Nat → Bool) : literal (valuationOf b) 1744 = decide (2 ≤ count1743 b) := rfl
theorem meaning1745 (b : Nat → Bool) : literal (valuationOf b) 1745 = decide (3 ≤ count1743 b) := rfl
theorem meaning1746 (b : Nat → Bool) : literal (valuationOf b) 1746 = decide (4 ≤ count1743 b) := rfl
theorem meaning1747 (b : Nat → Bool) : literal (valuationOf b) 1747 = decide (1 ≤ count1747 b) := rfl
theorem meaning1748 (b : Nat → Bool) : literal (valuationOf b) 1748 = decide (2 ≤ count1747 b) := rfl
theorem meaning1749 (b : Nat → Bool) : literal (valuationOf b) 1749 = decide (3 ≤ count1747 b) := rfl
theorem meaning1750 (b : Nat → Bool) : literal (valuationOf b) 1750 = decide (4 ≤ count1747 b) := rfl
theorem meaning1751 (b : Nat → Bool) : literal (valuationOf b) 1751 = decide (5 ≤ count1747 b) := rfl
theorem meaning1757 (b : Nat → Bool) : literal (valuationOf b) 1757 = decide (3 ≤ count1755 b) := rfl
theorem meaning1758 (b : Nat → Bool) : literal (valuationOf b) 1758 = decide (4 ≤ count1755 b) := rfl
theorem meaning1759 (b : Nat → Bool) : literal (valuationOf b) 1759 = decide (5 ≤ count1755 b) := rfl
theorem meaning1760 (b : Nat → Bool) : literal (valuationOf b) 1760 = decide (6 ≤ count1755 b) := rfl
theorem meaning1761 (b : Nat → Bool) : literal (valuationOf b) 1761 = decide (7 ≤ count1755 b) := rfl
theorem meaning1762 (b : Nat → Bool) : literal (valuationOf b) 1762 = decide (8 ≤ count1755 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (9 ≤ count1755 b) := rfl
theorem meaning1764 (b : Nat → Bool) : literal (valuationOf b) 1764 = decide (10 ≤ count1755 b) := rfl
theorem meaning1778 (b : Nat → Bool) : literal (valuationOf b) 1778 = decide (8 ≤ count1771 b) := rfl
theorem meaning1779 (b : Nat → Bool) : literal (valuationOf b) 1779 = decide (9 ≤ count1771 b) := rfl
theorem meaning1780 (b : Nat → Bool) : literal (valuationOf b) 1780 = decide (10 ≤ count1771 b) := rfl
theorem meaning1781 (b : Nat → Bool) : literal (valuationOf b) 1781 = decide (11 ≤ count1771 b) := rfl
theorem meaning1782 (b : Nat → Bool) : literal (valuationOf b) 1782 = decide (12 ≤ count1771 b) := rfl
theorem meaning1783 (b : Nat → Bool) : literal (valuationOf b) 1783 = decide (13 ≤ count1771 b) := rfl
theorem meaning1784 (b : Nat → Bool) : literal (valuationOf b) 1784 = decide (14 ≤ count1771 b) := rfl
theorem meaning1785 (b : Nat → Bool) : literal (valuationOf b) 1785 = decide (15 ≤ count1771 b) := rfl
theorem meaning1786 (b : Nat → Bool) : literal (valuationOf b) 1786 = decide (16 ≤ count1771 b) := rfl
theorem meaning1816 (b : Nat → Bool) : literal (valuationOf b) 1816 = decide (23 ≤ count1794 b) := rfl
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
end Snake9.Regrowth.E112186
