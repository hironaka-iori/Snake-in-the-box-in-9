import E112120Data
namespace Snake9.Regrowth.E112120
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 116 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (11 : Vertex)) else decide (InPath q (13 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (15 : Vertex)) else decide (InPath q (24 : Vertex))) else (if i < 6 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (72 : Vertex)) else (if i < 9 then decide (InPath q (76 : Vertex)) else decide (InPath q (130 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex))) else (if i < 13 then decide (InPath q (135 : Vertex)) else decide (InPath q (136 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (137 : Vertex)) else (if i < 16 then decide (InPath q (138 : Vertex)) else decide (InPath q (140 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (142 : Vertex)) else decide (InPath q (144 : Vertex))) else (if i < 20 then decide (InPath q (148 : Vertex)) else decide (InPath q (149 : Vertex))))) else (if i < 25 then (if i < 23 then (if i < 22 then decide (InPath q (151 : Vertex)) else decide (InPath q (153 : Vertex))) else (if i < 24 then decide (InPath q (154 : Vertex)) else decide (InPath q (155 : Vertex)))) else (if i < 27 then (if i < 26 then decide (InPath q (157 : Vertex)) else decide (InPath q (159 : Vertex))) else (if i < 28 then decide (InPath q (192 : Vertex)) else decide (InPath q (193 : Vertex))))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then decide (InPath q (197 : Vertex)) else (if i < 31 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex)))) else (if i < 34 then (if i < 33 then decide (InPath q (201 : Vertex)) else decide (InPath q (205 : Vertex))) else (if i < 35 then decide (InPath q (207 : Vertex)) else decide (InPath q (209 : Vertex))))) else (if i < 39 then (if i < 37 then decide (InPath q (210 : Vertex)) else (if i < 38 then decide (InPath q (211 : Vertex)) else decide (InPath q (214 : Vertex)))) else (if i < 41 then (if i < 40 then decide (InPath q (218 : Vertex)) else decide (InPath q (220 : Vertex))) else (if i < 42 then decide (InPath q (221 : Vertex)) else decide (InPath q (222 : Vertex)))))) else (if i < 50 then (if i < 46 then (if i < 44 then decide (InPath q (258 : Vertex)) else (if i < 45 then decide (InPath q (259 : Vertex)) else decide (InPath q (260 : Vertex)))) else (if i < 48 then (if i < 47 then decide (InPath q (261 : Vertex)) else decide (InPath q (265 : Vertex))) else (if i < 49 then decide (InPath q (266 : Vertex)) else decide (InPath q (267 : Vertex))))) else (if i < 54 then (if i < 52 then (if i < 51 then decide (InPath q (268 : Vertex)) else decide (InPath q (270 : Vertex))) else (if i < 53 then decide (InPath q (272 : Vertex)) else decide (InPath q (276 : Vertex)))) else (if i < 56 then (if i < 55 then decide (InPath q (277 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 57 then decide (InPath q (280 : Vertex)) else decide (InPath q (281 : Vertex)))))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then decide (InPath q (282 : Vertex)) else (if i < 60 then decide (InPath q (283 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex))) else (if i < 64 then decide (InPath q (327 : Vertex)) else decide (InPath q (328 : Vertex))))) else (if i < 68 then (if i < 66 then decide (InPath q (329 : Vertex)) else (if i < 67 then decide (InPath q (333 : Vertex)) else decide (InPath q (335 : Vertex)))) else (if i < 70 then (if i < 69 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex))) else (if i < 71 then decide (InPath q (339 : Vertex)) else decide (InPath q (342 : Vertex)))))) else (if i < 79 then (if i < 75 then (if i < 73 then decide (InPath q (346 : Vertex)) else (if i < 74 then decide (InPath q (348 : Vertex)) else decide (InPath q (349 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (350 : Vertex)) else decide (InPath q (384 : Vertex))) else (if i < 78 then decide (InPath q (385 : Vertex)) else decide (InPath q (386 : Vertex))))) else (if i < 83 then (if i < 81 then (if i < 80 then decide (InPath q (387 : Vertex)) else decide (InPath q (389 : Vertex))) else (if i < 82 then decide (InPath q (391 : Vertex)) else decide (InPath q (393 : Vertex)))) else (if i < 85 then (if i < 84 then decide (InPath q (394 : Vertex)) else decide (InPath q (396 : Vertex))) else (if i < 86 then decide (InPath q (397 : Vertex)) else decide (InPath q (398 : Vertex))))))) else (if i < 101 then (if i < 94 then (if i < 90 then (if i < 88 then decide (InPath q (399 : Vertex)) else (if i < 89 then decide (InPath q (400 : Vertex)) else decide (InPath q (401 : Vertex)))) else (if i < 92 then (if i < 91 then decide (InPath q (402 : Vertex)) else decide (InPath q (403 : Vertex))) else (if i < 93 then decide (InPath q (406 : Vertex)) else decide (InPath q (408 : Vertex))))) else (if i < 97 then (if i < 95 then decide (InPath q (409 : Vertex)) else (if i < 96 then decide (InPath q (410 : Vertex)) else decide (InPath q (412 : Vertex)))) else (if i < 99 then (if i < 98 then decide (InPath q (413 : Vertex)) else decide (InPath q (414 : Vertex))) else (if i < 100 then decide (InPath q (450 : Vertex)) else decide (InPath q (451 : Vertex)))))) else (if i < 108 then (if i < 104 then (if i < 102 then decide (InPath q (452 : Vertex)) else (if i < 103 then decide (InPath q (453 : Vertex)) else decide (InPath q (457 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (458 : Vertex)) else decide (InPath q (459 : Vertex))) else (if i < 107 then decide (InPath q (460 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 112 then (if i < 110 then (if i < 109 then decide (InPath q (464 : Vertex)) else decide (InPath q (468 : Vertex))) else (if i < 111 then decide (InPath q (469 : Vertex)) else decide (InPath q (470 : Vertex)))) else (if i < 114 then (if i < 113 then decide (InPath q (471 : Vertex)) else decide (InPath q (472 : Vertex))) else (if i < 115 then decide (InPath q (473 : Vertex)) else decide (InPath q (475 : Vertex))))))))) else (if i < 174 then (if i < 145 then (if i < 130 then (if i < 123 then (if i < 119 then (if i < 117 then decide (InPath q (479 : Vertex)) else (if i < 118 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else decide (BallClauseLogic.Endpoint q (13 : Vertex)))) else (if i < 121 then (if i < 120 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else decide (BallClauseLogic.Endpoint q (24 : Vertex))) else (if i < 122 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex))))) else (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (76 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex)))))) else (if i < 137 then (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (140 : Vertex)))) else (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (144 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (149 : Vertex))))) else (if i < 141 then (if i < 139 then (if i < 138 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (153 : Vertex))) else (if i < 140 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else decide (BallClauseLogic.Endpoint q (155 : Vertex)))) else (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (157 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (193 : Vertex))))))) else (if i < 159 then (if i < 152 then (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (197 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (200 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else decide (BallClauseLogic.Endpoint q (209 : Vertex))))) else (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (210 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (220 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else decide (BallClauseLogic.Endpoint q (222 : Vertex)))))) else (if i < 166 then (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (265 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex))))) else (if i < 170 then (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (270 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else decide (BallClauseLogic.Endpoint q (279 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else decide (BallClauseLogic.Endpoint q (281 : Vertex)))))))) else (if i < 203 then (if i < 188 then (if i < 181 then (if i < 177 then (if i < 175 then decide (BallClauseLogic.Endpoint q (282 : Vertex)) else (if i < 176 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex)))) else (if i < 179 then (if i < 178 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else decide (BallClauseLogic.Endpoint q (321 : Vertex))) else (if i < 180 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (328 : Vertex))))) else (if i < 184 then (if i < 182 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else (if i < 183 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (335 : Vertex)))) else (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (338 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (339 : Vertex)) else decide (BallClauseLogic.Endpoint q (342 : Vertex)))))) else (if i < 195 then (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else decide (BallClauseLogic.Endpoint q (349 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (350 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (386 : Vertex))))) else (if i < 199 then (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (389 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (393 : Vertex)))) else (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (394 : Vertex)) else decide (BallClauseLogic.Endpoint q (396 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else decide (BallClauseLogic.Endpoint q (398 : Vertex))))))) else (if i < 218 then (if i < 210 then (if i < 206 then (if i < 204 then decide (BallClauseLogic.Endpoint q (399 : Vertex)) else (if i < 205 then decide (BallClauseLogic.Endpoint q (400 : Vertex)) else decide (BallClauseLogic.Endpoint q (401 : Vertex)))) else (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else decide (BallClauseLogic.Endpoint q (403 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (408 : Vertex))))) else (if i < 214 then (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (409 : Vertex)) else decide (BallClauseLogic.Endpoint q (410 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex)))) else (if i < 216 then (if i < 215 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else decide (BallClauseLogic.Endpoint q (450 : Vertex))) else (if i < 217 then decide (BallClauseLogic.Endpoint q (451 : Vertex)) else decide (BallClauseLogic.Endpoint q (452 : Vertex)))))) else (if i < 225 then (if i < 221 then (if i < 219 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else (if i < 220 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else decide (BallClauseLogic.Endpoint q (458 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (459 : Vertex)) else decide (BallClauseLogic.Endpoint q (460 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else decide (BallClauseLogic.Endpoint q (469 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (470 : Vertex)) else decide (BallClauseLogic.Endpoint q (471 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count233 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count235 (b : Nat → Bool) : Nat := countLit b [118, 119, 120]
def count237 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count241 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131]
def count255 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [132, 133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count267 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count277 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145]
def count281 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count305 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count307 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count333 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count337 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count343 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
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
def count459 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]
def count461 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count463 (b : Nat → Bool) : Nat := countLit b [3, 4, 6]
def count466 (b : Nat → Bool) : Nat := countLit b [7, 9]
def count468 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count470 (b : Nat → Bool) : Nat := countLit b [7, 9, 11, 12]
def count474 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11, 12]
def count481 (b : Nat → Bool) : Nat := countLit b [17, 18]
def count483 (b : Nat → Bool) : Nat := countLit b [13, 17, 18]
def count486 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count488 (b : Nat → Bool) : Nat := countLit b [23, 26]
def count490 (b : Nat → Bool) : Nat := countLit b [20, 22, 23, 26]
def count494 (b : Nat → Bool) : Nat := countLit b [13, 17, 18, 20, 22, 23, 26]
def count501 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11, 12, 13, 17, 18, 20, 22, 23, 26]
def count515 (b : Nat → Bool) : Nat := countLit b [29, 32]
def count517 (b : Nat → Bool) : Nat := countLit b [27, 29, 32]
def count520 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count522 (b : Nat → Bool) : Nat := countLit b [36, 41]
def count524 (b : Nat → Bool) : Nat := countLit b [34, 35, 36, 41]
def count528 (b : Nat → Bool) : Nat := countLit b [27, 29, 32, 34, 35, 36, 41]
def count535 (b : Nat → Bool) : Nat := countLit b [42, 43]
def count537 (b : Nat → Bool) : Nat := countLit b [45, 49]
def count539 (b : Nat → Bool) : Nat := countLit b [42, 43, 45, 49]
def count543 (b : Nat → Bool) : Nat := countLit b [51, 52]
def count545 (b : Nat → Bool) : Nat := countLit b [54, 57]
def count547 (b : Nat → Bool) : Nat := countLit b [51, 52, 54, 57]
def count551 (b : Nat → Bool) : Nat := countLit b [42, 43, 45, 49, 51, 52, 54, 57]
def count559 (b : Nat → Bool) : Nat := countLit b [27, 29, 32, 34, 35, 36, 41, 42, 43, 45, 49, 51, 52, 54, 57]
def count574 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11, 12, 13, 17, 18, 20, 22, 23, 26, 27, 29, 32, 34, 35, 36, 41, 42, 43, 45, 49, 51, 52, 54, 57]
def count603 (b : Nat → Bool) : Nat := countLit b [60, 61]
def count605 (b : Nat → Bool) : Nat := countLit b [58, 60, 61]
def count608 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count610 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count612 (b : Nat → Bool) : Nat := countLit b [65, 67, 68, 69]
def count616 (b : Nat → Bool) : Nat := countLit b [58, 60, 61, 65, 67, 68, 69]
def count623 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count625 (b : Nat → Bool) : Nat := countLit b [76, 79]
def count627 (b : Nat → Bool) : Nat := countLit b [74, 75, 76, 79]
def count631 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count633 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count635 (b : Nat → Bool) : Nat := countLit b [80, 82, 83, 84]
def count639 (b : Nat → Bool) : Nat := countLit b [74, 75, 76, 79, 80, 82, 83, 84]
def count647 (b : Nat → Bool) : Nat := countLit b [58, 60, 61, 65, 67, 68, 69, 74, 75, 76, 79, 80, 82, 83, 84]
def count662 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count664 (b : Nat → Bool) : Nat := countLit b [87, 89, 90]
def count667 (b : Nat → Bool) : Nat := countLit b [93, 97]
def count669 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count671 (b : Nat → Bool) : Nat := countLit b [93, 97, 98, 99]
def count675 (b : Nat → Bool) : Nat := countLit b [87, 89, 90, 93, 97, 98, 99]
def count682 (b : Nat → Bool) : Nat := countLit b [101, 105]
def count684 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count686 (b : Nat → Bool) : Nat := countLit b [101, 105, 107, 108]
def count690 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count692 (b : Nat → Bool) : Nat := countLit b [114, 116]
def count694 (b : Nat → Bool) : Nat := countLit b [110, 111, 114, 116]
def count698 (b : Nat → Bool) : Nat := countLit b [101, 105, 107, 108, 110, 111, 114, 116]
def count706 (b : Nat → Bool) : Nat := countLit b [87, 89, 90, 93, 97, 98, 99, 101, 105, 107, 108, 110, 111, 114, 116]
def count721 (b : Nat → Bool) : Nat := countLit b [58, 60, 61, 65, 67, 68, 69, 74, 75, 76, 79, 80, 82, 83, 84, 87, 89, 90, 93, 97, 98, 99, 101, 105, 107, 108, 110, 111, 114, 116]
def count751 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11, 12, 13, 17, 18, 20, 22, 23, 26, 27, 29, 32, 34, 35, 36, 41, 42, 43, 45, 49, 51, 52, 54, 57, 58, 60, 61, 65, 67, 68, 69, 74, 75, 76, 79, 80, 82, 83, 84, 87, 89, 90, 93, 97, 98, 99, 101, 105, 107, 108, 110, 111, 114, 116]
def count793 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count795 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6]
def count798 (b : Nat → Bool) : Nat := countLit b [-7, -9]
def count800 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count802 (b : Nat → Bool) : Nat := countLit b [-7, -9, -11, -12]
def count806 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11, -12]
def count813 (b : Nat → Bool) : Nat := countLit b [-17, -18]
def count815 (b : Nat → Bool) : Nat := countLit b [-13, -17, -18]
def count818 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count820 (b : Nat → Bool) : Nat := countLit b [-23, -26]
def count822 (b : Nat → Bool) : Nat := countLit b [-20, -22, -23, -26]
def count826 (b : Nat → Bool) : Nat := countLit b [-13, -17, -18, -20, -22, -23, -26]
def count833 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11, -12, -13, -17, -18, -20, -22, -23, -26]
def count847 (b : Nat → Bool) : Nat := countLit b [-29, -32]
def count849 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32]
def count852 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count854 (b : Nat → Bool) : Nat := countLit b [-36, -41]
def count856 (b : Nat → Bool) : Nat := countLit b [-34, -35, -36, -41]
def count860 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32, -34, -35, -36, -41]
def count867 (b : Nat → Bool) : Nat := countLit b [-42, -43]
def count869 (b : Nat → Bool) : Nat := countLit b [-45, -49]
def count871 (b : Nat → Bool) : Nat := countLit b [-42, -43, -45, -49]
def count875 (b : Nat → Bool) : Nat := countLit b [-51, -52]
def count877 (b : Nat → Bool) : Nat := countLit b [-54, -57]
def count879 (b : Nat → Bool) : Nat := countLit b [-51, -52, -54, -57]
def count883 (b : Nat → Bool) : Nat := countLit b [-42, -43, -45, -49, -51, -52, -54, -57]
def count891 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32, -34, -35, -36, -41, -42, -43, -45, -49, -51, -52, -54, -57]
def count906 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11, -12, -13, -17, -18, -20, -22, -23, -26, -27, -29, -32, -34, -35, -36, -41, -42, -43, -45, -49, -51, -52, -54, -57]
def count925 (b : Nat → Bool) : Nat := countLit b [-60, -61]
def count927 (b : Nat → Bool) : Nat := countLit b [-58, -60, -61]
def count930 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count932 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count934 (b : Nat → Bool) : Nat := countLit b [-65, -67, -68, -69]
def count938 (b : Nat → Bool) : Nat := countLit b [-58, -60, -61, -65, -67, -68, -69]
def count945 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count947 (b : Nat → Bool) : Nat := countLit b [-76, -79]
def count949 (b : Nat → Bool) : Nat := countLit b [-74, -75, -76, -79]
def count953 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count955 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count957 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83, -84]
def count961 (b : Nat → Bool) : Nat := countLit b [-74, -75, -76, -79, -80, -82, -83, -84]
def count969 (b : Nat → Bool) : Nat := countLit b [-58, -60, -61, -65, -67, -68, -69, -74, -75, -76, -79, -80, -82, -83, -84]
def count984 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count986 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90]
def count989 (b : Nat → Bool) : Nat := countLit b [-93, -97]
def count991 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count993 (b : Nat → Bool) : Nat := countLit b [-93, -97, -98, -99]
def count997 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90, -93, -97, -98, -99]
def count1004 (b : Nat → Bool) : Nat := countLit b [-101, -105]
def count1006 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1008 (b : Nat → Bool) : Nat := countLit b [-101, -105, -107, -108]
def count1012 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1014 (b : Nat → Bool) : Nat := countLit b [-114, -116]
def count1016 (b : Nat → Bool) : Nat := countLit b [-110, -111, -114, -116]
def count1020 (b : Nat → Bool) : Nat := countLit b [-101, -105, -107, -108, -110, -111, -114, -116]
def count1028 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90, -93, -97, -98, -99, -101, -105, -107, -108, -110, -111, -114, -116]
def count1043 (b : Nat → Bool) : Nat := countLit b [-58, -60, -61, -65, -67, -68, -69, -74, -75, -76, -79, -80, -82, -83, -84, -87, -89, -90, -93, -97, -98, -99, -101, -105, -107, -108, -110, -111, -114, -116]
def count1062 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11, -12, -13, -17, -18, -20, -22, -23, -26, -27, -29, -32, -34, -35, -36, -41, -42, -43, -45, -49, -51, -52, -54, -57, -58, -60, -61, -65, -67, -68, -69, -74, -75, -76, -79, -80, -82, -83, -84, -87, -89, -90, -93, -97, -98, -99, -101, -105, -107, -108, -110, -111, -114, -116]
def count1081 (b : Nat → Bool) : Nat := countLit b [2, 5]
def count1083 (b : Nat → Bool) : Nat := countLit b [1, 2, 5]
def count1086 (b : Nat → Bool) : Nat := countLit b [8, 10]
def count1088 (b : Nat → Bool) : Nat := countLit b [14, 15]
def count1090 (b : Nat → Bool) : Nat := countLit b [8, 10, 14, 15]
def count1094 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 14, 15]
def count1101 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count1103 (b : Nat → Bool) : Nat := countLit b [16, 19, 21]
def count1106 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count1108 (b : Nat → Bool) : Nat := countLit b [28, 30]
def count1110 (b : Nat → Bool) : Nat := countLit b [24, 25, 28, 30]
def count1114 (b : Nat → Bool) : Nat := countLit b [16, 19, 21, 24, 25, 28, 30]
def count1121 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 14, 15, 16, 19, 21, 24, 25, 28, 30]
def count1135 (b : Nat → Bool) : Nat := countLit b [33, 37]
def count1137 (b : Nat → Bool) : Nat := countLit b [31, 33, 37]
def count1140 (b : Nat → Bool) : Nat := countLit b [38, 39]
def count1142 (b : Nat → Bool) : Nat := countLit b [40, 44]
def count1144 (b : Nat → Bool) : Nat := countLit b [38, 39, 40, 44]
def count1148 (b : Nat → Bool) : Nat := countLit b [31, 33, 37, 38, 39, 40, 44]
def count1155 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count1157 (b : Nat → Bool) : Nat := countLit b [46, 47, 48]
def count1160 (b : Nat → Bool) : Nat := countLit b [50, 53]
def count1162 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count1164 (b : Nat → Bool) : Nat := countLit b [50, 53, 55, 56]
def count1168 (b : Nat → Bool) : Nat := countLit b [46, 47, 48, 50, 53, 55, 56]
def count1175 (b : Nat → Bool) : Nat := countLit b [31, 33, 37, 38, 39, 40, 44, 46, 47, 48, 50, 53, 55, 56]
def count1189 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 14, 15, 16, 19, 21, 24, 25, 28, 30, 31, 33, 37, 38, 39, 40, 44, 46, 47, 48, 50, 53, 55, 56]
def count1217 (b : Nat → Bool) : Nat := countLit b [62, 63]
def count1219 (b : Nat → Bool) : Nat := countLit b [59, 62, 63]
def count1222 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count1224 (b : Nat → Bool) : Nat := countLit b [70, 71]
def count1226 (b : Nat → Bool) : Nat := countLit b [64, 66, 70, 71]
def count1230 (b : Nat → Bool) : Nat := countLit b [59, 62, 63, 64, 66, 70, 71]
def count1237 (b : Nat → Bool) : Nat := countLit b [73, 77]
def count1239 (b : Nat → Bool) : Nat := countLit b [72, 73, 77]
def count1242 (b : Nat → Bool) : Nat := countLit b [78, 81]
def count1244 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count1246 (b : Nat → Bool) : Nat := countLit b [78, 81, 85, 86]
def count1250 (b : Nat → Bool) : Nat := countLit b [72, 73, 77, 78, 81, 85, 86]
def count1257 (b : Nat → Bool) : Nat := countLit b [59, 62, 63, 64, 66, 70, 71, 72, 73, 77, 78, 81, 85, 86]
def count1271 (b : Nat → Bool) : Nat := countLit b [91, 92]
def count1273 (b : Nat → Bool) : Nat := countLit b [88, 91, 92]
def count1276 (b : Nat → Bool) : Nat := countLit b [94, 95]
def count1278 (b : Nat → Bool) : Nat := countLit b [96, 100]
def count1280 (b : Nat → Bool) : Nat := countLit b [94, 95, 96, 100]
def count1284 (b : Nat → Bool) : Nat := countLit b [88, 91, 92, 94, 95, 96, 100]
def count1291 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count1293 (b : Nat → Bool) : Nat := countLit b [104, 106]
def count1295 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 106]
def count1299 (b : Nat → Bool) : Nat := countLit b [109, 112]
def count1301 (b : Nat → Bool) : Nat := countLit b [113, 115]
def count1303 (b : Nat → Bool) : Nat := countLit b [109, 112, 113, 115]
def count1307 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 106, 109, 112, 113, 115]
def count1315 (b : Nat → Bool) : Nat := countLit b [88, 91, 92, 94, 95, 96, 100, 102, 103, 104, 106, 109, 112, 113, 115]
def count1330 (b : Nat → Bool) : Nat := countLit b [59, 62, 63, 64, 66, 70, 71, 72, 73, 77, 78, 81, 85, 86, 88, 91, 92, 94, 95, 96, 100, 102, 103, 104, 106, 109, 112, 113, 115]
def count1359 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 14, 15, 16, 19, 21, 24, 25, 28, 30, 31, 33, 37, 38, 39, 40, 44, 46, 47, 48, 50, 53, 55, 56, 59, 62, 63, 64, 66, 70, 71, 72, 73, 77, 78, 81, 85, 86, 88, 91, 92, 94, 95, 96, 100, 102, 103, 104, 106, 109, 112, 113, 115]
def count1401 (b : Nat → Bool) : Nat := countLit b [-2, -5]
def count1403 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5]
def count1406 (b : Nat → Bool) : Nat := countLit b [-8, -10]
def count1408 (b : Nat → Bool) : Nat := countLit b [-14, -15]
def count1410 (b : Nat → Bool) : Nat := countLit b [-8, -10, -14, -15]
def count1414 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -14, -15]
def count1421 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count1423 (b : Nat → Bool) : Nat := countLit b [-16, -19, -21]
def count1426 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1428 (b : Nat → Bool) : Nat := countLit b [-28, -30]
def count1430 (b : Nat → Bool) : Nat := countLit b [-24, -25, -28, -30]
def count1434 (b : Nat → Bool) : Nat := countLit b [-16, -19, -21, -24, -25, -28, -30]
def count1441 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]
def count1455 (b : Nat → Bool) : Nat := countLit b [-33, -37]
def count1457 (b : Nat → Bool) : Nat := countLit b [-31, -33, -37]
def count1460 (b : Nat → Bool) : Nat := countLit b [-38, -39]
def count1462 (b : Nat → Bool) : Nat := countLit b [-40, -44]
def count1464 (b : Nat → Bool) : Nat := countLit b [-38, -39, -40, -44]
def count1468 (b : Nat → Bool) : Nat := countLit b [-31, -33, -37, -38, -39, -40, -44]
def count1475 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count1477 (b : Nat → Bool) : Nat := countLit b [-46, -47, -48]
def count1480 (b : Nat → Bool) : Nat := countLit b [-50, -53]
def count1482 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count1484 (b : Nat → Bool) : Nat := countLit b [-50, -53, -55, -56]
def count1488 (b : Nat → Bool) : Nat := countLit b [-46, -47, -48, -50, -53, -55, -56]
def count1495 (b : Nat → Bool) : Nat := countLit b [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]
def count1509 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]
def count1526 (b : Nat → Bool) : Nat := countLit b [-62, -63]
def count1528 (b : Nat → Bool) : Nat := countLit b [-59, -62, -63]
def count1531 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1533 (b : Nat → Bool) : Nat := countLit b [-70, -71]
def count1535 (b : Nat → Bool) : Nat := countLit b [-64, -66, -70, -71]
def count1539 (b : Nat → Bool) : Nat := countLit b [-59, -62, -63, -64, -66, -70, -71]
def count1546 (b : Nat → Bool) : Nat := countLit b [-73, -77]
def count1548 (b : Nat → Bool) : Nat := countLit b [-72, -73, -77]
def count1551 (b : Nat → Bool) : Nat := countLit b [-78, -81]
def count1553 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count1555 (b : Nat → Bool) : Nat := countLit b [-78, -81, -85, -86]
def count1559 (b : Nat → Bool) : Nat := countLit b [-72, -73, -77, -78, -81, -85, -86]
def count1566 (b : Nat → Bool) : Nat := countLit b [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86]
def count1580 (b : Nat → Bool) : Nat := countLit b [-91, -92]
def count1582 (b : Nat → Bool) : Nat := countLit b [-88, -91, -92]
def count1585 (b : Nat → Bool) : Nat := countLit b [-94, -95]
def count1587 (b : Nat → Bool) : Nat := countLit b [-96, -100]
def count1589 (b : Nat → Bool) : Nat := countLit b [-94, -95, -96, -100]
def count1593 (b : Nat → Bool) : Nat := countLit b [-88, -91, -92, -94, -95, -96, -100]
def count1600 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1602 (b : Nat → Bool) : Nat := countLit b [-104, -106]
def count1604 (b : Nat → Bool) : Nat := countLit b [-102, -103, -104, -106]
def count1608 (b : Nat → Bool) : Nat := countLit b [-109, -112]
def count1610 (b : Nat → Bool) : Nat := countLit b [-113, -115]
def count1612 (b : Nat → Bool) : Nat := countLit b [-109, -112, -113, -115]
def count1616 (b : Nat → Bool) : Nat := countLit b [-102, -103, -104, -106, -109, -112, -113, -115]
def count1624 (b : Nat → Bool) : Nat := countLit b [-88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]
def count1639 (b : Nat → Bool) : Nat := countLit b [-59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]
def count1656 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30, -31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59, -62, -63, -64, -66, -70, -71, -72, -73, -77, -78, -81, -85, -86, -88, -91, -92, -94, -95, -96, -100, -102, -103, -104, -106, -109, -112, -113, -115]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 836 then (if i < 418 then (if i < 209 then (if i < 104 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 19 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 17 then b 16 else (if i < 18 then b 17 else b 18))) else (if i < 22 then (if i < 20 then b 19 else (if i < 21 then b 20 else b 21)) else (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else b 25))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31))) else (if i < 35 then (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)) else (if i < 37 then (if i < 36 then b 35 else b 36) else (if i < 38 then b 37 else b 38)))) else (if i < 45 then (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44))) else (if i < 48 then (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)) else (if i < 50 then (if i < 49 then b 48 else b 49) else (if i < 51 then b 50 else b 51)))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then b 52 else (if i < 54 then b 53 else b 54)) else (if i < 56 then b 55 else (if i < 57 then b 56 else b 57))) else (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else b 64)))) else (if i < 71 then (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 69 then b 68 else (if i < 70 then b 69 else b 70))) else (if i < 74 then (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)) else (if i < 76 then (if i < 75 then b 74 else b 75) else (if i < 77 then b 76 else b 77))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90)))) else (if i < 97 then (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 95 then b 94 else (if i < 96 then b 95 else b 96))) else (if i < 100 then (if i < 98 then b 97 else (if i < 99 then b 98 else b 99)) else (if i < 102 then (if i < 101 then b 100 else b 101) else (if i < 103 then b 102 else b 103))))))) else (if i < 156 then (if i < 130 then (if i < 117 then (if i < 110 then (if i < 107 then (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)) else (if i < 108 then b 107 else (if i < 109 then b 108 else b 109))) else (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 115 then (if i < 114 then b 113 else b 114) else (if i < 116 then b 115 else b 116)))) else (if i < 123 then (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122))) else (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else b 129))))) else (if i < 143 then (if i < 136 then (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 134 then b 133 else (if i < 135 then b 134 else b 135))) else (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 141 then (if i < 140 then b 139 else b 140) else (if i < 142 then b 141 else b 142)))) else (if i < 149 then (if i < 146 then (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)) else (if i < 147 then b 146 else (if i < 148 then b 147 else b 148))) else (if i < 152 then (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)) else (if i < 154 then (if i < 153 then b 152 else b 153) else (if i < 155 then b 154 else b 155)))))) else (if i < 182 then (if i < 169 then (if i < 162 then (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 167 then (if i < 166 then b 165 else b 166) else (if i < 168 then b 167 else b 168)))) else (if i < 175 then (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174))) else (if i < 178 then (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)) else (if i < 180 then (if i < 179 then b 178 else b 179) else (if i < 181 then b 180 else b 181))))) else (if i < 195 then (if i < 188 then (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187))) else (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else b 194)))) else (if i < 202 then (if i < 198 then (if i < 196 then b 195 else (if i < 197 then b 196 else b 197)) else (if i < 200 then (if i < 199 then b 198 else b 199) else (if i < 201 then b 200 else b 201))) else (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 207 then (if i < 206 then b 205 else b 206) else (if i < 208 then b 207 else b 208)))))))) else (if i < 313 then (if i < 261 then (if i < 235 then (if i < 222 then (if i < 215 then (if i < 212 then (if i < 210 then b 209 else (if i < 211 then b 210 else b 211)) else (if i < 213 then b 212 else (if i < 214 then b 213 else b 214))) else (if i < 218 then (if i < 216 then b 215 else (if i < 217 then b 216 else b 217)) else (if i < 220 then (if i < 219 then b 218 else b 219) else (if i < 221 then b 220 else b 221)))) else (if i < 228 then (if i < 225 then (if i < 223 then b 222 else (if i < 224 then b 223 else b 224)) else (if i < 226 then b 225 else (if i < 227 then b 226 else b 227))) else (if i < 231 then (if i < 229 then b 228 else (if i < 230 then b 229 else b 230)) else (if i < 233 then (if i < 232 then b 231 else b 232) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))))) else (if i < 248 then (if i < 241 then (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))) else (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 246 then (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))))) else (if i < 254 then (if i < 251 then (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 252 then decide (1 ≤ count251 b) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)))) else (if i < 257 then (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b))) else (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))))))) else (if i < 287 then (if i < 274 then (if i < 267 then (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))) else (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 272 then (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))))) else (if i < 280 then (if i < 277 then (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))) else (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)))) else (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))))) else (if i < 300 then (if i < 293 then (if i < 290 then (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))) else (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))) else (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 298 then (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))))) else (if i < 306 then (if i < 303 then (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b))) else (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))) else (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))))))) else (if i < 365 then (if i < 339 then (if i < 326 then (if i < 319 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))) else (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 324 then (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))))) else (if i < 332 then (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 335 then (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))))) else (if i < 352 then (if i < 345 then (if i < 342 then (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))) else (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)))) else (if i < 348 then (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))) else (if i < 350 then (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b))))) else (if i < 358 then (if i < 355 then (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b))) else (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b)))) else (if i < 361 then (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))) else (if i < 363 then (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b))))))) else (if i < 391 then (if i < 378 then (if i < 371 then (if i < 368 then (if i < 366 then decide (1 ≤ count365 b) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))) else (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 376 then (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))))) else (if i < 384 then (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)))) else (if i < 387 then (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b))) else (if i < 389 then (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))))) else (if i < 404 then (if i < 397 then (if i < 394 then (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)))) else (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))))) else (if i < 411 then (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)))) else (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 416 then (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)))))))))) else (if i < 627 then (if i < 522 then (if i < 470 then (if i < 444 then (if i < 431 then (if i < 424 then (if i < 421 then (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))) else (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)))) else (if i < 427 then (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b))) else (if i < 429 then (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))))) else (if i < 437 then (if i < 434 then (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))) else (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))) else (if i < 440 then (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))) else (if i < 442 then (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)))))) else (if i < 457 then (if i < 450 then (if i < 447 then (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b))) else (if i < 448 then decide (1 ≤ count447 b) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b)))) else (if i < 453 then (if i < 451 then decide (2 ≤ count449 b) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))) else (if i < 455 then (if i < 454 then decide (1 ≤ count453 b) else decide (2 ≤ count453 b)) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))))) else (if i < 463 then (if i < 460 then (if i < 458 then decide (1 ≤ count457 b) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b))) else (if i < 461 then decide (2 ≤ count459 b) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)))) else (if i < 466 then (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (3 ≤ count463 b))) else (if i < 468 then (if i < 467 then decide (1 ≤ count466 b) else decide (2 ≤ count466 b)) else (if i < 469 then decide (1 ≤ count468 b) else decide (2 ≤ count468 b))))))) else (if i < 496 then (if i < 483 then (if i < 476 then (if i < 473 then (if i < 471 then decide (1 ≤ count470 b) else (if i < 472 then decide (2 ≤ count470 b) else decide (3 ≤ count470 b))) else (if i < 474 then decide (4 ≤ count470 b) else (if i < 475 then decide (1 ≤ count474 b) else decide (2 ≤ count474 b)))) else (if i < 479 then (if i < 477 then decide (3 ≤ count474 b) else (if i < 478 then decide (4 ≤ count474 b) else decide (5 ≤ count474 b))) else (if i < 481 then (if i < 480 then decide (6 ≤ count474 b) else decide (7 ≤ count474 b)) else (if i < 482 then decide (1 ≤ count481 b) else decide (2 ≤ count481 b))))) else (if i < 489 then (if i < 486 then (if i < 484 then decide (1 ≤ count483 b) else (if i < 485 then decide (2 ≤ count483 b) else decide (3 ≤ count483 b))) else (if i < 487 then decide (1 ≤ count486 b) else (if i < 488 then decide (2 ≤ count486 b) else decide (1 ≤ count488 b)))) else (if i < 492 then (if i < 490 then decide (2 ≤ count488 b) else (if i < 491 then decide (1 ≤ count490 b) else decide (2 ≤ count490 b))) else (if i < 494 then (if i < 493 then decide (3 ≤ count490 b) else decide (4 ≤ count490 b)) else (if i < 495 then decide (1 ≤ count494 b) else decide (2 ≤ count494 b)))))) else (if i < 509 then (if i < 502 then (if i < 499 then (if i < 497 then decide (3 ≤ count494 b) else (if i < 498 then decide (4 ≤ count494 b) else decide (5 ≤ count494 b))) else (if i < 500 then decide (6 ≤ count494 b) else (if i < 501 then decide (7 ≤ count494 b) else decide (1 ≤ count501 b)))) else (if i < 505 then (if i < 503 then decide (2 ≤ count501 b) else (if i < 504 then decide (3 ≤ count501 b) else decide (4 ≤ count501 b))) else (if i < 507 then (if i < 506 then decide (5 ≤ count501 b) else decide (6 ≤ count501 b)) else (if i < 508 then decide (7 ≤ count501 b) else decide (8 ≤ count501 b))))) else (if i < 515 then (if i < 512 then (if i < 510 then decide (9 ≤ count501 b) else (if i < 511 then decide (10 ≤ count501 b) else decide (11 ≤ count501 b))) else (if i < 513 then decide (12 ≤ count501 b) else (if i < 514 then decide (13 ≤ count501 b) else decide (14 ≤ count501 b)))) else (if i < 518 then (if i < 516 then decide (1 ≤ count515 b) else (if i < 517 then decide (2 ≤ count515 b) else decide (1 ≤ count517 b))) else (if i < 520 then (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b)) else (if i < 521 then decide (1 ≤ count520 b) else decide (2 ≤ count520 b)))))))) else (if i < 574 then (if i < 548 then (if i < 535 then (if i < 528 then (if i < 525 then (if i < 523 then decide (1 ≤ count522 b) else (if i < 524 then decide (2 ≤ count522 b) else decide (1 ≤ count524 b))) else (if i < 526 then decide (2 ≤ count524 b) else (if i < 527 then decide (3 ≤ count524 b) else decide (4 ≤ count524 b)))) else (if i < 531 then (if i < 529 then decide (1 ≤ count528 b) else (if i < 530 then decide (2 ≤ count528 b) else decide (3 ≤ count528 b))) else (if i < 533 then (if i < 532 then decide (4 ≤ count528 b) else decide (5 ≤ count528 b)) else (if i < 534 then decide (6 ≤ count528 b) else decide (7 ≤ count528 b))))) else (if i < 541 then (if i < 538 then (if i < 536 then decide (1 ≤ count535 b) else (if i < 537 then decide (2 ≤ count535 b) else decide (1 ≤ count537 b))) else (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (1 ≤ count539 b) else decide (2 ≤ count539 b)))) else (if i < 544 then (if i < 542 then decide (3 ≤ count539 b) else (if i < 543 then decide (4 ≤ count539 b) else decide (1 ≤ count543 b))) else (if i < 546 then (if i < 545 then decide (2 ≤ count543 b) else decide (1 ≤ count545 b)) else (if i < 547 then decide (2 ≤ count545 b) else decide (1 ≤ count547 b)))))) else (if i < 561 then (if i < 554 then (if i < 551 then (if i < 549 then decide (2 ≤ count547 b) else (if i < 550 then decide (3 ≤ count547 b) else decide (4 ≤ count547 b))) else (if i < 552 then decide (1 ≤ count551 b) else (if i < 553 then decide (2 ≤ count551 b) else decide (3 ≤ count551 b)))) else (if i < 557 then (if i < 555 then decide (4 ≤ count551 b) else (if i < 556 then decide (5 ≤ count551 b) else decide (6 ≤ count551 b))) else (if i < 559 then (if i < 558 then decide (7 ≤ count551 b) else decide (8 ≤ count551 b)) else (if i < 560 then decide (1 ≤ count559 b) else decide (2 ≤ count559 b))))) else (if i < 567 then (if i < 564 then (if i < 562 then decide (3 ≤ count559 b) else (if i < 563 then decide (4 ≤ count559 b) else decide (5 ≤ count559 b))) else (if i < 565 then decide (6 ≤ count559 b) else (if i < 566 then decide (7 ≤ count559 b) else decide (8 ≤ count559 b)))) else (if i < 570 then (if i < 568 then decide (9 ≤ count559 b) else (if i < 569 then decide (10 ≤ count559 b) else decide (11 ≤ count559 b))) else (if i < 572 then (if i < 571 then decide (12 ≤ count559 b) else decide (13 ≤ count559 b)) else (if i < 573 then decide (14 ≤ count559 b) else decide (15 ≤ count559 b))))))) else (if i < 600 then (if i < 587 then (if i < 580 then (if i < 577 then (if i < 575 then decide (1 ≤ count574 b) else (if i < 576 then decide (2 ≤ count574 b) else decide (3 ≤ count574 b))) else (if i < 578 then decide (4 ≤ count574 b) else (if i < 579 then decide (5 ≤ count574 b) else decide (6 ≤ count574 b)))) else (if i < 583 then (if i < 581 then decide (7 ≤ count574 b) else (if i < 582 then decide (8 ≤ count574 b) else decide (9 ≤ count574 b))) else (if i < 585 then (if i < 584 then decide (10 ≤ count574 b) else decide (11 ≤ count574 b)) else (if i < 586 then decide (12 ≤ count574 b) else decide (13 ≤ count574 b))))) else (if i < 593 then (if i < 590 then (if i < 588 then decide (14 ≤ count574 b) else (if i < 589 then decide (15 ≤ count574 b) else decide (16 ≤ count574 b))) else (if i < 591 then decide (17 ≤ count574 b) else (if i < 592 then decide (18 ≤ count574 b) else decide (19 ≤ count574 b)))) else (if i < 596 then (if i < 594 then decide (20 ≤ count574 b) else (if i < 595 then decide (21 ≤ count574 b) else decide (22 ≤ count574 b))) else (if i < 598 then (if i < 597 then decide (23 ≤ count574 b) else decide (24 ≤ count574 b)) else (if i < 599 then decide (25 ≤ count574 b) else decide (26 ≤ count574 b)))))) else (if i < 613 then (if i < 606 then (if i < 603 then (if i < 601 then decide (27 ≤ count574 b) else (if i < 602 then decide (28 ≤ count574 b) else decide (29 ≤ count574 b))) else (if i < 604 then decide (1 ≤ count603 b) else (if i < 605 then decide (2 ≤ count603 b) else decide (1 ≤ count605 b)))) else (if i < 609 then (if i < 607 then decide (2 ≤ count605 b) else (if i < 608 then decide (3 ≤ count605 b) else decide (1 ≤ count608 b))) else (if i < 611 then (if i < 610 then decide (2 ≤ count608 b) else decide (1 ≤ count610 b)) else (if i < 612 then decide (2 ≤ count610 b) else decide (1 ≤ count612 b))))) else (if i < 620 then (if i < 616 then (if i < 614 then decide (2 ≤ count612 b) else (if i < 615 then decide (3 ≤ count612 b) else decide (4 ≤ count612 b))) else (if i < 618 then (if i < 617 then decide (1 ≤ count616 b) else decide (2 ≤ count616 b)) else (if i < 619 then decide (3 ≤ count616 b) else decide (4 ≤ count616 b)))) else (if i < 623 then (if i < 621 then decide (5 ≤ count616 b) else (if i < 622 then decide (6 ≤ count616 b) else decide (7 ≤ count616 b))) else (if i < 625 then (if i < 624 then decide (1 ≤ count623 b) else decide (2 ≤ count623 b)) else (if i < 626 then decide (1 ≤ count625 b) else decide (2 ≤ count625 b))))))))) else (if i < 731 then (if i < 679 then (if i < 653 then (if i < 640 then (if i < 633 then (if i < 630 then (if i < 628 then decide (1 ≤ count627 b) else (if i < 629 then decide (2 ≤ count627 b) else decide (3 ≤ count627 b))) else (if i < 631 then decide (4 ≤ count627 b) else (if i < 632 then decide (1 ≤ count631 b) else decide (2 ≤ count631 b)))) else (if i < 636 then (if i < 634 then decide (1 ≤ count633 b) else (if i < 635 then decide (2 ≤ count633 b) else decide (1 ≤ count635 b))) else (if i < 638 then (if i < 637 then decide (2 ≤ count635 b) else decide (3 ≤ count635 b)) else (if i < 639 then decide (4 ≤ count635 b) else decide (1 ≤ count639 b))))) else (if i < 646 then (if i < 643 then (if i < 641 then decide (2 ≤ count639 b) else (if i < 642 then decide (3 ≤ count639 b) else decide (4 ≤ count639 b))) else (if i < 644 then decide (5 ≤ count639 b) else (if i < 645 then decide (6 ≤ count639 b) else decide (7 ≤ count639 b)))) else (if i < 649 then (if i < 647 then decide (8 ≤ count639 b) else (if i < 648 then decide (1 ≤ count647 b) else decide (2 ≤ count647 b))) else (if i < 651 then (if i < 650 then decide (3 ≤ count647 b) else decide (4 ≤ count647 b)) else (if i < 652 then decide (5 ≤ count647 b) else decide (6 ≤ count647 b)))))) else (if i < 666 then (if i < 659 then (if i < 656 then (if i < 654 then decide (7 ≤ count647 b) else (if i < 655 then decide (8 ≤ count647 b) else decide (9 ≤ count647 b))) else (if i < 657 then decide (10 ≤ count647 b) else (if i < 658 then decide (11 ≤ count647 b) else decide (12 ≤ count647 b)))) else (if i < 662 then (if i < 660 then decide (13 ≤ count647 b) else (if i < 661 then decide (14 ≤ count647 b) else decide (15 ≤ count647 b))) else (if i < 664 then (if i < 663 then decide (1 ≤ count662 b) else decide (2 ≤ count662 b)) else (if i < 665 then decide (1 ≤ count664 b) else decide (2 ≤ count664 b))))) else (if i < 672 then (if i < 669 then (if i < 667 then decide (3 ≤ count664 b) else (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b))) else (if i < 670 then decide (1 ≤ count669 b) else (if i < 671 then decide (2 ≤ count669 b) else decide (1 ≤ count671 b)))) else (if i < 675 then (if i < 673 then decide (2 ≤ count671 b) else (if i < 674 then decide (3 ≤ count671 b) else decide (4 ≤ count671 b))) else (if i < 677 then (if i < 676 then decide (1 ≤ count675 b) else decide (2 ≤ count675 b)) else (if i < 678 then decide (3 ≤ count675 b) else decide (4 ≤ count675 b))))))) else (if i < 705 then (if i < 692 then (if i < 685 then (if i < 682 then (if i < 680 then decide (5 ≤ count675 b) else (if i < 681 then decide (6 ≤ count675 b) else decide (7 ≤ count675 b))) else (if i < 683 then decide (1 ≤ count682 b) else (if i < 684 then decide (2 ≤ count682 b) else decide (1 ≤ count684 b)))) else (if i < 688 then (if i < 686 then decide (2 ≤ count684 b) else (if i < 687 then decide (1 ≤ count686 b) else decide (2 ≤ count686 b))) else (if i < 690 then (if i < 689 then decide (3 ≤ count686 b) else decide (4 ≤ count686 b)) else (if i < 691 then decide (1 ≤ count690 b) else decide (2 ≤ count690 b))))) else (if i < 698 then (if i < 695 then (if i < 693 then decide (1 ≤ count692 b) else (if i < 694 then decide (2 ≤ count692 b) else decide (1 ≤ count694 b))) else (if i < 696 then decide (2 ≤ count694 b) else (if i < 697 then decide (3 ≤ count694 b) else decide (4 ≤ count694 b)))) else (if i < 701 then (if i < 699 then decide (1 ≤ count698 b) else (if i < 700 then decide (2 ≤ count698 b) else decide (3 ≤ count698 b))) else (if i < 703 then (if i < 702 then decide (4 ≤ count698 b) else decide (5 ≤ count698 b)) else (if i < 704 then decide (6 ≤ count698 b) else decide (7 ≤ count698 b)))))) else (if i < 718 then (if i < 711 then (if i < 708 then (if i < 706 then decide (8 ≤ count698 b) else (if i < 707 then decide (1 ≤ count706 b) else decide (2 ≤ count706 b))) else (if i < 709 then decide (3 ≤ count706 b) else (if i < 710 then decide (4 ≤ count706 b) else decide (5 ≤ count706 b)))) else (if i < 714 then (if i < 712 then decide (6 ≤ count706 b) else (if i < 713 then decide (7 ≤ count706 b) else decide (8 ≤ count706 b))) else (if i < 716 then (if i < 715 then decide (9 ≤ count706 b) else decide (10 ≤ count706 b)) else (if i < 717 then decide (11 ≤ count706 b) else decide (12 ≤ count706 b))))) else (if i < 724 then (if i < 721 then (if i < 719 then decide (13 ≤ count706 b) else (if i < 720 then decide (14 ≤ count706 b) else decide (15 ≤ count706 b))) else (if i < 722 then decide (1 ≤ count721 b) else (if i < 723 then decide (2 ≤ count721 b) else decide (3 ≤ count721 b)))) else (if i < 727 then (if i < 725 then decide (4 ≤ count721 b) else (if i < 726 then decide (5 ≤ count721 b) else decide (6 ≤ count721 b))) else (if i < 729 then (if i < 728 then decide (7 ≤ count721 b) else decide (8 ≤ count721 b)) else (if i < 730 then decide (9 ≤ count721 b) else decide (10 ≤ count721 b)))))))) else (if i < 783 then (if i < 757 then (if i < 744 then (if i < 737 then (if i < 734 then (if i < 732 then decide (11 ≤ count721 b) else (if i < 733 then decide (12 ≤ count721 b) else decide (13 ≤ count721 b))) else (if i < 735 then decide (14 ≤ count721 b) else (if i < 736 then decide (15 ≤ count721 b) else decide (16 ≤ count721 b)))) else (if i < 740 then (if i < 738 then decide (17 ≤ count721 b) else (if i < 739 then decide (18 ≤ count721 b) else decide (19 ≤ count721 b))) else (if i < 742 then (if i < 741 then decide (20 ≤ count721 b) else decide (21 ≤ count721 b)) else (if i < 743 then decide (22 ≤ count721 b) else decide (23 ≤ count721 b))))) else (if i < 750 then (if i < 747 then (if i < 745 then decide (24 ≤ count721 b) else (if i < 746 then decide (25 ≤ count721 b) else decide (26 ≤ count721 b))) else (if i < 748 then decide (27 ≤ count721 b) else (if i < 749 then decide (28 ≤ count721 b) else decide (29 ≤ count721 b)))) else (if i < 753 then (if i < 751 then decide (30 ≤ count721 b) else (if i < 752 then decide (1 ≤ count751 b) else decide (2 ≤ count751 b))) else (if i < 755 then (if i < 754 then decide (3 ≤ count751 b) else decide (4 ≤ count751 b)) else (if i < 756 then decide (5 ≤ count751 b) else decide (6 ≤ count751 b)))))) else (if i < 770 then (if i < 763 then (if i < 760 then (if i < 758 then decide (7 ≤ count751 b) else (if i < 759 then decide (8 ≤ count751 b) else decide (9 ≤ count751 b))) else (if i < 761 then decide (10 ≤ count751 b) else (if i < 762 then decide (11 ≤ count751 b) else decide (12 ≤ count751 b)))) else (if i < 766 then (if i < 764 then decide (13 ≤ count751 b) else (if i < 765 then decide (14 ≤ count751 b) else decide (15 ≤ count751 b))) else (if i < 768 then (if i < 767 then decide (16 ≤ count751 b) else decide (17 ≤ count751 b)) else (if i < 769 then decide (18 ≤ count751 b) else decide (19 ≤ count751 b))))) else (if i < 776 then (if i < 773 then (if i < 771 then decide (20 ≤ count751 b) else (if i < 772 then decide (21 ≤ count751 b) else decide (22 ≤ count751 b))) else (if i < 774 then decide (23 ≤ count751 b) else (if i < 775 then decide (24 ≤ count751 b) else decide (25 ≤ count751 b)))) else (if i < 779 then (if i < 777 then decide (26 ≤ count751 b) else (if i < 778 then decide (27 ≤ count751 b) else decide (28 ≤ count751 b))) else (if i < 781 then (if i < 780 then decide (29 ≤ count751 b) else decide (30 ≤ count751 b)) else (if i < 782 then decide (31 ≤ count751 b) else decide (32 ≤ count751 b))))))) else (if i < 809 then (if i < 796 then (if i < 789 then (if i < 786 then (if i < 784 then decide (33 ≤ count751 b) else (if i < 785 then decide (34 ≤ count751 b) else decide (35 ≤ count751 b))) else (if i < 787 then decide (36 ≤ count751 b) else (if i < 788 then decide (37 ≤ count751 b) else decide (38 ≤ count751 b)))) else (if i < 792 then (if i < 790 then decide (39 ≤ count751 b) else (if i < 791 then decide (40 ≤ count751 b) else decide (41 ≤ count751 b))) else (if i < 794 then (if i < 793 then decide (42 ≤ count751 b) else decide (1 ≤ count793 b)) else (if i < 795 then decide (2 ≤ count793 b) else decide (1 ≤ count795 b))))) else (if i < 802 then (if i < 799 then (if i < 797 then decide (2 ≤ count795 b) else (if i < 798 then decide (3 ≤ count795 b) else decide (1 ≤ count798 b))) else (if i < 800 then decide (2 ≤ count798 b) else (if i < 801 then decide (1 ≤ count800 b) else decide (2 ≤ count800 b)))) else (if i < 805 then (if i < 803 then decide (1 ≤ count802 b) else (if i < 804 then decide (2 ≤ count802 b) else decide (3 ≤ count802 b))) else (if i < 807 then (if i < 806 then decide (4 ≤ count802 b) else decide (1 ≤ count806 b)) else (if i < 808 then decide (2 ≤ count806 b) else decide (3 ≤ count806 b)))))) else (if i < 822 then (if i < 815 then (if i < 812 then (if i < 810 then decide (4 ≤ count806 b) else (if i < 811 then decide (5 ≤ count806 b) else decide (6 ≤ count806 b))) else (if i < 813 then decide (7 ≤ count806 b) else (if i < 814 then decide (1 ≤ count813 b) else decide (2 ≤ count813 b)))) else (if i < 818 then (if i < 816 then decide (1 ≤ count815 b) else (if i < 817 then decide (2 ≤ count815 b) else decide (3 ≤ count815 b))) else (if i < 820 then (if i < 819 then decide (1 ≤ count818 b) else decide (2 ≤ count818 b)) else (if i < 821 then decide (1 ≤ count820 b) else decide (2 ≤ count820 b))))) else (if i < 829 then (if i < 825 then (if i < 823 then decide (1 ≤ count822 b) else (if i < 824 then decide (2 ≤ count822 b) else decide (3 ≤ count822 b))) else (if i < 827 then (if i < 826 then decide (4 ≤ count822 b) else decide (1 ≤ count826 b)) else (if i < 828 then decide (2 ≤ count826 b) else decide (3 ≤ count826 b)))) else (if i < 832 then (if i < 830 then decide (4 ≤ count826 b) else (if i < 831 then decide (5 ≤ count826 b) else decide (6 ≤ count826 b))) else (if i < 834 then (if i < 833 then decide (7 ≤ count826 b) else decide (1 ≤ count833 b)) else (if i < 835 then decide (2 ≤ count833 b) else decide (3 ≤ count833 b))))))))))) else (if i < 1254 then (if i < 1045 then (if i < 940 then (if i < 888 then (if i < 862 then (if i < 849 then (if i < 842 then (if i < 839 then (if i < 837 then decide (4 ≤ count833 b) else (if i < 838 then decide (5 ≤ count833 b) else decide (6 ≤ count833 b))) else (if i < 840 then decide (7 ≤ count833 b) else (if i < 841 then decide (8 ≤ count833 b) else decide (9 ≤ count833 b)))) else (if i < 845 then (if i < 843 then decide (10 ≤ count833 b) else (if i < 844 then decide (11 ≤ count833 b) else decide (12 ≤ count833 b))) else (if i < 847 then (if i < 846 then decide (13 ≤ count833 b) else decide (14 ≤ count833 b)) else (if i < 848 then decide (1 ≤ count847 b) else decide (2 ≤ count847 b))))) else (if i < 855 then (if i < 852 then (if i < 850 then decide (1 ≤ count849 b) else (if i < 851 then decide (2 ≤ count849 b) else decide (3 ≤ count849 b))) else (if i < 853 then decide (1 ≤ count852 b) else (if i < 854 then decide (2 ≤ count852 b) else decide (1 ≤ count854 b)))) else (if i < 858 then (if i < 856 then decide (2 ≤ count854 b) else (if i < 857 then decide (1 ≤ count856 b) else decide (2 ≤ count856 b))) else (if i < 860 then (if i < 859 then decide (3 ≤ count856 b) else decide (4 ≤ count856 b)) else (if i < 861 then decide (1 ≤ count860 b) else decide (2 ≤ count860 b)))))) else (if i < 875 then (if i < 868 then (if i < 865 then (if i < 863 then decide (3 ≤ count860 b) else (if i < 864 then decide (4 ≤ count860 b) else decide (5 ≤ count860 b))) else (if i < 866 then decide (6 ≤ count860 b) else (if i < 867 then decide (7 ≤ count860 b) else decide (1 ≤ count867 b)))) else (if i < 871 then (if i < 869 then decide (2 ≤ count867 b) else (if i < 870 then decide (1 ≤ count869 b) else decide (2 ≤ count869 b))) else (if i < 873 then (if i < 872 then decide (1 ≤ count871 b) else decide (2 ≤ count871 b)) else (if i < 874 then decide (3 ≤ count871 b) else decide (4 ≤ count871 b))))) else (if i < 881 then (if i < 878 then (if i < 876 then decide (1 ≤ count875 b) else (if i < 877 then decide (2 ≤ count875 b) else decide (1 ≤ count877 b))) else (if i < 879 then decide (2 ≤ count877 b) else (if i < 880 then decide (1 ≤ count879 b) else decide (2 ≤ count879 b)))) else (if i < 884 then (if i < 882 then decide (3 ≤ count879 b) else (if i < 883 then decide (4 ≤ count879 b) else decide (1 ≤ count883 b))) else (if i < 886 then (if i < 885 then decide (2 ≤ count883 b) else decide (3 ≤ count883 b)) else (if i < 887 then decide (4 ≤ count883 b) else decide (5 ≤ count883 b))))))) else (if i < 914 then (if i < 901 then (if i < 894 then (if i < 891 then (if i < 889 then decide (6 ≤ count883 b) else (if i < 890 then decide (7 ≤ count883 b) else decide (8 ≤ count883 b))) else (if i < 892 then decide (1 ≤ count891 b) else (if i < 893 then decide (2 ≤ count891 b) else decide (3 ≤ count891 b)))) else (if i < 897 then (if i < 895 then decide (4 ≤ count891 b) else (if i < 896 then decide (5 ≤ count891 b) else decide (6 ≤ count891 b))) else (if i < 899 then (if i < 898 then decide (7 ≤ count891 b) else decide (8 ≤ count891 b)) else (if i < 900 then decide (9 ≤ count891 b) else decide (10 ≤ count891 b))))) else (if i < 907 then (if i < 904 then (if i < 902 then decide (11 ≤ count891 b) else (if i < 903 then decide (12 ≤ count891 b) else decide (13 ≤ count891 b))) else (if i < 905 then decide (14 ≤ count891 b) else (if i < 906 then decide (15 ≤ count891 b) else decide (1 ≤ count906 b)))) else (if i < 910 then (if i < 908 then decide (2 ≤ count906 b) else (if i < 909 then decide (3 ≤ count906 b) else decide (4 ≤ count906 b))) else (if i < 912 then (if i < 911 then decide (5 ≤ count906 b) else decide (6 ≤ count906 b)) else (if i < 913 then decide (7 ≤ count906 b) else decide (8 ≤ count906 b)))))) else (if i < 927 then (if i < 920 then (if i < 917 then (if i < 915 then decide (9 ≤ count906 b) else (if i < 916 then decide (10 ≤ count906 b) else decide (11 ≤ count906 b))) else (if i < 918 then decide (12 ≤ count906 b) else (if i < 919 then decide (13 ≤ count906 b) else decide (14 ≤ count906 b)))) else (if i < 923 then (if i < 921 then decide (15 ≤ count906 b) else (if i < 922 then decide (16 ≤ count906 b) else decide (17 ≤ count906 b))) else (if i < 925 then (if i < 924 then decide (18 ≤ count906 b) else decide (19 ≤ count906 b)) else (if i < 926 then decide (1 ≤ count925 b) else decide (2 ≤ count925 b))))) else (if i < 933 then (if i < 930 then (if i < 928 then decide (1 ≤ count927 b) else (if i < 929 then decide (2 ≤ count927 b) else decide (3 ≤ count927 b))) else (if i < 931 then decide (1 ≤ count930 b) else (if i < 932 then decide (2 ≤ count930 b) else decide (1 ≤ count932 b)))) else (if i < 936 then (if i < 934 then decide (2 ≤ count932 b) else (if i < 935 then decide (1 ≤ count934 b) else decide (2 ≤ count934 b))) else (if i < 938 then (if i < 937 then decide (3 ≤ count934 b) else decide (4 ≤ count934 b)) else (if i < 939 then decide (1 ≤ count938 b) else decide (2 ≤ count938 b)))))))) else (if i < 992 then (if i < 966 then (if i < 953 then (if i < 946 then (if i < 943 then (if i < 941 then decide (3 ≤ count938 b) else (if i < 942 then decide (4 ≤ count938 b) else decide (5 ≤ count938 b))) else (if i < 944 then decide (6 ≤ count938 b) else (if i < 945 then decide (7 ≤ count938 b) else decide (1 ≤ count945 b)))) else (if i < 949 then (if i < 947 then decide (2 ≤ count945 b) else (if i < 948 then decide (1 ≤ count947 b) else decide (2 ≤ count947 b))) else (if i < 951 then (if i < 950 then decide (1 ≤ count949 b) else decide (2 ≤ count949 b)) else (if i < 952 then decide (3 ≤ count949 b) else decide (4 ≤ count949 b))))) else (if i < 959 then (if i < 956 then (if i < 954 then decide (1 ≤ count953 b) else (if i < 955 then decide (2 ≤ count953 b) else decide (1 ≤ count955 b))) else (if i < 957 then decide (2 ≤ count955 b) else (if i < 958 then decide (1 ≤ count957 b) else decide (2 ≤ count957 b)))) else (if i < 962 then (if i < 960 then decide (3 ≤ count957 b) else (if i < 961 then decide (4 ≤ count957 b) else decide (1 ≤ count961 b))) else (if i < 964 then (if i < 963 then decide (2 ≤ count961 b) else decide (3 ≤ count961 b)) else (if i < 965 then decide (4 ≤ count961 b) else decide (5 ≤ count961 b)))))) else (if i < 979 then (if i < 972 then (if i < 969 then (if i < 967 then decide (6 ≤ count961 b) else (if i < 968 then decide (7 ≤ count961 b) else decide (8 ≤ count961 b))) else (if i < 970 then decide (1 ≤ count969 b) else (if i < 971 then decide (2 ≤ count969 b) else decide (3 ≤ count969 b)))) else (if i < 975 then (if i < 973 then decide (4 ≤ count969 b) else (if i < 974 then decide (5 ≤ count969 b) else decide (6 ≤ count969 b))) else (if i < 977 then (if i < 976 then decide (7 ≤ count969 b) else decide (8 ≤ count969 b)) else (if i < 978 then decide (9 ≤ count969 b) else decide (10 ≤ count969 b))))) else (if i < 985 then (if i < 982 then (if i < 980 then decide (11 ≤ count969 b) else (if i < 981 then decide (12 ≤ count969 b) else decide (13 ≤ count969 b))) else (if i < 983 then decide (14 ≤ count969 b) else (if i < 984 then decide (15 ≤ count969 b) else decide (1 ≤ count984 b)))) else (if i < 988 then (if i < 986 then decide (2 ≤ count984 b) else (if i < 987 then decide (1 ≤ count986 b) else decide (2 ≤ count986 b))) else (if i < 990 then (if i < 989 then decide (3 ≤ count986 b) else decide (1 ≤ count989 b)) else (if i < 991 then decide (2 ≤ count989 b) else decide (1 ≤ count991 b))))))) else (if i < 1018 then (if i < 1005 then (if i < 998 then (if i < 995 then (if i < 993 then decide (2 ≤ count991 b) else (if i < 994 then decide (1 ≤ count993 b) else decide (2 ≤ count993 b))) else (if i < 996 then decide (3 ≤ count993 b) else (if i < 997 then decide (4 ≤ count993 b) else decide (1 ≤ count997 b)))) else (if i < 1001 then (if i < 999 then decide (2 ≤ count997 b) else (if i < 1000 then decide (3 ≤ count997 b) else decide (4 ≤ count997 b))) else (if i < 1003 then (if i < 1002 then decide (5 ≤ count997 b) else decide (6 ≤ count997 b)) else (if i < 1004 then decide (7 ≤ count997 b) else decide (1 ≤ count1004 b))))) else (if i < 1011 then (if i < 1008 then (if i < 1006 then decide (2 ≤ count1004 b) else (if i < 1007 then decide (1 ≤ count1006 b) else decide (2 ≤ count1006 b))) else (if i < 1009 then decide (1 ≤ count1008 b) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (3 ≤ count1008 b)))) else (if i < 1014 then (if i < 1012 then decide (4 ≤ count1008 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b))) else (if i < 1016 then (if i < 1015 then decide (1 ≤ count1014 b) else decide (2 ≤ count1014 b)) else (if i < 1017 then decide (1 ≤ count1016 b) else decide (2 ≤ count1016 b)))))) else (if i < 1031 then (if i < 1024 then (if i < 1021 then (if i < 1019 then decide (3 ≤ count1016 b) else (if i < 1020 then decide (4 ≤ count1016 b) else decide (1 ≤ count1020 b))) else (if i < 1022 then decide (2 ≤ count1020 b) else (if i < 1023 then decide (3 ≤ count1020 b) else decide (4 ≤ count1020 b)))) else (if i < 1027 then (if i < 1025 then decide (5 ≤ count1020 b) else (if i < 1026 then decide (6 ≤ count1020 b) else decide (7 ≤ count1020 b))) else (if i < 1029 then (if i < 1028 then decide (8 ≤ count1020 b) else decide (1 ≤ count1028 b)) else (if i < 1030 then decide (2 ≤ count1028 b) else decide (3 ≤ count1028 b))))) else (if i < 1038 then (if i < 1034 then (if i < 1032 then decide (4 ≤ count1028 b) else (if i < 1033 then decide (5 ≤ count1028 b) else decide (6 ≤ count1028 b))) else (if i < 1036 then (if i < 1035 then decide (7 ≤ count1028 b) else decide (8 ≤ count1028 b)) else (if i < 1037 then decide (9 ≤ count1028 b) else decide (10 ≤ count1028 b)))) else (if i < 1041 then (if i < 1039 then decide (11 ≤ count1028 b) else (if i < 1040 then decide (12 ≤ count1028 b) else decide (13 ≤ count1028 b))) else (if i < 1043 then (if i < 1042 then decide (14 ≤ count1028 b) else decide (15 ≤ count1028 b)) else (if i < 1044 then decide (1 ≤ count1043 b) else decide (2 ≤ count1043 b))))))))) else (if i < 1149 then (if i < 1097 then (if i < 1071 then (if i < 1058 then (if i < 1051 then (if i < 1048 then (if i < 1046 then decide (3 ≤ count1043 b) else (if i < 1047 then decide (4 ≤ count1043 b) else decide (5 ≤ count1043 b))) else (if i < 1049 then decide (6 ≤ count1043 b) else (if i < 1050 then decide (7 ≤ count1043 b) else decide (8 ≤ count1043 b)))) else (if i < 1054 then (if i < 1052 then decide (9 ≤ count1043 b) else (if i < 1053 then decide (10 ≤ count1043 b) else decide (11 ≤ count1043 b))) else (if i < 1056 then (if i < 1055 then decide (12 ≤ count1043 b) else decide (13 ≤ count1043 b)) else (if i < 1057 then decide (14 ≤ count1043 b) else decide (15 ≤ count1043 b))))) else (if i < 1064 then (if i < 1061 then (if i < 1059 then decide (16 ≤ count1043 b) else (if i < 1060 then decide (17 ≤ count1043 b) else decide (18 ≤ count1043 b))) else (if i < 1062 then decide (19 ≤ count1043 b) else (if i < 1063 then decide (1 ≤ count1062 b) else decide (2 ≤ count1062 b)))) else (if i < 1067 then (if i < 1065 then decide (3 ≤ count1062 b) else (if i < 1066 then decide (4 ≤ count1062 b) else decide (5 ≤ count1062 b))) else (if i < 1069 then (if i < 1068 then decide (6 ≤ count1062 b) else decide (7 ≤ count1062 b)) else (if i < 1070 then decide (8 ≤ count1062 b) else decide (9 ≤ count1062 b)))))) else (if i < 1084 then (if i < 1077 then (if i < 1074 then (if i < 1072 then decide (10 ≤ count1062 b) else (if i < 1073 then decide (11 ≤ count1062 b) else decide (12 ≤ count1062 b))) else (if i < 1075 then decide (13 ≤ count1062 b) else (if i < 1076 then decide (14 ≤ count1062 b) else decide (15 ≤ count1062 b)))) else (if i < 1080 then (if i < 1078 then decide (16 ≤ count1062 b) else (if i < 1079 then decide (17 ≤ count1062 b) else decide (18 ≤ count1062 b))) else (if i < 1082 then (if i < 1081 then decide (19 ≤ count1062 b) else decide (1 ≤ count1081 b)) else (if i < 1083 then decide (2 ≤ count1081 b) else decide (1 ≤ count1083 b))))) else (if i < 1090 then (if i < 1087 then (if i < 1085 then decide (2 ≤ count1083 b) else (if i < 1086 then decide (3 ≤ count1083 b) else decide (1 ≤ count1086 b))) else (if i < 1088 then decide (2 ≤ count1086 b) else (if i < 1089 then decide (1 ≤ count1088 b) else decide (2 ≤ count1088 b)))) else (if i < 1093 then (if i < 1091 then decide (1 ≤ count1090 b) else (if i < 1092 then decide (2 ≤ count1090 b) else decide (3 ≤ count1090 b))) else (if i < 1095 then (if i < 1094 then decide (4 ≤ count1090 b) else decide (1 ≤ count1094 b)) else (if i < 1096 then decide (2 ≤ count1094 b) else decide (3 ≤ count1094 b))))))) else (if i < 1123 then (if i < 1110 then (if i < 1103 then (if i < 1100 then (if i < 1098 then decide (4 ≤ count1094 b) else (if i < 1099 then decide (5 ≤ count1094 b) else decide (6 ≤ count1094 b))) else (if i < 1101 then decide (7 ≤ count1094 b) else (if i < 1102 then decide (1 ≤ count1101 b) else decide (2 ≤ count1101 b)))) else (if i < 1106 then (if i < 1104 then decide (1 ≤ count1103 b) else (if i < 1105 then decide (2 ≤ count1103 b) else decide (3 ≤ count1103 b))) else (if i < 1108 then (if i < 1107 then decide (1 ≤ count1106 b) else decide (2 ≤ count1106 b)) else (if i < 1109 then decide (1 ≤ count1108 b) else decide (2 ≤ count1108 b))))) else (if i < 1116 then (if i < 1113 then (if i < 1111 then decide (1 ≤ count1110 b) else (if i < 1112 then decide (2 ≤ count1110 b) else decide (3 ≤ count1110 b))) else (if i < 1114 then decide (4 ≤ count1110 b) else (if i < 1115 then decide (1 ≤ count1114 b) else decide (2 ≤ count1114 b)))) else (if i < 1119 then (if i < 1117 then decide (3 ≤ count1114 b) else (if i < 1118 then decide (4 ≤ count1114 b) else decide (5 ≤ count1114 b))) else (if i < 1121 then (if i < 1120 then decide (6 ≤ count1114 b) else decide (7 ≤ count1114 b)) else (if i < 1122 then decide (1 ≤ count1121 b) else decide (2 ≤ count1121 b)))))) else (if i < 1136 then (if i < 1129 then (if i < 1126 then (if i < 1124 then decide (3 ≤ count1121 b) else (if i < 1125 then decide (4 ≤ count1121 b) else decide (5 ≤ count1121 b))) else (if i < 1127 then decide (6 ≤ count1121 b) else (if i < 1128 then decide (7 ≤ count1121 b) else decide (8 ≤ count1121 b)))) else (if i < 1132 then (if i < 1130 then decide (9 ≤ count1121 b) else (if i < 1131 then decide (10 ≤ count1121 b) else decide (11 ≤ count1121 b))) else (if i < 1134 then (if i < 1133 then decide (12 ≤ count1121 b) else decide (13 ≤ count1121 b)) else (if i < 1135 then decide (14 ≤ count1121 b) else decide (1 ≤ count1135 b))))) else (if i < 1142 then (if i < 1139 then (if i < 1137 then decide (2 ≤ count1135 b) else (if i < 1138 then decide (1 ≤ count1137 b) else decide (2 ≤ count1137 b))) else (if i < 1140 then decide (3 ≤ count1137 b) else (if i < 1141 then decide (1 ≤ count1140 b) else decide (2 ≤ count1140 b)))) else (if i < 1145 then (if i < 1143 then decide (1 ≤ count1142 b) else (if i < 1144 then decide (2 ≤ count1142 b) else decide (1 ≤ count1144 b))) else (if i < 1147 then (if i < 1146 then decide (2 ≤ count1144 b) else decide (3 ≤ count1144 b)) else (if i < 1148 then decide (4 ≤ count1144 b) else decide (1 ≤ count1148 b)))))))) else (if i < 1201 then (if i < 1175 then (if i < 1162 then (if i < 1155 then (if i < 1152 then (if i < 1150 then decide (2 ≤ count1148 b) else (if i < 1151 then decide (3 ≤ count1148 b) else decide (4 ≤ count1148 b))) else (if i < 1153 then decide (5 ≤ count1148 b) else (if i < 1154 then decide (6 ≤ count1148 b) else decide (7 ≤ count1148 b)))) else (if i < 1158 then (if i < 1156 then decide (1 ≤ count1155 b) else (if i < 1157 then decide (2 ≤ count1155 b) else decide (1 ≤ count1157 b))) else (if i < 1160 then (if i < 1159 then decide (2 ≤ count1157 b) else decide (3 ≤ count1157 b)) else (if i < 1161 then decide (1 ≤ count1160 b) else decide (2 ≤ count1160 b))))) else (if i < 1168 then (if i < 1165 then (if i < 1163 then decide (1 ≤ count1162 b) else (if i < 1164 then decide (2 ≤ count1162 b) else decide (1 ≤ count1164 b))) else (if i < 1166 then decide (2 ≤ count1164 b) else (if i < 1167 then decide (3 ≤ count1164 b) else decide (4 ≤ count1164 b)))) else (if i < 1171 then (if i < 1169 then decide (1 ≤ count1168 b) else (if i < 1170 then decide (2 ≤ count1168 b) else decide (3 ≤ count1168 b))) else (if i < 1173 then (if i < 1172 then decide (4 ≤ count1168 b) else decide (5 ≤ count1168 b)) else (if i < 1174 then decide (6 ≤ count1168 b) else decide (7 ≤ count1168 b)))))) else (if i < 1188 then (if i < 1181 then (if i < 1178 then (if i < 1176 then decide (1 ≤ count1175 b) else (if i < 1177 then decide (2 ≤ count1175 b) else decide (3 ≤ count1175 b))) else (if i < 1179 then decide (4 ≤ count1175 b) else (if i < 1180 then decide (5 ≤ count1175 b) else decide (6 ≤ count1175 b)))) else (if i < 1184 then (if i < 1182 then decide (7 ≤ count1175 b) else (if i < 1183 then decide (8 ≤ count1175 b) else decide (9 ≤ count1175 b))) else (if i < 1186 then (if i < 1185 then decide (10 ≤ count1175 b) else decide (11 ≤ count1175 b)) else (if i < 1187 then decide (12 ≤ count1175 b) else decide (13 ≤ count1175 b))))) else (if i < 1194 then (if i < 1191 then (if i < 1189 then decide (14 ≤ count1175 b) else (if i < 1190 then decide (1 ≤ count1189 b) else decide (2 ≤ count1189 b))) else (if i < 1192 then decide (3 ≤ count1189 b) else (if i < 1193 then decide (4 ≤ count1189 b) else decide (5 ≤ count1189 b)))) else (if i < 1197 then (if i < 1195 then decide (6 ≤ count1189 b) else (if i < 1196 then decide (7 ≤ count1189 b) else decide (8 ≤ count1189 b))) else (if i < 1199 then (if i < 1198 then decide (9 ≤ count1189 b) else decide (10 ≤ count1189 b)) else (if i < 1200 then decide (11 ≤ count1189 b) else decide (12 ≤ count1189 b))))))) else (if i < 1227 then (if i < 1214 then (if i < 1207 then (if i < 1204 then (if i < 1202 then decide (13 ≤ count1189 b) else (if i < 1203 then decide (14 ≤ count1189 b) else decide (15 ≤ count1189 b))) else (if i < 1205 then decide (16 ≤ count1189 b) else (if i < 1206 then decide (17 ≤ count1189 b) else decide (18 ≤ count1189 b)))) else (if i < 1210 then (if i < 1208 then decide (19 ≤ count1189 b) else (if i < 1209 then decide (20 ≤ count1189 b) else decide (21 ≤ count1189 b))) else (if i < 1212 then (if i < 1211 then decide (22 ≤ count1189 b) else decide (23 ≤ count1189 b)) else (if i < 1213 then decide (24 ≤ count1189 b) else decide (25 ≤ count1189 b))))) else (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (26 ≤ count1189 b) else (if i < 1216 then decide (27 ≤ count1189 b) else decide (28 ≤ count1189 b))) else (if i < 1218 then decide (1 ≤ count1217 b) else (if i < 1219 then decide (2 ≤ count1217 b) else decide (1 ≤ count1219 b)))) else (if i < 1223 then (if i < 1221 then decide (2 ≤ count1219 b) else (if i < 1222 then decide (3 ≤ count1219 b) else decide (1 ≤ count1222 b))) else (if i < 1225 then (if i < 1224 then decide (2 ≤ count1222 b) else decide (1 ≤ count1224 b)) else (if i < 1226 then decide (2 ≤ count1224 b) else decide (1 ≤ count1226 b)))))) else (if i < 1240 then (if i < 1233 then (if i < 1230 then (if i < 1228 then decide (2 ≤ count1226 b) else (if i < 1229 then decide (3 ≤ count1226 b) else decide (4 ≤ count1226 b))) else (if i < 1231 then decide (1 ≤ count1230 b) else (if i < 1232 then decide (2 ≤ count1230 b) else decide (3 ≤ count1230 b)))) else (if i < 1236 then (if i < 1234 then decide (4 ≤ count1230 b) else (if i < 1235 then decide (5 ≤ count1230 b) else decide (6 ≤ count1230 b))) else (if i < 1238 then (if i < 1237 then decide (7 ≤ count1230 b) else decide (1 ≤ count1237 b)) else (if i < 1239 then decide (2 ≤ count1237 b) else decide (1 ≤ count1239 b))))) else (if i < 1247 then (if i < 1243 then (if i < 1241 then decide (2 ≤ count1239 b) else (if i < 1242 then decide (3 ≤ count1239 b) else decide (1 ≤ count1242 b))) else (if i < 1245 then (if i < 1244 then decide (2 ≤ count1242 b) else decide (1 ≤ count1244 b)) else (if i < 1246 then decide (2 ≤ count1244 b) else decide (1 ≤ count1246 b)))) else (if i < 1250 then (if i < 1248 then decide (2 ≤ count1246 b) else (if i < 1249 then decide (3 ≤ count1246 b) else decide (4 ≤ count1246 b))) else (if i < 1252 then (if i < 1251 then decide (1 ≤ count1250 b) else decide (2 ≤ count1250 b)) else (if i < 1253 then decide (3 ≤ count1250 b) else decide (4 ≤ count1250 b)))))))))) else (if i < 1463 then (if i < 1358 then (if i < 1306 then (if i < 1280 then (if i < 1267 then (if i < 1260 then (if i < 1257 then (if i < 1255 then decide (5 ≤ count1250 b) else (if i < 1256 then decide (6 ≤ count1250 b) else decide (7 ≤ count1250 b))) else (if i < 1258 then decide (1 ≤ count1257 b) else (if i < 1259 then decide (2 ≤ count1257 b) else decide (3 ≤ count1257 b)))) else (if i < 1263 then (if i < 1261 then decide (4 ≤ count1257 b) else (if i < 1262 then decide (5 ≤ count1257 b) else decide (6 ≤ count1257 b))) else (if i < 1265 then (if i < 1264 then decide (7 ≤ count1257 b) else decide (8 ≤ count1257 b)) else (if i < 1266 then decide (9 ≤ count1257 b) else decide (10 ≤ count1257 b))))) else (if i < 1273 then (if i < 1270 then (if i < 1268 then decide (11 ≤ count1257 b) else (if i < 1269 then decide (12 ≤ count1257 b) else decide (13 ≤ count1257 b))) else (if i < 1271 then decide (14 ≤ count1257 b) else (if i < 1272 then decide (1 ≤ count1271 b) else decide (2 ≤ count1271 b)))) else (if i < 1276 then (if i < 1274 then decide (1 ≤ count1273 b) else (if i < 1275 then decide (2 ≤ count1273 b) else decide (3 ≤ count1273 b))) else (if i < 1278 then (if i < 1277 then decide (1 ≤ count1276 b) else decide (2 ≤ count1276 b)) else (if i < 1279 then decide (1 ≤ count1278 b) else decide (2 ≤ count1278 b)))))) else (if i < 1293 then (if i < 1286 then (if i < 1283 then (if i < 1281 then decide (1 ≤ count1280 b) else (if i < 1282 then decide (2 ≤ count1280 b) else decide (3 ≤ count1280 b))) else (if i < 1284 then decide (4 ≤ count1280 b) else (if i < 1285 then decide (1 ≤ count1284 b) else decide (2 ≤ count1284 b)))) else (if i < 1289 then (if i < 1287 then decide (3 ≤ count1284 b) else (if i < 1288 then decide (4 ≤ count1284 b) else decide (5 ≤ count1284 b))) else (if i < 1291 then (if i < 1290 then decide (6 ≤ count1284 b) else decide (7 ≤ count1284 b)) else (if i < 1292 then decide (1 ≤ count1291 b) else decide (2 ≤ count1291 b))))) else (if i < 1299 then (if i < 1296 then (if i < 1294 then decide (1 ≤ count1293 b) else (if i < 1295 then decide (2 ≤ count1293 b) else decide (1 ≤ count1295 b))) else (if i < 1297 then decide (2 ≤ count1295 b) else (if i < 1298 then decide (3 ≤ count1295 b) else decide (4 ≤ count1295 b)))) else (if i < 1302 then (if i < 1300 then decide (1 ≤ count1299 b) else (if i < 1301 then decide (2 ≤ count1299 b) else decide (1 ≤ count1301 b))) else (if i < 1304 then (if i < 1303 then decide (2 ≤ count1301 b) else decide (1 ≤ count1303 b)) else (if i < 1305 then decide (2 ≤ count1303 b) else decide (3 ≤ count1303 b))))))) else (if i < 1332 then (if i < 1319 then (if i < 1312 then (if i < 1309 then (if i < 1307 then decide (4 ≤ count1303 b) else (if i < 1308 then decide (1 ≤ count1307 b) else decide (2 ≤ count1307 b))) else (if i < 1310 then decide (3 ≤ count1307 b) else (if i < 1311 then decide (4 ≤ count1307 b) else decide (5 ≤ count1307 b)))) else (if i < 1315 then (if i < 1313 then decide (6 ≤ count1307 b) else (if i < 1314 then decide (7 ≤ count1307 b) else decide (8 ≤ count1307 b))) else (if i < 1317 then (if i < 1316 then decide (1 ≤ count1315 b) else decide (2 ≤ count1315 b)) else (if i < 1318 then decide (3 ≤ count1315 b) else decide (4 ≤ count1315 b))))) else (if i < 1325 then (if i < 1322 then (if i < 1320 then decide (5 ≤ count1315 b) else (if i < 1321 then decide (6 ≤ count1315 b) else decide (7 ≤ count1315 b))) else (if i < 1323 then decide (8 ≤ count1315 b) else (if i < 1324 then decide (9 ≤ count1315 b) else decide (10 ≤ count1315 b)))) else (if i < 1328 then (if i < 1326 then decide (11 ≤ count1315 b) else (if i < 1327 then decide (12 ≤ count1315 b) else decide (13 ≤ count1315 b))) else (if i < 1330 then (if i < 1329 then decide (14 ≤ count1315 b) else decide (15 ≤ count1315 b)) else (if i < 1331 then decide (1 ≤ count1330 b) else decide (2 ≤ count1330 b)))))) else (if i < 1345 then (if i < 1338 then (if i < 1335 then (if i < 1333 then decide (3 ≤ count1330 b) else (if i < 1334 then decide (4 ≤ count1330 b) else decide (5 ≤ count1330 b))) else (if i < 1336 then decide (6 ≤ count1330 b) else (if i < 1337 then decide (7 ≤ count1330 b) else decide (8 ≤ count1330 b)))) else (if i < 1341 then (if i < 1339 then decide (9 ≤ count1330 b) else (if i < 1340 then decide (10 ≤ count1330 b) else decide (11 ≤ count1330 b))) else (if i < 1343 then (if i < 1342 then decide (12 ≤ count1330 b) else decide (13 ≤ count1330 b)) else (if i < 1344 then decide (14 ≤ count1330 b) else decide (15 ≤ count1330 b))))) else (if i < 1351 then (if i < 1348 then (if i < 1346 then decide (16 ≤ count1330 b) else (if i < 1347 then decide (17 ≤ count1330 b) else decide (18 ≤ count1330 b))) else (if i < 1349 then decide (19 ≤ count1330 b) else (if i < 1350 then decide (20 ≤ count1330 b) else decide (21 ≤ count1330 b)))) else (if i < 1354 then (if i < 1352 then decide (22 ≤ count1330 b) else (if i < 1353 then decide (23 ≤ count1330 b) else decide (24 ≤ count1330 b))) else (if i < 1356 then (if i < 1355 then decide (25 ≤ count1330 b) else decide (26 ≤ count1330 b)) else (if i < 1357 then decide (27 ≤ count1330 b) else decide (28 ≤ count1330 b)))))))) else (if i < 1410 then (if i < 1384 then (if i < 1371 then (if i < 1364 then (if i < 1361 then (if i < 1359 then decide (29 ≤ count1330 b) else (if i < 1360 then decide (1 ≤ count1359 b) else decide (2 ≤ count1359 b))) else (if i < 1362 then decide (3 ≤ count1359 b) else (if i < 1363 then decide (4 ≤ count1359 b) else decide (5 ≤ count1359 b)))) else (if i < 1367 then (if i < 1365 then decide (6 ≤ count1359 b) else (if i < 1366 then decide (7 ≤ count1359 b) else decide (8 ≤ count1359 b))) else (if i < 1369 then (if i < 1368 then decide (9 ≤ count1359 b) else decide (10 ≤ count1359 b)) else (if i < 1370 then decide (11 ≤ count1359 b) else decide (12 ≤ count1359 b))))) else (if i < 1377 then (if i < 1374 then (if i < 1372 then decide (13 ≤ count1359 b) else (if i < 1373 then decide (14 ≤ count1359 b) else decide (15 ≤ count1359 b))) else (if i < 1375 then decide (16 ≤ count1359 b) else (if i < 1376 then decide (17 ≤ count1359 b) else decide (18 ≤ count1359 b)))) else (if i < 1380 then (if i < 1378 then decide (19 ≤ count1359 b) else (if i < 1379 then decide (20 ≤ count1359 b) else decide (21 ≤ count1359 b))) else (if i < 1382 then (if i < 1381 then decide (22 ≤ count1359 b) else decide (23 ≤ count1359 b)) else (if i < 1383 then decide (24 ≤ count1359 b) else decide (25 ≤ count1359 b)))))) else (if i < 1397 then (if i < 1390 then (if i < 1387 then (if i < 1385 then decide (26 ≤ count1359 b) else (if i < 1386 then decide (27 ≤ count1359 b) else decide (28 ≤ count1359 b))) else (if i < 1388 then decide (29 ≤ count1359 b) else (if i < 1389 then decide (30 ≤ count1359 b) else decide (31 ≤ count1359 b)))) else (if i < 1393 then (if i < 1391 then decide (32 ≤ count1359 b) else (if i < 1392 then decide (33 ≤ count1359 b) else decide (34 ≤ count1359 b))) else (if i < 1395 then (if i < 1394 then decide (35 ≤ count1359 b) else decide (36 ≤ count1359 b)) else (if i < 1396 then decide (37 ≤ count1359 b) else decide (38 ≤ count1359 b))))) else (if i < 1403 then (if i < 1400 then (if i < 1398 then decide (39 ≤ count1359 b) else (if i < 1399 then decide (40 ≤ count1359 b) else decide (41 ≤ count1359 b))) else (if i < 1401 then decide (42 ≤ count1359 b) else (if i < 1402 then decide (1 ≤ count1401 b) else decide (2 ≤ count1401 b)))) else (if i < 1406 then (if i < 1404 then decide (1 ≤ count1403 b) else (if i < 1405 then decide (2 ≤ count1403 b) else decide (3 ≤ count1403 b))) else (if i < 1408 then (if i < 1407 then decide (1 ≤ count1406 b) else decide (2 ≤ count1406 b)) else (if i < 1409 then decide (1 ≤ count1408 b) else decide (2 ≤ count1408 b))))))) else (if i < 1436 then (if i < 1423 then (if i < 1416 then (if i < 1413 then (if i < 1411 then decide (1 ≤ count1410 b) else (if i < 1412 then decide (2 ≤ count1410 b) else decide (3 ≤ count1410 b))) else (if i < 1414 then decide (4 ≤ count1410 b) else (if i < 1415 then decide (1 ≤ count1414 b) else decide (2 ≤ count1414 b)))) else (if i < 1419 then (if i < 1417 then decide (3 ≤ count1414 b) else (if i < 1418 then decide (4 ≤ count1414 b) else decide (5 ≤ count1414 b))) else (if i < 1421 then (if i < 1420 then decide (6 ≤ count1414 b) else decide (7 ≤ count1414 b)) else (if i < 1422 then decide (1 ≤ count1421 b) else decide (2 ≤ count1421 b))))) else (if i < 1429 then (if i < 1426 then (if i < 1424 then decide (1 ≤ count1423 b) else (if i < 1425 then decide (2 ≤ count1423 b) else decide (3 ≤ count1423 b))) else (if i < 1427 then decide (1 ≤ count1426 b) else (if i < 1428 then decide (2 ≤ count1426 b) else decide (1 ≤ count1428 b)))) else (if i < 1432 then (if i < 1430 then decide (2 ≤ count1428 b) else (if i < 1431 then decide (1 ≤ count1430 b) else decide (2 ≤ count1430 b))) else (if i < 1434 then (if i < 1433 then decide (3 ≤ count1430 b) else decide (4 ≤ count1430 b)) else (if i < 1435 then decide (1 ≤ count1434 b) else decide (2 ≤ count1434 b)))))) else (if i < 1449 then (if i < 1442 then (if i < 1439 then (if i < 1437 then decide (3 ≤ count1434 b) else (if i < 1438 then decide (4 ≤ count1434 b) else decide (5 ≤ count1434 b))) else (if i < 1440 then decide (6 ≤ count1434 b) else (if i < 1441 then decide (7 ≤ count1434 b) else decide (1 ≤ count1441 b)))) else (if i < 1445 then (if i < 1443 then decide (2 ≤ count1441 b) else (if i < 1444 then decide (3 ≤ count1441 b) else decide (4 ≤ count1441 b))) else (if i < 1447 then (if i < 1446 then decide (5 ≤ count1441 b) else decide (6 ≤ count1441 b)) else (if i < 1448 then decide (7 ≤ count1441 b) else decide (8 ≤ count1441 b))))) else (if i < 1456 then (if i < 1452 then (if i < 1450 then decide (9 ≤ count1441 b) else (if i < 1451 then decide (10 ≤ count1441 b) else decide (11 ≤ count1441 b))) else (if i < 1454 then (if i < 1453 then decide (12 ≤ count1441 b) else decide (13 ≤ count1441 b)) else (if i < 1455 then decide (14 ≤ count1441 b) else decide (1 ≤ count1455 b)))) else (if i < 1459 then (if i < 1457 then decide (2 ≤ count1455 b) else (if i < 1458 then decide (1 ≤ count1457 b) else decide (2 ≤ count1457 b))) else (if i < 1461 then (if i < 1460 then decide (3 ≤ count1457 b) else decide (1 ≤ count1460 b)) else (if i < 1462 then decide (2 ≤ count1460 b) else decide (1 ≤ count1462 b))))))))) else (if i < 1568 then (if i < 1515 then (if i < 1489 then (if i < 1476 then (if i < 1469 then (if i < 1466 then (if i < 1464 then decide (2 ≤ count1462 b) else (if i < 1465 then decide (1 ≤ count1464 b) else decide (2 ≤ count1464 b))) else (if i < 1467 then decide (3 ≤ count1464 b) else (if i < 1468 then decide (4 ≤ count1464 b) else decide (1 ≤ count1468 b)))) else (if i < 1472 then (if i < 1470 then decide (2 ≤ count1468 b) else (if i < 1471 then decide (3 ≤ count1468 b) else decide (4 ≤ count1468 b))) else (if i < 1474 then (if i < 1473 then decide (5 ≤ count1468 b) else decide (6 ≤ count1468 b)) else (if i < 1475 then decide (7 ≤ count1468 b) else decide (1 ≤ count1475 b))))) else (if i < 1482 then (if i < 1479 then (if i < 1477 then decide (2 ≤ count1475 b) else (if i < 1478 then decide (1 ≤ count1477 b) else decide (2 ≤ count1477 b))) else (if i < 1480 then decide (3 ≤ count1477 b) else (if i < 1481 then decide (1 ≤ count1480 b) else decide (2 ≤ count1480 b)))) else (if i < 1485 then (if i < 1483 then decide (1 ≤ count1482 b) else (if i < 1484 then decide (2 ≤ count1482 b) else decide (1 ≤ count1484 b))) else (if i < 1487 then (if i < 1486 then decide (2 ≤ count1484 b) else decide (3 ≤ count1484 b)) else (if i < 1488 then decide (4 ≤ count1484 b) else decide (1 ≤ count1488 b)))))) else (if i < 1502 then (if i < 1495 then (if i < 1492 then (if i < 1490 then decide (2 ≤ count1488 b) else (if i < 1491 then decide (3 ≤ count1488 b) else decide (4 ≤ count1488 b))) else (if i < 1493 then decide (5 ≤ count1488 b) else (if i < 1494 then decide (6 ≤ count1488 b) else decide (7 ≤ count1488 b)))) else (if i < 1498 then (if i < 1496 then decide (1 ≤ count1495 b) else (if i < 1497 then decide (2 ≤ count1495 b) else decide (3 ≤ count1495 b))) else (if i < 1500 then (if i < 1499 then decide (4 ≤ count1495 b) else decide (5 ≤ count1495 b)) else (if i < 1501 then decide (6 ≤ count1495 b) else decide (7 ≤ count1495 b))))) else (if i < 1508 then (if i < 1505 then (if i < 1503 then decide (8 ≤ count1495 b) else (if i < 1504 then decide (9 ≤ count1495 b) else decide (10 ≤ count1495 b))) else (if i < 1506 then decide (11 ≤ count1495 b) else (if i < 1507 then decide (12 ≤ count1495 b) else decide (13 ≤ count1495 b)))) else (if i < 1511 then (if i < 1509 then decide (14 ≤ count1495 b) else (if i < 1510 then decide (1 ≤ count1509 b) else decide (2 ≤ count1509 b))) else (if i < 1513 then (if i < 1512 then decide (3 ≤ count1509 b) else decide (4 ≤ count1509 b)) else (if i < 1514 then decide (5 ≤ count1509 b) else decide (6 ≤ count1509 b))))))) else (if i < 1541 then (if i < 1528 then (if i < 1521 then (if i < 1518 then (if i < 1516 then decide (7 ≤ count1509 b) else (if i < 1517 then decide (8 ≤ count1509 b) else decide (9 ≤ count1509 b))) else (if i < 1519 then decide (10 ≤ count1509 b) else (if i < 1520 then decide (11 ≤ count1509 b) else decide (12 ≤ count1509 b)))) else (if i < 1524 then (if i < 1522 then decide (13 ≤ count1509 b) else (if i < 1523 then decide (14 ≤ count1509 b) else decide (15 ≤ count1509 b))) else (if i < 1526 then (if i < 1525 then decide (16 ≤ count1509 b) else decide (17 ≤ count1509 b)) else (if i < 1527 then decide (1 ≤ count1526 b) else decide (2 ≤ count1526 b))))) else (if i < 1534 then (if i < 1531 then (if i < 1529 then decide (1 ≤ count1528 b) else (if i < 1530 then decide (2 ≤ count1528 b) else decide (3 ≤ count1528 b))) else (if i < 1532 then decide (1 ≤ count1531 b) else (if i < 1533 then decide (2 ≤ count1531 b) else decide (1 ≤ count1533 b)))) else (if i < 1537 then (if i < 1535 then decide (2 ≤ count1533 b) else (if i < 1536 then decide (1 ≤ count1535 b) else decide (2 ≤ count1535 b))) else (if i < 1539 then (if i < 1538 then decide (3 ≤ count1535 b) else decide (4 ≤ count1535 b)) else (if i < 1540 then decide (1 ≤ count1539 b) else decide (2 ≤ count1539 b)))))) else (if i < 1554 then (if i < 1547 then (if i < 1544 then (if i < 1542 then decide (3 ≤ count1539 b) else (if i < 1543 then decide (4 ≤ count1539 b) else decide (5 ≤ count1539 b))) else (if i < 1545 then decide (6 ≤ count1539 b) else (if i < 1546 then decide (7 ≤ count1539 b) else decide (1 ≤ count1546 b)))) else (if i < 1550 then (if i < 1548 then decide (2 ≤ count1546 b) else (if i < 1549 then decide (1 ≤ count1548 b) else decide (2 ≤ count1548 b))) else (if i < 1552 then (if i < 1551 then decide (3 ≤ count1548 b) else decide (1 ≤ count1551 b)) else (if i < 1553 then decide (2 ≤ count1551 b) else decide (1 ≤ count1553 b))))) else (if i < 1561 then (if i < 1557 then (if i < 1555 then decide (2 ≤ count1553 b) else (if i < 1556 then decide (1 ≤ count1555 b) else decide (2 ≤ count1555 b))) else (if i < 1559 then (if i < 1558 then decide (3 ≤ count1555 b) else decide (4 ≤ count1555 b)) else (if i < 1560 then decide (1 ≤ count1559 b) else decide (2 ≤ count1559 b)))) else (if i < 1564 then (if i < 1562 then decide (3 ≤ count1559 b) else (if i < 1563 then decide (4 ≤ count1559 b) else decide (5 ≤ count1559 b))) else (if i < 1566 then (if i < 1565 then decide (6 ≤ count1559 b) else decide (7 ≤ count1559 b)) else (if i < 1567 then decide (1 ≤ count1566 b) else decide (2 ≤ count1566 b)))))))) else (if i < 1620 then (if i < 1594 then (if i < 1581 then (if i < 1574 then (if i < 1571 then (if i < 1569 then decide (3 ≤ count1566 b) else (if i < 1570 then decide (4 ≤ count1566 b) else decide (5 ≤ count1566 b))) else (if i < 1572 then decide (6 ≤ count1566 b) else (if i < 1573 then decide (7 ≤ count1566 b) else decide (8 ≤ count1566 b)))) else (if i < 1577 then (if i < 1575 then decide (9 ≤ count1566 b) else (if i < 1576 then decide (10 ≤ count1566 b) else decide (11 ≤ count1566 b))) else (if i < 1579 then (if i < 1578 then decide (12 ≤ count1566 b) else decide (13 ≤ count1566 b)) else (if i < 1580 then decide (14 ≤ count1566 b) else decide (1 ≤ count1580 b))))) else (if i < 1587 then (if i < 1584 then (if i < 1582 then decide (2 ≤ count1580 b) else (if i < 1583 then decide (1 ≤ count1582 b) else decide (2 ≤ count1582 b))) else (if i < 1585 then decide (3 ≤ count1582 b) else (if i < 1586 then decide (1 ≤ count1585 b) else decide (2 ≤ count1585 b)))) else (if i < 1590 then (if i < 1588 then decide (1 ≤ count1587 b) else (if i < 1589 then decide (2 ≤ count1587 b) else decide (1 ≤ count1589 b))) else (if i < 1592 then (if i < 1591 then decide (2 ≤ count1589 b) else decide (3 ≤ count1589 b)) else (if i < 1593 then decide (4 ≤ count1589 b) else decide (1 ≤ count1593 b)))))) else (if i < 1607 then (if i < 1600 then (if i < 1597 then (if i < 1595 then decide (2 ≤ count1593 b) else (if i < 1596 then decide (3 ≤ count1593 b) else decide (4 ≤ count1593 b))) else (if i < 1598 then decide (5 ≤ count1593 b) else (if i < 1599 then decide (6 ≤ count1593 b) else decide (7 ≤ count1593 b)))) else (if i < 1603 then (if i < 1601 then decide (1 ≤ count1600 b) else (if i < 1602 then decide (2 ≤ count1600 b) else decide (1 ≤ count1602 b))) else (if i < 1605 then (if i < 1604 then decide (2 ≤ count1602 b) else decide (1 ≤ count1604 b)) else (if i < 1606 then decide (2 ≤ count1604 b) else decide (3 ≤ count1604 b))))) else (if i < 1613 then (if i < 1610 then (if i < 1608 then decide (4 ≤ count1604 b) else (if i < 1609 then decide (1 ≤ count1608 b) else decide (2 ≤ count1608 b))) else (if i < 1611 then decide (1 ≤ count1610 b) else (if i < 1612 then decide (2 ≤ count1610 b) else decide (1 ≤ count1612 b)))) else (if i < 1616 then (if i < 1614 then decide (2 ≤ count1612 b) else (if i < 1615 then decide (3 ≤ count1612 b) else decide (4 ≤ count1612 b))) else (if i < 1618 then (if i < 1617 then decide (1 ≤ count1616 b) else decide (2 ≤ count1616 b)) else (if i < 1619 then decide (3 ≤ count1616 b) else decide (4 ≤ count1616 b))))))) else (if i < 1646 then (if i < 1633 then (if i < 1626 then (if i < 1623 then (if i < 1621 then decide (5 ≤ count1616 b) else (if i < 1622 then decide (6 ≤ count1616 b) else decide (7 ≤ count1616 b))) else (if i < 1624 then decide (8 ≤ count1616 b) else (if i < 1625 then decide (1 ≤ count1624 b) else decide (2 ≤ count1624 b)))) else (if i < 1629 then (if i < 1627 then decide (3 ≤ count1624 b) else (if i < 1628 then decide (4 ≤ count1624 b) else decide (5 ≤ count1624 b))) else (if i < 1631 then (if i < 1630 then decide (6 ≤ count1624 b) else decide (7 ≤ count1624 b)) else (if i < 1632 then decide (8 ≤ count1624 b) else decide (9 ≤ count1624 b))))) else (if i < 1639 then (if i < 1636 then (if i < 1634 then decide (10 ≤ count1624 b) else (if i < 1635 then decide (11 ≤ count1624 b) else decide (12 ≤ count1624 b))) else (if i < 1637 then decide (13 ≤ count1624 b) else (if i < 1638 then decide (14 ≤ count1624 b) else decide (15 ≤ count1624 b)))) else (if i < 1642 then (if i < 1640 then decide (1 ≤ count1639 b) else (if i < 1641 then decide (2 ≤ count1639 b) else decide (3 ≤ count1639 b))) else (if i < 1644 then (if i < 1643 then decide (4 ≤ count1639 b) else decide (5 ≤ count1639 b)) else (if i < 1645 then decide (6 ≤ count1639 b) else decide (7 ≤ count1639 b)))))) else (if i < 1659 then (if i < 1652 then (if i < 1649 then (if i < 1647 then decide (8 ≤ count1639 b) else (if i < 1648 then decide (9 ≤ count1639 b) else decide (10 ≤ count1639 b))) else (if i < 1650 then decide (11 ≤ count1639 b) else (if i < 1651 then decide (12 ≤ count1639 b) else decide (13 ≤ count1639 b)))) else (if i < 1655 then (if i < 1653 then decide (14 ≤ count1639 b) else (if i < 1654 then decide (15 ≤ count1639 b) else decide (16 ≤ count1639 b))) else (if i < 1657 then (if i < 1656 then decide (17 ≤ count1639 b) else decide (1 ≤ count1656 b)) else (if i < 1658 then decide (2 ≤ count1656 b) else decide (3 ≤ count1656 b))))) else (if i < 1666 then (if i < 1662 then (if i < 1660 then decide (4 ≤ count1656 b) else (if i < 1661 then decide (5 ≤ count1656 b) else decide (6 ≤ count1656 b))) else (if i < 1664 then (if i < 1663 then decide (7 ≤ count1656 b) else decide (8 ≤ count1656 b)) else (if i < 1665 then decide (9 ≤ count1656 b) else decide (10 ≤ count1656 b)))) else (if i < 1669 then (if i < 1667 then decide (11 ≤ count1656 b) else (if i < 1668 then decide (12 ≤ count1656 b) else decide (13 ≤ count1656 b))) else (if i < 1671 then (if i < 1670 then decide (14 ≤ count1656 b) else decide (15 ≤ count1656 b)) else (if i < 1672 then decide (16 ≤ count1656 b) else decide (17 ≤ count1656 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (11 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (13 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (15 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (24 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (28 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (29 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (76 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (130 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (131 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (135 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (136 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (137 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (138 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (140 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (142 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (148 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (149 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (151 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (153 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (154 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (155 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (157 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (159 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (192 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (193 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (197 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (199 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (200 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (201 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (205 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (207 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (209 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (210 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (211 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (214 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (218 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (220 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (221 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (222 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (258 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (259 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (260 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (261 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (265 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (266 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (267 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (268 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (270 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (272 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (276 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (277 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (279 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (280 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (281 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (282 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (283 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (287 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (320 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (321 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (327 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (328 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (329 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (333 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (335 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (337 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (338 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (339 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (342 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (346 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (348 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (349 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (350 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (384 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (385 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (386 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (387 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (389 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (391 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (393 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (394 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (396 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (397 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (398 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (399 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (400 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (401 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (402 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (403 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (406 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (408 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (409 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (410 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (412 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (413 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (414 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (450 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (451 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (452 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (453 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (457 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (458 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (459 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (460 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (462 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (464 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (468 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (469 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (470 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (471 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (472 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (473 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (475 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (479 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (24 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (402 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (450 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (452 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (469 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (471 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (479 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value370 (q : Snake 81) : valuation q 370 = decide (2 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value454 (q : Snake 81) : valuation q 454 = decide (2 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value456 (q : Snake 81) : valuation q 456 = decide (2 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value458 (q : Snake 81) : valuation q 458 = decide (2 ≤ count457 (baseVal q)) := rfl
theorem value460 (q : Snake 81) : valuation q 460 = decide (2 ≤ count459 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (1 ≤ count1401 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (1 ≤ count1403 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (1 ≤ count1406 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (2 ≤ count1406 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (1 ≤ count1408 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (2 ≤ count1408 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (1 ≤ count1410 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (2 ≤ count1410 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (3 ≤ count1410 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (1 ≤ count1414 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (2 ≤ count1414 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (3 ≤ count1414 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (4 ≤ count1414 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (1 ≤ count1421 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (1 ≤ count1423 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (2 ≤ count1423 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (1 ≤ count1426 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (2 ≤ count1426 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (1 ≤ count1428 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (2 ≤ count1428 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (1 ≤ count1430 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (2 ≤ count1430 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (3 ≤ count1430 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (1 ≤ count1434 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (2 ≤ count1434 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (3 ≤ count1434 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (4 ≤ count1434 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (1 ≤ count1441 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (2 ≤ count1441 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (3 ≤ count1441 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (4 ≤ count1441 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (5 ≤ count1441 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (1 ≤ count1455 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (2 ≤ count1455 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (1 ≤ count1457 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (2 ≤ count1457 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (1 ≤ count1460 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (1 ≤ count1462 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (2 ≤ count1462 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (1 ≤ count1464 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (2 ≤ count1464 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (3 ≤ count1464 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (1 ≤ count1468 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (2 ≤ count1468 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (3 ≤ count1468 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (4 ≤ count1468 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (1 ≤ count1475 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (2 ≤ count1475 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (1 ≤ count1477 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (2 ≤ count1477 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (3 ≤ count1477 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (1 ≤ count1480 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (2 ≤ count1480 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (1 ≤ count1482 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (2 ≤ count1482 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (1 ≤ count1484 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (2 ≤ count1484 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (3 ≤ count1484 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (1 ≤ count1488 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (2 ≤ count1488 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (3 ≤ count1488 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (4 ≤ count1488 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (2 ≤ count1495 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (3 ≤ count1495 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (4 ≤ count1495 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (5 ≤ count1495 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (6 ≤ count1495 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (4 ≤ count1509 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (5 ≤ count1509 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (6 ≤ count1509 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (7 ≤ count1509 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (8 ≤ count1509 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (9 ≤ count1509 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (1 ≤ count1526 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (2 ≤ count1526 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (1 ≤ count1528 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (2 ≤ count1528 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (3 ≤ count1528 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (1 ≤ count1531 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (2 ≤ count1531 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (1 ≤ count1533 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (2 ≤ count1533 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (1 ≤ count1535 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (2 ≤ count1535 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (3 ≤ count1535 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (4 ≤ count1535 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (1 ≤ count1539 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (2 ≤ count1539 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (3 ≤ count1539 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (4 ≤ count1539 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (5 ≤ count1539 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (6 ≤ count1539 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (7 ≤ count1539 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (1 ≤ count1546 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (2 ≤ count1546 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (1 ≤ count1548 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (2 ≤ count1548 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (3 ≤ count1548 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (2 ≤ count1551 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (1 ≤ count1553 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (2 ≤ count1553 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (1 ≤ count1555 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (2 ≤ count1555 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (3 ≤ count1555 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (4 ≤ count1555 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (1 ≤ count1559 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (2 ≤ count1559 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (3 ≤ count1559 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (4 ≤ count1559 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (5 ≤ count1559 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (3 ≤ count1566 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (4 ≤ count1566 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (5 ≤ count1566 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (6 ≤ count1566 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (7 ≤ count1566 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (8 ≤ count1566 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (9 ≤ count1566 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (1 ≤ count1582 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (2 ≤ count1582 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (3 ≤ count1582 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (1 ≤ count1585 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (2 ≤ count1585 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (1 ≤ count1587 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (2 ≤ count1587 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (1 ≤ count1589 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (2 ≤ count1589 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (3 ≤ count1589 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (4 ≤ count1589 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (1 ≤ count1593 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (2 ≤ count1593 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (3 ≤ count1593 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (4 ≤ count1593 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (5 ≤ count1593 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (1 ≤ count1600 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (2 ≤ count1600 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (1 ≤ count1602 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (2 ≤ count1602 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (1 ≤ count1604 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (2 ≤ count1604 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (3 ≤ count1604 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (1 ≤ count1608 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (2 ≤ count1608 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (1 ≤ count1610 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (2 ≤ count1610 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (1 ≤ count1612 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (2 ≤ count1612 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (3 ≤ count1612 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (1 ≤ count1616 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (2 ≤ count1616 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (3 ≤ count1616 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (4 ≤ count1616 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (2 ≤ count1624 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (3 ≤ count1624 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (4 ≤ count1624 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (5 ≤ count1624 (baseVal q)) := rfl
theorem value1629 (q : Snake 81) : valuation q 1629 = decide (6 ≤ count1624 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (7 ≤ count1624 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (8 ≤ count1639 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (9 ≤ count1639 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (10 ≤ count1639 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (11 ≤ count1639 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (12 ≤ count1639 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (13 ≤ count1639 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (17 ≤ count1656 (baseVal q)) := rfl
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
theorem meaningNeg106 (b : Nat → Bool) : literal (valuationOf b) (-106) = decide (1 ≤ countLit b [-106]) := by
  change literal b (-106) = decide (1 ≤ countLit b [-106])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-106) <;> decide
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
theorem meaningNeg102 (b : Nat → Bool) : literal (valuationOf b) (-102) = decide (1 ≤ countLit b [-102]) := by
  change literal b (-102) = decide (1 ≤ countLit b [-102])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-102) <;> decide
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
theorem meaningNeg66 (b : Nat → Bool) : literal (valuationOf b) (-66) = decide (1 ≤ countLit b [-66]) := by
  change literal b (-66) = decide (1 ≤ countLit b [-66])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-66) <;> decide
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
theorem meaning120 (b : Nat → Bool) : literal (valuationOf b) (120) = decide (1 ≤ countLit b [120]) := by
  change literal b (120) = decide (1 ≤ countLit b [120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (120) <;> decide
theorem meaning142 (b : Nat → Bool) : literal (valuationOf b) (142) = decide (1 ≤ countLit b [142]) := by
  change literal b (142) = decide (1 ≤ countLit b [142])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (142) <;> decide
theorem meaning150 (b : Nat → Bool) : literal (valuationOf b) (150) = decide (1 ≤ countLit b [150]) := by
  change literal b (150) = decide (1 ≤ countLit b [150])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (150) <;> decide
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
theorem meaning176 (b : Nat → Bool) : literal (valuationOf b) (176) = decide (1 ≤ countLit b [176]) := by
  change literal b (176) = decide (1 ≤ countLit b [176])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (176) <;> decide
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
theorem meaning190 (b : Nat → Bool) : literal (valuationOf b) (190) = decide (1 ≤ countLit b [190]) := by
  change literal b (190) = decide (1 ≤ countLit b [190])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (190) <;> decide
theorem meaning191 (b : Nat → Bool) : literal (valuationOf b) (191) = decide (1 ≤ countLit b [191]) := by
  change literal b (191) = decide (1 ≤ countLit b [191])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (191) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
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
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) (223) = decide (1 ≤ countLit b [223]) := by
  change literal b (223) = decide (1 ≤ countLit b [223])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (223) <;> decide
theorem meaning224 (b : Nat → Bool) : literal (valuationOf b) (224) = decide (1 ≤ countLit b [224]) := by
  change literal b (224) = decide (1 ≤ countLit b [224])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (224) <;> decide
theorem meaning226 (b : Nat → Bool) : literal (valuationOf b) (226) = decide (1 ≤ countLit b [226]) := by
  change literal b (226) = decide (1 ≤ countLit b [226])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (226) <;> decide
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) (232) = decide (1 ≤ countLit b [232]) := by
  change literal b (232) = decide (1 ≤ countLit b [232])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (232) <;> decide
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning370 (b : Nat → Bool) : literal (valuationOf b) 370 = decide (2 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning454 (b : Nat → Bool) : literal (valuationOf b) 454 = decide (2 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning456 (b : Nat → Bool) : literal (valuationOf b) 456 = decide (2 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning458 (b : Nat → Bool) : literal (valuationOf b) 458 = decide (2 ≤ count457 b) := rfl
theorem meaning460 (b : Nat → Bool) : literal (valuationOf b) 460 = decide (2 ≤ count459 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (1 ≤ count1401 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (1 ≤ count1403 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (1 ≤ count1406 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (2 ≤ count1406 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (1 ≤ count1408 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (2 ≤ count1408 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (1 ≤ count1410 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (2 ≤ count1410 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (3 ≤ count1410 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (1 ≤ count1414 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (2 ≤ count1414 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (3 ≤ count1414 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (4 ≤ count1414 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (1 ≤ count1421 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (1 ≤ count1423 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (2 ≤ count1423 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (1 ≤ count1426 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (2 ≤ count1426 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (1 ≤ count1428 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (2 ≤ count1428 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (1 ≤ count1430 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (2 ≤ count1430 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (3 ≤ count1430 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (1 ≤ count1434 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (2 ≤ count1434 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (3 ≤ count1434 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (4 ≤ count1434 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (1 ≤ count1441 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (2 ≤ count1441 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (3 ≤ count1441 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (4 ≤ count1441 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (5 ≤ count1441 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (1 ≤ count1455 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (2 ≤ count1455 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (1 ≤ count1457 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (2 ≤ count1457 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (1 ≤ count1460 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (1 ≤ count1462 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (2 ≤ count1462 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (1 ≤ count1464 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (2 ≤ count1464 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (3 ≤ count1464 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (1 ≤ count1468 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (2 ≤ count1468 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (3 ≤ count1468 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (4 ≤ count1468 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (1 ≤ count1475 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (2 ≤ count1475 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (1 ≤ count1477 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (2 ≤ count1477 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (3 ≤ count1477 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (1 ≤ count1480 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (2 ≤ count1480 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (1 ≤ count1482 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (2 ≤ count1482 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (1 ≤ count1484 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (2 ≤ count1484 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (3 ≤ count1484 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (1 ≤ count1488 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (2 ≤ count1488 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (3 ≤ count1488 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (4 ≤ count1488 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (2 ≤ count1495 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (3 ≤ count1495 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (4 ≤ count1495 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (5 ≤ count1495 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (6 ≤ count1495 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (4 ≤ count1509 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (5 ≤ count1509 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (6 ≤ count1509 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (7 ≤ count1509 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (8 ≤ count1509 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (9 ≤ count1509 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (1 ≤ count1526 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (2 ≤ count1526 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (1 ≤ count1528 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (2 ≤ count1528 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (3 ≤ count1528 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (1 ≤ count1531 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (2 ≤ count1531 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (1 ≤ count1533 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (2 ≤ count1533 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (1 ≤ count1535 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (2 ≤ count1535 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (3 ≤ count1535 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (4 ≤ count1535 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (1 ≤ count1539 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (2 ≤ count1539 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (3 ≤ count1539 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (4 ≤ count1539 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (5 ≤ count1539 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (6 ≤ count1539 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (7 ≤ count1539 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (1 ≤ count1546 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (2 ≤ count1546 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (1 ≤ count1548 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (2 ≤ count1548 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (3 ≤ count1548 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (2 ≤ count1551 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (1 ≤ count1553 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (2 ≤ count1553 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (1 ≤ count1555 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (2 ≤ count1555 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (3 ≤ count1555 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (4 ≤ count1555 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (1 ≤ count1559 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (2 ≤ count1559 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (3 ≤ count1559 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (4 ≤ count1559 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (5 ≤ count1559 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (3 ≤ count1566 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (4 ≤ count1566 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (5 ≤ count1566 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (6 ≤ count1566 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (7 ≤ count1566 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (8 ≤ count1566 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (9 ≤ count1566 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (1 ≤ count1582 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (2 ≤ count1582 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (3 ≤ count1582 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (1 ≤ count1585 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (2 ≤ count1585 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (1 ≤ count1587 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (2 ≤ count1587 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (1 ≤ count1589 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (2 ≤ count1589 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (3 ≤ count1589 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (4 ≤ count1589 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (1 ≤ count1593 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (2 ≤ count1593 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (3 ≤ count1593 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (4 ≤ count1593 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (5 ≤ count1593 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (1 ≤ count1600 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (2 ≤ count1600 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (1 ≤ count1602 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (2 ≤ count1602 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (1 ≤ count1604 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (2 ≤ count1604 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (3 ≤ count1604 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (1 ≤ count1608 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (2 ≤ count1608 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (1 ≤ count1610 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (2 ≤ count1610 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (1 ≤ count1612 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (2 ≤ count1612 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (3 ≤ count1612 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (1 ≤ count1616 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (2 ≤ count1616 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (3 ≤ count1616 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (4 ≤ count1616 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (2 ≤ count1624 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (3 ≤ count1624 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (4 ≤ count1624 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (5 ≤ count1624 b) := rfl
theorem meaning1629 (b : Nat → Bool) : literal (valuationOf b) 1629 = decide (6 ≤ count1624 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (7 ≤ count1624 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (8 ≤ count1639 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (9 ≤ count1639 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (10 ≤ count1639 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (11 ≤ count1639 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (12 ≤ count1639 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (13 ≤ count1639 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (17 ≤ count1656 b) := rfl
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
end Snake9.Regrowth.E112120
