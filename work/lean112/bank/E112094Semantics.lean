import E112094Data
namespace Snake9.Regrowth.E112094
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 104 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (18 : Vertex)) else decide (InPath q (20 : Vertex)))) else (if i < 4 then decide (InPath q (22 : Vertex)) else (if i < 5 then decide (InPath q (24 : Vertex)) else decide (InPath q (26 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (28 : Vertex)) else (if i < 8 then decide (InPath q (66 : Vertex)) else decide (InPath q (69 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (70 : Vertex)) else decide (InPath q (71 : Vertex))) else (if i < 12 then decide (InPath q (72 : Vertex)) else decide (InPath q (73 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (74 : Vertex)) else (if i < 15 then decide (InPath q (78 : Vertex)) else decide (InPath q (82 : Vertex)))) else (if i < 17 then decide (InPath q (83 : Vertex)) else (if i < 18 then decide (InPath q (84 : Vertex)) else decide (InPath q (85 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (89 : Vertex)) else (if i < 21 then decide (InPath q (91 : Vertex)) else decide (InPath q (92 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (93 : Vertex)) else decide (InPath q (130 : Vertex))) else (if i < 25 then decide (InPath q (133 : Vertex)) else decide (InPath q (134 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (135 : Vertex)) else (if i < 28 then decide (InPath q (136 : Vertex)) else decide (InPath q (137 : Vertex)))) else (if i < 30 then decide (InPath q (138 : Vertex)) else (if i < 31 then decide (InPath q (142 : Vertex)) else decide (InPath q (146 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (147 : Vertex)) else (if i < 34 then decide (InPath q (148 : Vertex)) else decide (InPath q (149 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (153 : Vertex)) else decide (InPath q (155 : Vertex))) else (if i < 38 then decide (InPath q (156 : Vertex)) else decide (InPath q (157 : Vertex)))))) else (if i < 45 then (if i < 42 then (if i < 40 then decide (InPath q (226 : Vertex)) else (if i < 41 then decide (InPath q (229 : Vertex)) else decide (InPath q (230 : Vertex)))) else (if i < 43 then decide (InPath q (231 : Vertex)) else (if i < 44 then decide (InPath q (232 : Vertex)) else decide (InPath q (233 : Vertex))))) else (if i < 48 then (if i < 46 then decide (InPath q (234 : Vertex)) else (if i < 47 then decide (InPath q (238 : Vertex)) else decide (InPath q (242 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (243 : Vertex)) else decide (InPath q (244 : Vertex))) else (if i < 51 then decide (InPath q (245 : Vertex)) else decide (InPath q (249 : Vertex)))))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then decide (InPath q (251 : Vertex)) else (if i < 54 then decide (InPath q (252 : Vertex)) else decide (InPath q (253 : Vertex)))) else (if i < 56 then decide (InPath q (289 : Vertex)) else (if i < 57 then decide (InPath q (291 : Vertex)) else decide (InPath q (307 : Vertex))))) else (if i < 61 then (if i < 59 then decide (InPath q (354 : Vertex)) else (if i < 60 then decide (InPath q (357 : Vertex)) else decide (InPath q (358 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (359 : Vertex)) else decide (InPath q (360 : Vertex))) else (if i < 64 then decide (InPath q (361 : Vertex)) else decide (InPath q (362 : Vertex)))))) else (if i < 71 then (if i < 68 then (if i < 66 then decide (InPath q (370 : Vertex)) else (if i < 67 then decide (InPath q (371 : Vertex)) else decide (InPath q (372 : Vertex)))) else (if i < 69 then decide (InPath q (373 : Vertex)) else (if i < 70 then decide (InPath q (377 : Vertex)) else decide (InPath q (379 : Vertex))))) else (if i < 74 then (if i < 72 then decide (InPath q (380 : Vertex)) else (if i < 73 then decide (InPath q (384 : Vertex)) else decide (InPath q (385 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (387 : Vertex)) else decide (InPath q (393 : Vertex))) else (if i < 77 then decide (InPath q (395 : Vertex)) else decide (InPath q (397 : Vertex))))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then decide (InPath q (398 : Vertex)) else (if i < 80 then decide (InPath q (399 : Vertex)) else decide (InPath q (400 : Vertex)))) else (if i < 82 then decide (InPath q (402 : Vertex)) else (if i < 83 then decide (InPath q (403 : Vertex)) else decide (InPath q (404 : Vertex))))) else (if i < 87 then (if i < 85 then decide (InPath q (406 : Vertex)) else (if i < 86 then decide (InPath q (408 : Vertex)) else decide (InPath q (410 : Vertex)))) else (if i < 89 then (if i < 88 then decide (InPath q (412 : Vertex)) else decide (InPath q (413 : Vertex))) else (if i < 90 then decide (InPath q (414 : Vertex)) else decide (InPath q (450 : Vertex)))))) else (if i < 97 then (if i < 94 then (if i < 92 then decide (InPath q (456 : Vertex)) else (if i < 93 then decide (InPath q (457 : Vertex)) else decide (InPath q (458 : Vertex)))) else (if i < 95 then decide (InPath q (462 : Vertex)) else (if i < 96 then decide (InPath q (466 : Vertex)) else decide (InPath q (473 : Vertex))))) else (if i < 100 then (if i < 98 then decide (InPath q (475 : Vertex)) else (if i < 99 then decide (InPath q (476 : Vertex)) else decide (InPath q (477 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (498 : Vertex)) else decide (InPath q (502 : Vertex))) else (if i < 103 then decide (InPath q (504 : Vertex)) else decide (InPath q (506 : Vertex))))))))) else (if i < 156 then (if i < 130 then (if i < 117 then (if i < 110 then (if i < 107 then (if i < 105 then decide (InPath q (508 : Vertex)) else (if i < 106 then decide (BallClauseLogic.Endpoint q (18 : Vertex)) else decide (BallClauseLogic.Endpoint q (20 : Vertex)))) else (if i < 108 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else (if i < 109 then decide (BallClauseLogic.Endpoint q (24 : Vertex)) else decide (BallClauseLogic.Endpoint q (26 : Vertex))))) else (if i < 113 then (if i < 111 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else decide (BallClauseLogic.Endpoint q (69 : Vertex)))) else (if i < 115 then (if i < 114 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (71 : Vertex))) else (if i < 116 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else decide (BallClauseLogic.Endpoint q (73 : Vertex)))))) else (if i < 123 then (if i < 120 then (if i < 118 then decide (BallClauseLogic.Endpoint q (74 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (78 : Vertex)) else decide (BallClauseLogic.Endpoint q (82 : Vertex)))) else (if i < 121 then decide (BallClauseLogic.Endpoint q (83 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (85 : Vertex))))) else (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (89 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (91 : Vertex)) else decide (BallClauseLogic.Endpoint q (92 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (93 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex))))))) else (if i < 143 then (if i < 136 then (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (136 : Vertex)) else decide (BallClauseLogic.Endpoint q (137 : Vertex)))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else (if i < 135 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (146 : Vertex))))) else (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (147 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (149 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (153 : Vertex)) else decide (BallClauseLogic.Endpoint q (155 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (156 : Vertex)) else decide (BallClauseLogic.Endpoint q (157 : Vertex)))))) else (if i < 149 then (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex)))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (231 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (232 : Vertex)) else decide (BallClauseLogic.Endpoint q (233 : Vertex))))) else (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (234 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else decide (BallClauseLogic.Endpoint q (242 : Vertex)))) else (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (243 : Vertex)) else decide (BallClauseLogic.Endpoint q (244 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (249 : Vertex)))))))) else (if i < 182 then (if i < 169 then (if i < 162 then (if i < 159 then (if i < 157 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (252 : Vertex)) else decide (BallClauseLogic.Endpoint q (253 : Vertex)))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (289 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (291 : Vertex)) else decide (BallClauseLogic.Endpoint q (307 : Vertex))))) else (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (354 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else decide (BallClauseLogic.Endpoint q (358 : Vertex)))) else (if i < 167 then (if i < 166 then decide (BallClauseLogic.Endpoint q (359 : Vertex)) else decide (BallClauseLogic.Endpoint q (360 : Vertex))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (361 : Vertex)) else decide (BallClauseLogic.Endpoint q (362 : Vertex)))))) else (if i < 175 then (if i < 172 then (if i < 170 then decide (BallClauseLogic.Endpoint q (370 : Vertex)) else (if i < 171 then decide (BallClauseLogic.Endpoint q (371 : Vertex)) else decide (BallClauseLogic.Endpoint q (372 : Vertex)))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (373 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (377 : Vertex)) else decide (BallClauseLogic.Endpoint q (379 : Vertex))))) else (if i < 178 then (if i < 176 then decide (BallClauseLogic.Endpoint q (380 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (384 : Vertex)) else decide (BallClauseLogic.Endpoint q (385 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (393 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (395 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex))))))) else (if i < 195 then (if i < 188 then (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (398 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (399 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex)))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (404 : Vertex))))) else (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (408 : Vertex)) else decide (BallClauseLogic.Endpoint q (410 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else decide (BallClauseLogic.Endpoint q (450 : Vertex)))))) else (if i < 202 then (if i < 198 then (if i < 196 then decide (BallClauseLogic.Endpoint q (456 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else decide (BallClauseLogic.Endpoint q (458 : Vertex)))) else (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (466 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (473 : Vertex)) else decide (BallClauseLogic.Endpoint q (475 : Vertex))))) else (if i < 205 then (if i < 203 then decide (BallClauseLogic.Endpoint q (476 : Vertex)) else (if i < 204 then decide (BallClauseLogic.Endpoint q (477 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (502 : Vertex)) else decide (BallClauseLogic.Endpoint q (504 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count209 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count211 (b : Nat → Bool) : Nat := countLit b [105, 106, 107]
def count213 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count215 (b : Nat → Bool) : Nat := countLit b [108, 109, 110]
def count217 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110]
def count219 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count221 (b : Nat → Bool) : Nat := countLit b [111, 112, 113]
def count223 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count225 (b : Nat → Bool) : Nat := countLit b [114, 115, 116]
def count227 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116]
def count229 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116]
def count231 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [117, 118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count237 (b : Nat → Bool) : Nat := countLit b [120, 121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122]
def count241 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124, 125]
def count245 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127, 128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129]
def count257 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [130, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count275 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count309 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count335 (b : Nat → Bool) : Nat := countLit b [170, 171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [173, 174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count349 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count375 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count377 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192, 193, 194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count395 (b : Nat → Bool) : Nat := countLit b [202, 203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count399 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count401 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count403 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count409 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count411 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count413 (b : Nat → Bool) : Nat := countLit b [2, 4]
def count415 (b : Nat → Bool) : Nat := countLit b [1, 2, 4]
def count418 (b : Nat → Bool) : Nat := countLit b [10, 11]
def count420 (b : Nat → Bool) : Nat := countLit b [7, 10, 11]
def count423 (b : Nat → Bool) : Nat := countLit b [1, 2, 4, 7, 10, 11]
def count429 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count431 (b : Nat → Bool) : Nat := countLit b [14, 16, 18]
def count434 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count436 (b : Nat → Bool) : Nat := countLit b [19, 21, 23]
def count439 (b : Nat → Bool) : Nat := countLit b [14, 16, 18, 19, 21, 23]
def count445 (b : Nat → Bool) : Nat := countLit b [1, 2, 4, 7, 10, 11, 14, 16, 18, 19, 21, 23]
def count457 (b : Nat → Bool) : Nat := countLit b [27, 30]
def count459 (b : Nat → Bool) : Nat := countLit b [26, 27, 30]
def count462 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count464 (b : Nat → Bool) : Nat := countLit b [32, 34, 35]
def count467 (b : Nat → Bool) : Nat := countLit b [26, 27, 30, 32, 34, 35]
def count473 (b : Nat → Bool) : Nat := countLit b [39, 42]
def count475 (b : Nat → Bool) : Nat := countLit b [37, 39, 42]
def count478 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count480 (b : Nat → Bool) : Nat := countLit b [48, 50]
def count482 (b : Nat → Bool) : Nat := countLit b [43, 46, 48, 50]
def count486 (b : Nat → Bool) : Nat := countLit b [37, 39, 42, 43, 46, 48, 50]
def count493 (b : Nat → Bool) : Nat := countLit b [26, 27, 30, 32, 34, 35, 37, 39, 42, 43, 46, 48, 50]
def count506 (b : Nat → Bool) : Nat := countLit b [1, 2, 4, 7, 10, 11, 14, 16, 18, 19, 21, 23, 26, 27, 30, 32, 34, 35, 37, 39, 42, 43, 46, 48, 50]
def count531 (b : Nat → Bool) : Nat := countLit b [53, 56]
def count533 (b : Nat → Bool) : Nat := countLit b [51, 53, 56]
def count536 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count538 (b : Nat → Bool) : Nat := countLit b [58, 61, 62]
def count541 (b : Nat → Bool) : Nat := countLit b [51, 53, 56, 58, 61, 62]
def count547 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count549 (b : Nat → Bool) : Nat := countLit b [66, 68, 69]
def count552 (b : Nat → Bool) : Nat := countLit b [71, 72]
def count554 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count556 (b : Nat → Bool) : Nat := countLit b [71, 72, 74, 75]
def count560 (b : Nat → Bool) : Nat := countLit b [66, 68, 69, 71, 72, 74, 75]
def count567 (b : Nat → Bool) : Nat := countLit b [51, 53, 56, 58, 61, 62, 66, 68, 69, 71, 72, 74, 75]
def count580 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count582 (b : Nat → Bool) : Nat := countLit b [79, 81, 83]
def count585 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count587 (b : Nat → Bool) : Nat := countLit b [85, 88, 89]
def count590 (b : Nat → Bool) : Nat := countLit b [79, 81, 83, 85, 88, 89]
def count596 (b : Nat → Bool) : Nat := countLit b [91, 94]
def count598 (b : Nat → Bool) : Nat := countLit b [90, 91, 94]
def count601 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count603 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count605 (b : Nat → Bool) : Nat := countLit b [96, 98, 100, 102]
def count609 (b : Nat → Bool) : Nat := countLit b [90, 91, 94, 96, 98, 100, 102]
def count616 (b : Nat → Bool) : Nat := countLit b [79, 81, 83, 85, 88, 89, 90, 91, 94, 96, 98, 100, 102]
def count629 (b : Nat → Bool) : Nat := countLit b [51, 53, 56, 58, 61, 62, 66, 68, 69, 71, 72, 74, 75, 79, 81, 83, 85, 88, 89, 90, 91, 94, 96, 98, 100, 102]
def count655 (b : Nat → Bool) : Nat := countLit b [1, 2, 4, 7, 10, 11, 14, 16, 18, 19, 21, 23, 26, 27, 30, 32, 34, 35, 37, 39, 42, 43, 46, 48, 50, 51, 53, 56, 58, 61, 62, 66, 68, 69, 71, 72, 74, 75, 79, 81, 83, 85, 88, 89, 90, 91, 94, 96, 98, 100, 102]
def count697 (b : Nat → Bool) : Nat := countLit b [-2, -4]
def count699 (b : Nat → Bool) : Nat := countLit b [-1, -2, -4]
def count702 (b : Nat → Bool) : Nat := countLit b [-10, -11]
def count704 (b : Nat → Bool) : Nat := countLit b [-7, -10, -11]
def count707 (b : Nat → Bool) : Nat := countLit b [-1, -2, -4, -7, -10, -11]
def count713 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count715 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18]
def count718 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count720 (b : Nat → Bool) : Nat := countLit b [-19, -21, -23]
def count723 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18, -19, -21, -23]
def count729 (b : Nat → Bool) : Nat := countLit b [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23]
def count740 (b : Nat → Bool) : Nat := countLit b [-27, -30]
def count742 (b : Nat → Bool) : Nat := countLit b [-26, -27, -30]
def count745 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count747 (b : Nat → Bool) : Nat := countLit b [-32, -34, -35]
def count750 (b : Nat → Bool) : Nat := countLit b [-26, -27, -30, -32, -34, -35]
def count756 (b : Nat → Bool) : Nat := countLit b [-39, -42]
def count758 (b : Nat → Bool) : Nat := countLit b [-37, -39, -42]
def count761 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count763 (b : Nat → Bool) : Nat := countLit b [-48, -50]
def count765 (b : Nat → Bool) : Nat := countLit b [-43, -46, -48, -50]
def count769 (b : Nat → Bool) : Nat := countLit b [-37, -39, -42, -43, -46, -48, -50]
def count776 (b : Nat → Bool) : Nat := countLit b [-26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]
def count787 (b : Nat → Bool) : Nat := countLit b [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50]
def count798 (b : Nat → Bool) : Nat := countLit b [-53, -56]
def count800 (b : Nat → Bool) : Nat := countLit b [-51, -53, -56]
def count803 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count805 (b : Nat → Bool) : Nat := countLit b [-58, -61, -62]
def count808 (b : Nat → Bool) : Nat := countLit b [-51, -53, -56, -58, -61, -62]
def count814 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count816 (b : Nat → Bool) : Nat := countLit b [-66, -68, -69]
def count819 (b : Nat → Bool) : Nat := countLit b [-71, -72]
def count821 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count823 (b : Nat → Bool) : Nat := countLit b [-71, -72, -74, -75]
def count827 (b : Nat → Bool) : Nat := countLit b [-66, -68, -69, -71, -72, -74, -75]
def count834 (b : Nat → Bool) : Nat := countLit b [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75]
def count845 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count847 (b : Nat → Bool) : Nat := countLit b [-79, -81, -83]
def count850 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count852 (b : Nat → Bool) : Nat := countLit b [-85, -88, -89]
def count855 (b : Nat → Bool) : Nat := countLit b [-79, -81, -83, -85, -88, -89]
def count861 (b : Nat → Bool) : Nat := countLit b [-91, -94]
def count863 (b : Nat → Bool) : Nat := countLit b [-90, -91, -94]
def count866 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count868 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count870 (b : Nat → Bool) : Nat := countLit b [-96, -98, -100, -102]
def count874 (b : Nat → Bool) : Nat := countLit b [-90, -91, -94, -96, -98, -100, -102]
def count881 (b : Nat → Bool) : Nat := countLit b [-79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]
def count892 (b : Nat → Bool) : Nat := countLit b [-51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]
def count903 (b : Nat → Bool) : Nat := countLit b [-1, -2, -4, -7, -10, -11, -14, -16, -18, -19, -21, -23, -26, -27, -30, -32, -34, -35, -37, -39, -42, -43, -46, -48, -50, -51, -53, -56, -58, -61, -62, -66, -68, -69, -71, -72, -74, -75, -79, -81, -83, -85, -88, -89, -90, -91, -94, -96, -98, -100, -102]
def count914 (b : Nat → Bool) : Nat := countLit b [5, 6]
def count916 (b : Nat → Bool) : Nat := countLit b [3, 5, 6]
def count919 (b : Nat → Bool) : Nat := countLit b [9, 12]
def count921 (b : Nat → Bool) : Nat := countLit b [8, 9, 12]
def count924 (b : Nat → Bool) : Nat := countLit b [3, 5, 6, 8, 9, 12]
def count930 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count932 (b : Nat → Bool) : Nat := countLit b [13, 15, 17]
def count935 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count937 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count939 (b : Nat → Bool) : Nat := countLit b [20, 22, 24, 25]
def count943 (b : Nat → Bool) : Nat := countLit b [13, 15, 17, 20, 22, 24, 25]
def count950 (b : Nat → Bool) : Nat := countLit b [3, 5, 6, 8, 9, 12, 13, 15, 17, 20, 22, 24, 25]
def count963 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count965 (b : Nat → Bool) : Nat := countLit b [28, 29, 31]
def count968 (b : Nat → Bool) : Nat := countLit b [36, 38]
def count970 (b : Nat → Bool) : Nat := countLit b [33, 36, 38]
def count973 (b : Nat → Bool) : Nat := countLit b [28, 29, 31, 33, 36, 38]
def count979 (b : Nat → Bool) : Nat := countLit b [41, 44]
def count981 (b : Nat → Bool) : Nat := countLit b [40, 41, 44]
def count984 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count986 (b : Nat → Bool) : Nat := countLit b [49, 52]
def count988 (b : Nat → Bool) : Nat := countLit b [45, 47, 49, 52]
def count992 (b : Nat → Bool) : Nat := countLit b [40, 41, 44, 45, 47, 49, 52]
def count999 (b : Nat → Bool) : Nat := countLit b [28, 29, 31, 33, 36, 38, 40, 41, 44, 45, 47, 49, 52]
def count1012 (b : Nat → Bool) : Nat := countLit b [3, 5, 6, 8, 9, 12, 13, 15, 17, 20, 22, 24, 25, 28, 29, 31, 33, 36, 38, 40, 41, 44, 45, 47, 49, 52]
def count1038 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count1040 (b : Nat → Bool) : Nat := countLit b [54, 55, 57]
def count1043 (b : Nat → Bool) : Nat := countLit b [60, 63]
def count1045 (b : Nat → Bool) : Nat := countLit b [59, 60, 63]
def count1048 (b : Nat → Bool) : Nat := countLit b [54, 55, 57, 59, 60, 63]
def count1054 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count1056 (b : Nat → Bool) : Nat := countLit b [64, 65, 67]
def count1059 (b : Nat → Bool) : Nat := countLit b [70, 73]
def count1061 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count1063 (b : Nat → Bool) : Nat := countLit b [70, 73, 76, 77]
def count1067 (b : Nat → Bool) : Nat := countLit b [64, 65, 67, 70, 73, 76, 77]
def count1074 (b : Nat → Bool) : Nat := countLit b [54, 55, 57, 59, 60, 63, 64, 65, 67, 70, 73, 76, 77]
def count1087 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count1089 (b : Nat → Bool) : Nat := countLit b [78, 80, 82]
def count1092 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count1094 (b : Nat → Bool) : Nat := countLit b [87, 92]
def count1096 (b : Nat → Bool) : Nat := countLit b [84, 86, 87, 92]
def count1100 (b : Nat → Bool) : Nat := countLit b [78, 80, 82, 84, 86, 87, 92]
def count1107 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count1109 (b : Nat → Bool) : Nat := countLit b [93, 95, 97]
def count1112 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count1114 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count1116 (b : Nat → Bool) : Nat := countLit b [99, 101, 103, 104]
def count1120 (b : Nat → Bool) : Nat := countLit b [93, 95, 97, 99, 101, 103, 104]
def count1127 (b : Nat → Bool) : Nat := countLit b [78, 80, 82, 84, 86, 87, 92, 93, 95, 97, 99, 101, 103, 104]
def count1141 (b : Nat → Bool) : Nat := countLit b [54, 55, 57, 59, 60, 63, 64, 65, 67, 70, 73, 76, 77, 78, 80, 82, 84, 86, 87, 92, 93, 95, 97, 99, 101, 103, 104]
def count1168 (b : Nat → Bool) : Nat := countLit b [3, 5, 6, 8, 9, 12, 13, 15, 17, 20, 22, 24, 25, 28, 29, 31, 33, 36, 38, 40, 41, 44, 45, 47, 49, 52, 54, 55, 57, 59, 60, 63, 64, 65, 67, 70, 73, 76, 77, 78, 80, 82, 84, 86, 87, 92, 93, 95, 97, 99, 101, 103, 104]
def count1210 (b : Nat → Bool) : Nat := countLit b [-5, -6]
def count1212 (b : Nat → Bool) : Nat := countLit b [-3, -5, -6]
def count1215 (b : Nat → Bool) : Nat := countLit b [-9, -12]
def count1217 (b : Nat → Bool) : Nat := countLit b [-8, -9, -12]
def count1220 (b : Nat → Bool) : Nat := countLit b [-3, -5, -6, -8, -9, -12]
def count1226 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count1228 (b : Nat → Bool) : Nat := countLit b [-13, -15, -17]
def count1231 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count1233 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1235 (b : Nat → Bool) : Nat := countLit b [-20, -22, -24, -25]
def count1239 (b : Nat → Bool) : Nat := countLit b [-13, -15, -17, -20, -22, -24, -25]
def count1246 (b : Nat → Bool) : Nat := countLit b [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25]
def count1259 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count1261 (b : Nat → Bool) : Nat := countLit b [-28, -29, -31]
def count1264 (b : Nat → Bool) : Nat := countLit b [-36, -38]
def count1266 (b : Nat → Bool) : Nat := countLit b [-33, -36, -38]
def count1269 (b : Nat → Bool) : Nat := countLit b [-28, -29, -31, -33, -36, -38]
def count1275 (b : Nat → Bool) : Nat := countLit b [-41, -44]
def count1277 (b : Nat → Bool) : Nat := countLit b [-40, -41, -44]
def count1280 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count1282 (b : Nat → Bool) : Nat := countLit b [-49, -52]
def count1284 (b : Nat → Bool) : Nat := countLit b [-45, -47, -49, -52]
def count1288 (b : Nat → Bool) : Nat := countLit b [-40, -41, -44, -45, -47, -49, -52]
def count1295 (b : Nat → Bool) : Nat := countLit b [-28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]
def count1308 (b : Nat → Bool) : Nat := countLit b [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52]
def count1321 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count1323 (b : Nat → Bool) : Nat := countLit b [-54, -55, -57]
def count1326 (b : Nat → Bool) : Nat := countLit b [-60, -63]
def count1328 (b : Nat → Bool) : Nat := countLit b [-59, -60, -63]
def count1331 (b : Nat → Bool) : Nat := countLit b [-54, -55, -57, -59, -60, -63]
def count1337 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count1339 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67]
def count1342 (b : Nat → Bool) : Nat := countLit b [-70, -73]
def count1344 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count1346 (b : Nat → Bool) : Nat := countLit b [-70, -73, -76, -77]
def count1350 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67, -70, -73, -76, -77]
def count1357 (b : Nat → Bool) : Nat := countLit b [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77]
def count1370 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count1372 (b : Nat → Bool) : Nat := countLit b [-78, -80, -82]
def count1375 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count1377 (b : Nat → Bool) : Nat := countLit b [-87, -92]
def count1379 (b : Nat → Bool) : Nat := countLit b [-84, -86, -87, -92]
def count1383 (b : Nat → Bool) : Nat := countLit b [-78, -80, -82, -84, -86, -87, -92]
def count1390 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count1392 (b : Nat → Bool) : Nat := countLit b [-93, -95, -97]
def count1395 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count1397 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1399 (b : Nat → Bool) : Nat := countLit b [-99, -101, -103, -104]
def count1403 (b : Nat → Bool) : Nat := countLit b [-93, -95, -97, -99, -101, -103, -104]
def count1410 (b : Nat → Bool) : Nat := countLit b [-78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]
def count1423 (b : Nat → Bool) : Nat := countLit b [-54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]
def count1436 (b : Nat → Bool) : Nat := countLit b [-3, -5, -6, -8, -9, -12, -13, -15, -17, -20, -22, -24, -25, -28, -29, -31, -33, -36, -38, -40, -41, -44, -45, -47, -49, -52, -54, -55, -57, -59, -60, -63, -64, -65, -67, -70, -73, -76, -77, -78, -80, -82, -84, -86, -87, -92, -93, -95, -97, -99, -101, -103, -104]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 724 then (if i < 362 then (if i < 181 then (if i < 90 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 16 then (if i < 13 then (if i < 12 then b 11 else b 12) else (if i < 14 then b 13 else (if i < 15 then b 14 else b 15))) else (if i < 19 then (if i < 17 then b 16 else (if i < 18 then b 17 else b 18)) else (if i < 20 then b 19 else (if i < 21 then b 20 else b 21))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else (if i < 26 then b 25 else b 26))) else (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)))) else (if i < 39 then (if i < 36 then (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)) else (if i < 37 then b 36 else (if i < 38 then b 37 else b 38))) else (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)))))) else (if i < 67 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else (if i < 49 then b 48 else b 49))) else (if i < 53 then (if i < 51 then b 50 else (if i < 52 then b 51 else b 52)) else (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)))) else (if i < 61 then (if i < 58 then (if i < 57 then b 56 else b 57) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60))) else (if i < 64 then (if i < 62 then b 61 else (if i < 63 then b 62 else b 63)) else (if i < 65 then b 64 else (if i < 66 then b 65 else b 66))))) else (if i < 78 then (if i < 72 then (if i < 69 then (if i < 68 then b 67 else b 68) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))) else (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)))) else (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))))))) else (if i < 135 then (if i < 112 then (if i < 101 then (if i < 95 then (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))) else (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)))) else (if i < 106 then (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else (if i < 105 then b 104 else b 105))) else (if i < 109 then (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111))))) else (if i < 123 then (if i < 117 then (if i < 114 then (if i < 113 then b 112 else b 113) else (if i < 115 then b 114 else (if i < 116 then b 115 else b 116))) else (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)))) else (if i < 129 then (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 127 then b 126 else (if i < 128 then b 127 else b 128))) else (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)))))) else (if i < 158 then (if i < 146 then (if i < 140 then (if i < 137 then (if i < 136 then b 135 else b 136) else (if i < 138 then b 137 else (if i < 139 then b 138 else b 139))) else (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)))) else (if i < 152 then (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 150 then b 149 else (if i < 151 then b 150 else b 151))) else (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 156 then b 155 else (if i < 157 then b 156 else b 157))))) else (if i < 169 then (if i < 163 then (if i < 160 then (if i < 159 then b 158 else b 159) else (if i < 161 then b 160 else (if i < 162 then b 161 else b 162))) else (if i < 166 then (if i < 164 then b 163 else (if i < 165 then b 164 else b 165)) else (if i < 167 then b 166 else (if i < 168 then b 167 else b 168)))) else (if i < 175 then (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174))) else (if i < 178 then (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)) else (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)))))))) else (if i < 271 then (if i < 226 then (if i < 203 then (if i < 192 then (if i < 186 then (if i < 183 then (if i < 182 then b 181 else b 182) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185))) else (if i < 189 then (if i < 187 then b 186 else (if i < 188 then b 187 else b 188)) else (if i < 190 then b 189 else (if i < 191 then b 190 else b 191)))) else (if i < 197 then (if i < 194 then (if i < 193 then b 192 else b 193) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196))) else (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 201 then b 200 else (if i < 202 then b 201 else b 202))))) else (if i < 214 then (if i < 208 then (if i < 205 then (if i < 204 then b 203 else b 204) else (if i < 206 then b 205 else (if i < 207 then b 206 else b 207))) else (if i < 211 then (if i < 209 then b 208 else (if i < 210 then decide (1 ≤ count209 b) else decide (2 ≤ count209 b))) else (if i < 212 then decide (1 ≤ count211 b) else (if i < 213 then decide (2 ≤ count211 b) else decide (1 ≤ count213 b))))) else (if i < 220 then (if i < 217 then (if i < 215 then decide (2 ≤ count213 b) else (if i < 216 then decide (1 ≤ count215 b) else decide (2 ≤ count215 b))) else (if i < 218 then decide (1 ≤ count217 b) else (if i < 219 then decide (2 ≤ count217 b) else decide (1 ≤ count219 b)))) else (if i < 223 then (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b))) else (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b))))))) else (if i < 248 then (if i < 237 then (if i < 231 then (if i < 228 then (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b)) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b)))) else (if i < 234 then (if i < 232 then decide (1 ≤ count231 b) else (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b))) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b))))) else (if i < 242 then (if i < 239 then (if i < 238 then decide (1 ≤ count237 b) else decide (2 ≤ count237 b)) else (if i < 240 then decide (1 ≤ count239 b) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b)))) else (if i < 245 then (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b))) else (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b)))))) else (if i < 259 then (if i < 253 then (if i < 250 then (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b)) else (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)))) else (if i < 256 then (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b))) else (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))))) else (if i < 265 then (if i < 262 then (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))) else (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))) else (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)))))))) else (if i < 316 then (if i < 293 then (if i < 282 then (if i < 276 then (if i < 273 then (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)) else (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)))) else (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))))) else (if i < 287 then (if i < 284 then (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)) else (if i < 285 then decide (2 ≤ count283 b) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))) else (if i < 290 then (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))) else (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))))) else (if i < 304 then (if i < 298 then (if i < 295 then (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)) else (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)))) else (if i < 301 then (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))) else (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))))) else (if i < 310 then (if i < 307 then (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))) else (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)))) else (if i < 313 then (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))) else (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))))))) else (if i < 339 then (if i < 327 then (if i < 321 then (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)))) else (if i < 324 then (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b))) else (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))))) else (if i < 333 then (if i < 330 then (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b))) else (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)))) else (if i < 336 then (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))))) else (if i < 350 then (if i < 344 then (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b)))) else (if i < 347 then (if i < 345 then decide (2 ≤ count343 b) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b))) else (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))))) else (if i < 356 then (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b)))) else (if i < 359 then (if i < 357 then decide (2 ≤ count355 b) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b))) else (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)))))))))) else (if i < 543 then (if i < 452 then (if i < 407 then (if i < 384 then (if i < 373 then (if i < 367 then (if i < 364 then (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)))) else (if i < 370 then (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))) else (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))))) else (if i < 378 then (if i < 375 then (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)) else (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)))) else (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)))))) else (if i < 395 then (if i < 389 then (if i < 386 then (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b))))) else (if i < 401 then (if i < 398 then (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))) else (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)))) else (if i < 404 then (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))))))) else (if i < 429 then (if i < 418 then (if i < 412 then (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b)))) else (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (3 ≤ count415 b))))) else (if i < 423 then (if i < 420 then (if i < 419 then decide (1 ≤ count418 b) else decide (2 ≤ count418 b)) else (if i < 421 then decide (1 ≤ count420 b) else (if i < 422 then decide (2 ≤ count420 b) else decide (3 ≤ count420 b)))) else (if i < 426 then (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (3 ≤ count423 b))) else (if i < 427 then decide (4 ≤ count423 b) else (if i < 428 then decide (5 ≤ count423 b) else decide (6 ≤ count423 b)))))) else (if i < 440 then (if i < 434 then (if i < 431 then (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)) else (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (3 ≤ count431 b)))) else (if i < 437 then (if i < 435 then decide (1 ≤ count434 b) else (if i < 436 then decide (2 ≤ count434 b) else decide (1 ≤ count436 b))) else (if i < 438 then decide (2 ≤ count436 b) else (if i < 439 then decide (3 ≤ count436 b) else decide (1 ≤ count439 b))))) else (if i < 446 then (if i < 443 then (if i < 441 then decide (2 ≤ count439 b) else (if i < 442 then decide (3 ≤ count439 b) else decide (4 ≤ count439 b))) else (if i < 444 then decide (5 ≤ count439 b) else (if i < 445 then decide (6 ≤ count439 b) else decide (1 ≤ count445 b)))) else (if i < 449 then (if i < 447 then decide (2 ≤ count445 b) else (if i < 448 then decide (3 ≤ count445 b) else decide (4 ≤ count445 b))) else (if i < 450 then decide (5 ≤ count445 b) else (if i < 451 then decide (6 ≤ count445 b) else decide (7 ≤ count445 b)))))))) else (if i < 497 then (if i < 474 then (if i < 463 then (if i < 457 then (if i < 454 then (if i < 453 then decide (8 ≤ count445 b) else decide (9 ≤ count445 b)) else (if i < 455 then decide (10 ≤ count445 b) else (if i < 456 then decide (11 ≤ count445 b) else decide (12 ≤ count445 b)))) else (if i < 460 then (if i < 458 then decide (1 ≤ count457 b) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b))) else (if i < 461 then decide (2 ≤ count459 b) else (if i < 462 then decide (3 ≤ count459 b) else decide (1 ≤ count462 b))))) else (if i < 468 then (if i < 465 then (if i < 464 then decide (2 ≤ count462 b) else decide (1 ≤ count464 b)) else (if i < 466 then decide (2 ≤ count464 b) else (if i < 467 then decide (3 ≤ count464 b) else decide (1 ≤ count467 b)))) else (if i < 471 then (if i < 469 then decide (2 ≤ count467 b) else (if i < 470 then decide (3 ≤ count467 b) else decide (4 ≤ count467 b))) else (if i < 472 then decide (5 ≤ count467 b) else (if i < 473 then decide (6 ≤ count467 b) else decide (1 ≤ count473 b)))))) else (if i < 485 then (if i < 479 then (if i < 476 then (if i < 475 then decide (2 ≤ count473 b) else decide (1 ≤ count475 b)) else (if i < 477 then decide (2 ≤ count475 b) else (if i < 478 then decide (3 ≤ count475 b) else decide (1 ≤ count478 b)))) else (if i < 482 then (if i < 480 then decide (2 ≤ count478 b) else (if i < 481 then decide (1 ≤ count480 b) else decide (2 ≤ count480 b))) else (if i < 483 then decide (1 ≤ count482 b) else (if i < 484 then decide (2 ≤ count482 b) else decide (3 ≤ count482 b))))) else (if i < 491 then (if i < 488 then (if i < 486 then decide (4 ≤ count482 b) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b))) else (if i < 489 then decide (3 ≤ count486 b) else (if i < 490 then decide (4 ≤ count486 b) else decide (5 ≤ count486 b)))) else (if i < 494 then (if i < 492 then decide (6 ≤ count486 b) else (if i < 493 then decide (7 ≤ count486 b) else decide (1 ≤ count493 b))) else (if i < 495 then decide (2 ≤ count493 b) else (if i < 496 then decide (3 ≤ count493 b) else decide (4 ≤ count493 b))))))) else (if i < 520 then (if i < 508 then (if i < 502 then (if i < 499 then (if i < 498 then decide (5 ≤ count493 b) else decide (6 ≤ count493 b)) else (if i < 500 then decide (7 ≤ count493 b) else (if i < 501 then decide (8 ≤ count493 b) else decide (9 ≤ count493 b)))) else (if i < 505 then (if i < 503 then decide (10 ≤ count493 b) else (if i < 504 then decide (11 ≤ count493 b) else decide (12 ≤ count493 b))) else (if i < 506 then decide (13 ≤ count493 b) else (if i < 507 then decide (1 ≤ count506 b) else decide (2 ≤ count506 b))))) else (if i < 514 then (if i < 511 then (if i < 509 then decide (3 ≤ count506 b) else (if i < 510 then decide (4 ≤ count506 b) else decide (5 ≤ count506 b))) else (if i < 512 then decide (6 ≤ count506 b) else (if i < 513 then decide (7 ≤ count506 b) else decide (8 ≤ count506 b)))) else (if i < 517 then (if i < 515 then decide (9 ≤ count506 b) else (if i < 516 then decide (10 ≤ count506 b) else decide (11 ≤ count506 b))) else (if i < 518 then decide (12 ≤ count506 b) else (if i < 519 then decide (13 ≤ count506 b) else decide (14 ≤ count506 b)))))) else (if i < 531 then (if i < 525 then (if i < 522 then (if i < 521 then decide (15 ≤ count506 b) else decide (16 ≤ count506 b)) else (if i < 523 then decide (17 ≤ count506 b) else (if i < 524 then decide (18 ≤ count506 b) else decide (19 ≤ count506 b)))) else (if i < 528 then (if i < 526 then decide (20 ≤ count506 b) else (if i < 527 then decide (21 ≤ count506 b) else decide (22 ≤ count506 b))) else (if i < 529 then decide (23 ≤ count506 b) else (if i < 530 then decide (24 ≤ count506 b) else decide (25 ≤ count506 b))))) else (if i < 537 then (if i < 534 then (if i < 532 then decide (1 ≤ count531 b) else (if i < 533 then decide (2 ≤ count531 b) else decide (1 ≤ count533 b))) else (if i < 535 then decide (2 ≤ count533 b) else (if i < 536 then decide (3 ≤ count533 b) else decide (1 ≤ count536 b)))) else (if i < 540 then (if i < 538 then decide (2 ≤ count536 b) else (if i < 539 then decide (1 ≤ count538 b) else decide (2 ≤ count538 b))) else (if i < 541 then decide (3 ≤ count538 b) else (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b))))))))) else (if i < 633 then (if i < 588 then (if i < 565 then (if i < 554 then (if i < 548 then (if i < 545 then (if i < 544 then decide (3 ≤ count541 b) else decide (4 ≤ count541 b)) else (if i < 546 then decide (5 ≤ count541 b) else (if i < 547 then decide (6 ≤ count541 b) else decide (1 ≤ count547 b)))) else (if i < 551 then (if i < 549 then decide (2 ≤ count547 b) else (if i < 550 then decide (1 ≤ count549 b) else decide (2 ≤ count549 b))) else (if i < 552 then decide (3 ≤ count549 b) else (if i < 553 then decide (1 ≤ count552 b) else decide (2 ≤ count552 b))))) else (if i < 559 then (if i < 556 then (if i < 555 then decide (1 ≤ count554 b) else decide (2 ≤ count554 b)) else (if i < 557 then decide (1 ≤ count556 b) else (if i < 558 then decide (2 ≤ count556 b) else decide (3 ≤ count556 b)))) else (if i < 562 then (if i < 560 then decide (4 ≤ count556 b) else (if i < 561 then decide (1 ≤ count560 b) else decide (2 ≤ count560 b))) else (if i < 563 then decide (3 ≤ count560 b) else (if i < 564 then decide (4 ≤ count560 b) else decide (5 ≤ count560 b)))))) else (if i < 576 then (if i < 570 then (if i < 567 then (if i < 566 then decide (6 ≤ count560 b) else decide (7 ≤ count560 b)) else (if i < 568 then decide (1 ≤ count567 b) else (if i < 569 then decide (2 ≤ count567 b) else decide (3 ≤ count567 b)))) else (if i < 573 then (if i < 571 then decide (4 ≤ count567 b) else (if i < 572 then decide (5 ≤ count567 b) else decide (6 ≤ count567 b))) else (if i < 574 then decide (7 ≤ count567 b) else (if i < 575 then decide (8 ≤ count567 b) else decide (9 ≤ count567 b))))) else (if i < 582 then (if i < 579 then (if i < 577 then decide (10 ≤ count567 b) else (if i < 578 then decide (11 ≤ count567 b) else decide (12 ≤ count567 b))) else (if i < 580 then decide (13 ≤ count567 b) else (if i < 581 then decide (1 ≤ count580 b) else decide (2 ≤ count580 b)))) else (if i < 585 then (if i < 583 then decide (1 ≤ count582 b) else (if i < 584 then decide (2 ≤ count582 b) else decide (3 ≤ count582 b))) else (if i < 586 then decide (1 ≤ count585 b) else (if i < 587 then decide (2 ≤ count585 b) else decide (1 ≤ count587 b))))))) else (if i < 610 then (if i < 599 then (if i < 593 then (if i < 590 then (if i < 589 then decide (2 ≤ count587 b) else decide (3 ≤ count587 b)) else (if i < 591 then decide (1 ≤ count590 b) else (if i < 592 then decide (2 ≤ count590 b) else decide (3 ≤ count590 b)))) else (if i < 596 then (if i < 594 then decide (4 ≤ count590 b) else (if i < 595 then decide (5 ≤ count590 b) else decide (6 ≤ count590 b))) else (if i < 597 then decide (1 ≤ count596 b) else (if i < 598 then decide (2 ≤ count596 b) else decide (1 ≤ count598 b))))) else (if i < 604 then (if i < 601 then (if i < 600 then decide (2 ≤ count598 b) else decide (3 ≤ count598 b)) else (if i < 602 then decide (1 ≤ count601 b) else (if i < 603 then decide (2 ≤ count601 b) else decide (1 ≤ count603 b)))) else (if i < 607 then (if i < 605 then decide (2 ≤ count603 b) else (if i < 606 then decide (1 ≤ count605 b) else decide (2 ≤ count605 b))) else (if i < 608 then decide (3 ≤ count605 b) else (if i < 609 then decide (4 ≤ count605 b) else decide (1 ≤ count609 b)))))) else (if i < 621 then (if i < 615 then (if i < 612 then (if i < 611 then decide (2 ≤ count609 b) else decide (3 ≤ count609 b)) else (if i < 613 then decide (4 ≤ count609 b) else (if i < 614 then decide (5 ≤ count609 b) else decide (6 ≤ count609 b)))) else (if i < 618 then (if i < 616 then decide (7 ≤ count609 b) else (if i < 617 then decide (1 ≤ count616 b) else decide (2 ≤ count616 b))) else (if i < 619 then decide (3 ≤ count616 b) else (if i < 620 then decide (4 ≤ count616 b) else decide (5 ≤ count616 b))))) else (if i < 627 then (if i < 624 then (if i < 622 then decide (6 ≤ count616 b) else (if i < 623 then decide (7 ≤ count616 b) else decide (8 ≤ count616 b))) else (if i < 625 then decide (9 ≤ count616 b) else (if i < 626 then decide (10 ≤ count616 b) else decide (11 ≤ count616 b)))) else (if i < 630 then (if i < 628 then decide (12 ≤ count616 b) else (if i < 629 then decide (13 ≤ count616 b) else decide (1 ≤ count629 b))) else (if i < 631 then decide (2 ≤ count629 b) else (if i < 632 then decide (3 ≤ count629 b) else decide (4 ≤ count629 b)))))))) else (if i < 678 then (if i < 655 then (if i < 644 then (if i < 638 then (if i < 635 then (if i < 634 then decide (5 ≤ count629 b) else decide (6 ≤ count629 b)) else (if i < 636 then decide (7 ≤ count629 b) else (if i < 637 then decide (8 ≤ count629 b) else decide (9 ≤ count629 b)))) else (if i < 641 then (if i < 639 then decide (10 ≤ count629 b) else (if i < 640 then decide (11 ≤ count629 b) else decide (12 ≤ count629 b))) else (if i < 642 then decide (13 ≤ count629 b) else (if i < 643 then decide (14 ≤ count629 b) else decide (15 ≤ count629 b))))) else (if i < 649 then (if i < 646 then (if i < 645 then decide (16 ≤ count629 b) else decide (17 ≤ count629 b)) else (if i < 647 then decide (18 ≤ count629 b) else (if i < 648 then decide (19 ≤ count629 b) else decide (20 ≤ count629 b)))) else (if i < 652 then (if i < 650 then decide (21 ≤ count629 b) else (if i < 651 then decide (22 ≤ count629 b) else decide (23 ≤ count629 b))) else (if i < 653 then decide (24 ≤ count629 b) else (if i < 654 then decide (25 ≤ count629 b) else decide (26 ≤ count629 b)))))) else (if i < 666 then (if i < 660 then (if i < 657 then (if i < 656 then decide (1 ≤ count655 b) else decide (2 ≤ count655 b)) else (if i < 658 then decide (3 ≤ count655 b) else (if i < 659 then decide (4 ≤ count655 b) else decide (5 ≤ count655 b)))) else (if i < 663 then (if i < 661 then decide (6 ≤ count655 b) else (if i < 662 then decide (7 ≤ count655 b) else decide (8 ≤ count655 b))) else (if i < 664 then decide (9 ≤ count655 b) else (if i < 665 then decide (10 ≤ count655 b) else decide (11 ≤ count655 b))))) else (if i < 672 then (if i < 669 then (if i < 667 then decide (12 ≤ count655 b) else (if i < 668 then decide (13 ≤ count655 b) else decide (14 ≤ count655 b))) else (if i < 670 then decide (15 ≤ count655 b) else (if i < 671 then decide (16 ≤ count655 b) else decide (17 ≤ count655 b)))) else (if i < 675 then (if i < 673 then decide (18 ≤ count655 b) else (if i < 674 then decide (19 ≤ count655 b) else decide (20 ≤ count655 b))) else (if i < 676 then decide (21 ≤ count655 b) else (if i < 677 then decide (22 ≤ count655 b) else decide (23 ≤ count655 b))))))) else (if i < 701 then (if i < 689 then (if i < 683 then (if i < 680 then (if i < 679 then decide (24 ≤ count655 b) else decide (25 ≤ count655 b)) else (if i < 681 then decide (26 ≤ count655 b) else (if i < 682 then decide (27 ≤ count655 b) else decide (28 ≤ count655 b)))) else (if i < 686 then (if i < 684 then decide (29 ≤ count655 b) else (if i < 685 then decide (30 ≤ count655 b) else decide (31 ≤ count655 b))) else (if i < 687 then decide (32 ≤ count655 b) else (if i < 688 then decide (33 ≤ count655 b) else decide (34 ≤ count655 b))))) else (if i < 695 then (if i < 692 then (if i < 690 then decide (35 ≤ count655 b) else (if i < 691 then decide (36 ≤ count655 b) else decide (37 ≤ count655 b))) else (if i < 693 then decide (38 ≤ count655 b) else (if i < 694 then decide (39 ≤ count655 b) else decide (40 ≤ count655 b)))) else (if i < 698 then (if i < 696 then decide (41 ≤ count655 b) else (if i < 697 then decide (42 ≤ count655 b) else decide (1 ≤ count697 b))) else (if i < 699 then decide (2 ≤ count697 b) else (if i < 700 then decide (1 ≤ count699 b) else decide (2 ≤ count699 b)))))) else (if i < 712 then (if i < 706 then (if i < 703 then (if i < 702 then decide (3 ≤ count699 b) else decide (1 ≤ count702 b)) else (if i < 704 then decide (2 ≤ count702 b) else (if i < 705 then decide (1 ≤ count704 b) else decide (2 ≤ count704 b)))) else (if i < 709 then (if i < 707 then decide (3 ≤ count704 b) else (if i < 708 then decide (1 ≤ count707 b) else decide (2 ≤ count707 b))) else (if i < 710 then decide (3 ≤ count707 b) else (if i < 711 then decide (4 ≤ count707 b) else decide (5 ≤ count707 b))))) else (if i < 718 then (if i < 715 then (if i < 713 then decide (6 ≤ count707 b) else (if i < 714 then decide (1 ≤ count713 b) else decide (2 ≤ count713 b))) else (if i < 716 then decide (1 ≤ count715 b) else (if i < 717 then decide (2 ≤ count715 b) else decide (3 ≤ count715 b)))) else (if i < 721 then (if i < 719 then decide (1 ≤ count718 b) else (if i < 720 then decide (2 ≤ count718 b) else decide (1 ≤ count720 b))) else (if i < 722 then decide (2 ≤ count720 b) else (if i < 723 then decide (3 ≤ count720 b) else decide (1 ≤ count723 b))))))))))) else (if i < 1086 then (if i < 905 then (if i < 814 then (if i < 769 then (if i < 746 then (if i < 735 then (if i < 729 then (if i < 726 then (if i < 725 then decide (2 ≤ count723 b) else decide (3 ≤ count723 b)) else (if i < 727 then decide (4 ≤ count723 b) else (if i < 728 then decide (5 ≤ count723 b) else decide (6 ≤ count723 b)))) else (if i < 732 then (if i < 730 then decide (1 ≤ count729 b) else (if i < 731 then decide (2 ≤ count729 b) else decide (3 ≤ count729 b))) else (if i < 733 then decide (4 ≤ count729 b) else (if i < 734 then decide (5 ≤ count729 b) else decide (6 ≤ count729 b))))) else (if i < 740 then (if i < 737 then (if i < 736 then decide (7 ≤ count729 b) else decide (8 ≤ count729 b)) else (if i < 738 then decide (9 ≤ count729 b) else (if i < 739 then decide (10 ≤ count729 b) else decide (11 ≤ count729 b)))) else (if i < 743 then (if i < 741 then decide (1 ≤ count740 b) else (if i < 742 then decide (2 ≤ count740 b) else decide (1 ≤ count742 b))) else (if i < 744 then decide (2 ≤ count742 b) else (if i < 745 then decide (3 ≤ count742 b) else decide (1 ≤ count745 b)))))) else (if i < 757 then (if i < 751 then (if i < 748 then (if i < 747 then decide (2 ≤ count745 b) else decide (1 ≤ count747 b)) else (if i < 749 then decide (2 ≤ count747 b) else (if i < 750 then decide (3 ≤ count747 b) else decide (1 ≤ count750 b)))) else (if i < 754 then (if i < 752 then decide (2 ≤ count750 b) else (if i < 753 then decide (3 ≤ count750 b) else decide (4 ≤ count750 b))) else (if i < 755 then decide (5 ≤ count750 b) else (if i < 756 then decide (6 ≤ count750 b) else decide (1 ≤ count756 b))))) else (if i < 763 then (if i < 760 then (if i < 758 then decide (2 ≤ count756 b) else (if i < 759 then decide (1 ≤ count758 b) else decide (2 ≤ count758 b))) else (if i < 761 then decide (3 ≤ count758 b) else (if i < 762 then decide (1 ≤ count761 b) else decide (2 ≤ count761 b)))) else (if i < 766 then (if i < 764 then decide (1 ≤ count763 b) else (if i < 765 then decide (2 ≤ count763 b) else decide (1 ≤ count765 b))) else (if i < 767 then decide (2 ≤ count765 b) else (if i < 768 then decide (3 ≤ count765 b) else decide (4 ≤ count765 b))))))) else (if i < 791 then (if i < 780 then (if i < 774 then (if i < 771 then (if i < 770 then decide (1 ≤ count769 b) else decide (2 ≤ count769 b)) else (if i < 772 then decide (3 ≤ count769 b) else (if i < 773 then decide (4 ≤ count769 b) else decide (5 ≤ count769 b)))) else (if i < 777 then (if i < 775 then decide (6 ≤ count769 b) else (if i < 776 then decide (7 ≤ count769 b) else decide (1 ≤ count776 b))) else (if i < 778 then decide (2 ≤ count776 b) else (if i < 779 then decide (3 ≤ count776 b) else decide (4 ≤ count776 b))))) else (if i < 785 then (if i < 782 then (if i < 781 then decide (5 ≤ count776 b) else decide (6 ≤ count776 b)) else (if i < 783 then decide (7 ≤ count776 b) else (if i < 784 then decide (8 ≤ count776 b) else decide (9 ≤ count776 b)))) else (if i < 788 then (if i < 786 then decide (10 ≤ count776 b) else (if i < 787 then decide (11 ≤ count776 b) else decide (1 ≤ count787 b))) else (if i < 789 then decide (2 ≤ count787 b) else (if i < 790 then decide (3 ≤ count787 b) else decide (4 ≤ count787 b)))))) else (if i < 802 then (if i < 796 then (if i < 793 then (if i < 792 then decide (5 ≤ count787 b) else decide (6 ≤ count787 b)) else (if i < 794 then decide (7 ≤ count787 b) else (if i < 795 then decide (8 ≤ count787 b) else decide (9 ≤ count787 b)))) else (if i < 799 then (if i < 797 then decide (10 ≤ count787 b) else (if i < 798 then decide (11 ≤ count787 b) else decide (1 ≤ count798 b))) else (if i < 800 then decide (2 ≤ count798 b) else (if i < 801 then decide (1 ≤ count800 b) else decide (2 ≤ count800 b))))) else (if i < 808 then (if i < 805 then (if i < 803 then decide (3 ≤ count800 b) else (if i < 804 then decide (1 ≤ count803 b) else decide (2 ≤ count803 b))) else (if i < 806 then decide (1 ≤ count805 b) else (if i < 807 then decide (2 ≤ count805 b) else decide (3 ≤ count805 b)))) else (if i < 811 then (if i < 809 then decide (1 ≤ count808 b) else (if i < 810 then decide (2 ≤ count808 b) else decide (3 ≤ count808 b))) else (if i < 812 then decide (4 ≤ count808 b) else (if i < 813 then decide (5 ≤ count808 b) else decide (6 ≤ count808 b)))))))) else (if i < 859 then (if i < 836 then (if i < 825 then (if i < 819 then (if i < 816 then (if i < 815 then decide (1 ≤ count814 b) else decide (2 ≤ count814 b)) else (if i < 817 then decide (1 ≤ count816 b) else (if i < 818 then decide (2 ≤ count816 b) else decide (3 ≤ count816 b)))) else (if i < 822 then (if i < 820 then decide (1 ≤ count819 b) else (if i < 821 then decide (2 ≤ count819 b) else decide (1 ≤ count821 b))) else (if i < 823 then decide (2 ≤ count821 b) else (if i < 824 then decide (1 ≤ count823 b) else decide (2 ≤ count823 b))))) else (if i < 830 then (if i < 827 then (if i < 826 then decide (3 ≤ count823 b) else decide (4 ≤ count823 b)) else (if i < 828 then decide (1 ≤ count827 b) else (if i < 829 then decide (2 ≤ count827 b) else decide (3 ≤ count827 b)))) else (if i < 833 then (if i < 831 then decide (4 ≤ count827 b) else (if i < 832 then decide (5 ≤ count827 b) else decide (6 ≤ count827 b))) else (if i < 834 then decide (7 ≤ count827 b) else (if i < 835 then decide (1 ≤ count834 b) else decide (2 ≤ count834 b)))))) else (if i < 847 then (if i < 841 then (if i < 838 then (if i < 837 then decide (3 ≤ count834 b) else decide (4 ≤ count834 b)) else (if i < 839 then decide (5 ≤ count834 b) else (if i < 840 then decide (6 ≤ count834 b) else decide (7 ≤ count834 b)))) else (if i < 844 then (if i < 842 then decide (8 ≤ count834 b) else (if i < 843 then decide (9 ≤ count834 b) else decide (10 ≤ count834 b))) else (if i < 845 then decide (11 ≤ count834 b) else (if i < 846 then decide (1 ≤ count845 b) else decide (2 ≤ count845 b))))) else (if i < 853 then (if i < 850 then (if i < 848 then decide (1 ≤ count847 b) else (if i < 849 then decide (2 ≤ count847 b) else decide (3 ≤ count847 b))) else (if i < 851 then decide (1 ≤ count850 b) else (if i < 852 then decide (2 ≤ count850 b) else decide (1 ≤ count852 b)))) else (if i < 856 then (if i < 854 then decide (2 ≤ count852 b) else (if i < 855 then decide (3 ≤ count852 b) else decide (1 ≤ count855 b))) else (if i < 857 then decide (2 ≤ count855 b) else (if i < 858 then decide (3 ≤ count855 b) else decide (4 ≤ count855 b))))))) else (if i < 882 then (if i < 870 then (if i < 864 then (if i < 861 then (if i < 860 then decide (5 ≤ count855 b) else decide (6 ≤ count855 b)) else (if i < 862 then decide (1 ≤ count861 b) else (if i < 863 then decide (2 ≤ count861 b) else decide (1 ≤ count863 b)))) else (if i < 867 then (if i < 865 then decide (2 ≤ count863 b) else (if i < 866 then decide (3 ≤ count863 b) else decide (1 ≤ count866 b))) else (if i < 868 then decide (2 ≤ count866 b) else (if i < 869 then decide (1 ≤ count868 b) else decide (2 ≤ count868 b))))) else (if i < 876 then (if i < 873 then (if i < 871 then decide (1 ≤ count870 b) else (if i < 872 then decide (2 ≤ count870 b) else decide (3 ≤ count870 b))) else (if i < 874 then decide (4 ≤ count870 b) else (if i < 875 then decide (1 ≤ count874 b) else decide (2 ≤ count874 b)))) else (if i < 879 then (if i < 877 then decide (3 ≤ count874 b) else (if i < 878 then decide (4 ≤ count874 b) else decide (5 ≤ count874 b))) else (if i < 880 then decide (6 ≤ count874 b) else (if i < 881 then decide (7 ≤ count874 b) else decide (1 ≤ count881 b)))))) else (if i < 893 then (if i < 887 then (if i < 884 then (if i < 883 then decide (2 ≤ count881 b) else decide (3 ≤ count881 b)) else (if i < 885 then decide (4 ≤ count881 b) else (if i < 886 then decide (5 ≤ count881 b) else decide (6 ≤ count881 b)))) else (if i < 890 then (if i < 888 then decide (7 ≤ count881 b) else (if i < 889 then decide (8 ≤ count881 b) else decide (9 ≤ count881 b))) else (if i < 891 then decide (10 ≤ count881 b) else (if i < 892 then decide (11 ≤ count881 b) else decide (1 ≤ count892 b))))) else (if i < 899 then (if i < 896 then (if i < 894 then decide (2 ≤ count892 b) else (if i < 895 then decide (3 ≤ count892 b) else decide (4 ≤ count892 b))) else (if i < 897 then decide (5 ≤ count892 b) else (if i < 898 then decide (6 ≤ count892 b) else decide (7 ≤ count892 b)))) else (if i < 902 then (if i < 900 then decide (8 ≤ count892 b) else (if i < 901 then decide (9 ≤ count892 b) else decide (10 ≤ count892 b))) else (if i < 903 then decide (11 ≤ count892 b) else (if i < 904 then decide (1 ≤ count903 b) else decide (2 ≤ count903 b))))))))) else (if i < 995 then (if i < 950 then (if i < 927 then (if i < 916 then (if i < 910 then (if i < 907 then (if i < 906 then decide (3 ≤ count903 b) else decide (4 ≤ count903 b)) else (if i < 908 then decide (5 ≤ count903 b) else (if i < 909 then decide (6 ≤ count903 b) else decide (7 ≤ count903 b)))) else (if i < 913 then (if i < 911 then decide (8 ≤ count903 b) else (if i < 912 then decide (9 ≤ count903 b) else decide (10 ≤ count903 b))) else (if i < 914 then decide (11 ≤ count903 b) else (if i < 915 then decide (1 ≤ count914 b) else decide (2 ≤ count914 b))))) else (if i < 921 then (if i < 918 then (if i < 917 then decide (1 ≤ count916 b) else decide (2 ≤ count916 b)) else (if i < 919 then decide (3 ≤ count916 b) else (if i < 920 then decide (1 ≤ count919 b) else decide (2 ≤ count919 b)))) else (if i < 924 then (if i < 922 then decide (1 ≤ count921 b) else (if i < 923 then decide (2 ≤ count921 b) else decide (3 ≤ count921 b))) else (if i < 925 then decide (1 ≤ count924 b) else (if i < 926 then decide (2 ≤ count924 b) else decide (3 ≤ count924 b)))))) else (if i < 938 then (if i < 932 then (if i < 929 then (if i < 928 then decide (4 ≤ count924 b) else decide (5 ≤ count924 b)) else (if i < 930 then decide (6 ≤ count924 b) else (if i < 931 then decide (1 ≤ count930 b) else decide (2 ≤ count930 b)))) else (if i < 935 then (if i < 933 then decide (1 ≤ count932 b) else (if i < 934 then decide (2 ≤ count932 b) else decide (3 ≤ count932 b))) else (if i < 936 then decide (1 ≤ count935 b) else (if i < 937 then decide (2 ≤ count935 b) else decide (1 ≤ count937 b))))) else (if i < 944 then (if i < 941 then (if i < 939 then decide (2 ≤ count937 b) else (if i < 940 then decide (1 ≤ count939 b) else decide (2 ≤ count939 b))) else (if i < 942 then decide (3 ≤ count939 b) else (if i < 943 then decide (4 ≤ count939 b) else decide (1 ≤ count943 b)))) else (if i < 947 then (if i < 945 then decide (2 ≤ count943 b) else (if i < 946 then decide (3 ≤ count943 b) else decide (4 ≤ count943 b))) else (if i < 948 then decide (5 ≤ count943 b) else (if i < 949 then decide (6 ≤ count943 b) else decide (7 ≤ count943 b))))))) else (if i < 972 then (if i < 961 then (if i < 955 then (if i < 952 then (if i < 951 then decide (1 ≤ count950 b) else decide (2 ≤ count950 b)) else (if i < 953 then decide (3 ≤ count950 b) else (if i < 954 then decide (4 ≤ count950 b) else decide (5 ≤ count950 b)))) else (if i < 958 then (if i < 956 then decide (6 ≤ count950 b) else (if i < 957 then decide (7 ≤ count950 b) else decide (8 ≤ count950 b))) else (if i < 959 then decide (9 ≤ count950 b) else (if i < 960 then decide (10 ≤ count950 b) else decide (11 ≤ count950 b))))) else (if i < 966 then (if i < 963 then (if i < 962 then decide (12 ≤ count950 b) else decide (13 ≤ count950 b)) else (if i < 964 then decide (1 ≤ count963 b) else (if i < 965 then decide (2 ≤ count963 b) else decide (1 ≤ count965 b)))) else (if i < 969 then (if i < 967 then decide (2 ≤ count965 b) else (if i < 968 then decide (3 ≤ count965 b) else decide (1 ≤ count968 b))) else (if i < 970 then decide (2 ≤ count968 b) else (if i < 971 then decide (1 ≤ count970 b) else decide (2 ≤ count970 b)))))) else (if i < 983 then (if i < 977 then (if i < 974 then (if i < 973 then decide (3 ≤ count970 b) else decide (1 ≤ count973 b)) else (if i < 975 then decide (2 ≤ count973 b) else (if i < 976 then decide (3 ≤ count973 b) else decide (4 ≤ count973 b)))) else (if i < 980 then (if i < 978 then decide (5 ≤ count973 b) else (if i < 979 then decide (6 ≤ count973 b) else decide (1 ≤ count979 b))) else (if i < 981 then decide (2 ≤ count979 b) else (if i < 982 then decide (1 ≤ count981 b) else decide (2 ≤ count981 b))))) else (if i < 989 then (if i < 986 then (if i < 984 then decide (3 ≤ count981 b) else (if i < 985 then decide (1 ≤ count984 b) else decide (2 ≤ count984 b))) else (if i < 987 then decide (1 ≤ count986 b) else (if i < 988 then decide (2 ≤ count986 b) else decide (1 ≤ count988 b)))) else (if i < 992 then (if i < 990 then decide (2 ≤ count988 b) else (if i < 991 then decide (3 ≤ count988 b) else decide (4 ≤ count988 b))) else (if i < 993 then decide (1 ≤ count992 b) else (if i < 994 then decide (2 ≤ count992 b) else decide (3 ≤ count992 b)))))))) else (if i < 1040 then (if i < 1017 then (if i < 1006 then (if i < 1000 then (if i < 997 then (if i < 996 then decide (4 ≤ count992 b) else decide (5 ≤ count992 b)) else (if i < 998 then decide (6 ≤ count992 b) else (if i < 999 then decide (7 ≤ count992 b) else decide (1 ≤ count999 b)))) else (if i < 1003 then (if i < 1001 then decide (2 ≤ count999 b) else (if i < 1002 then decide (3 ≤ count999 b) else decide (4 ≤ count999 b))) else (if i < 1004 then decide (5 ≤ count999 b) else (if i < 1005 then decide (6 ≤ count999 b) else decide (7 ≤ count999 b))))) else (if i < 1011 then (if i < 1008 then (if i < 1007 then decide (8 ≤ count999 b) else decide (9 ≤ count999 b)) else (if i < 1009 then decide (10 ≤ count999 b) else (if i < 1010 then decide (11 ≤ count999 b) else decide (12 ≤ count999 b)))) else (if i < 1014 then (if i < 1012 then decide (13 ≤ count999 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b))) else (if i < 1015 then decide (3 ≤ count1012 b) else (if i < 1016 then decide (4 ≤ count1012 b) else decide (5 ≤ count1012 b)))))) else (if i < 1028 then (if i < 1022 then (if i < 1019 then (if i < 1018 then decide (6 ≤ count1012 b) else decide (7 ≤ count1012 b)) else (if i < 1020 then decide (8 ≤ count1012 b) else (if i < 1021 then decide (9 ≤ count1012 b) else decide (10 ≤ count1012 b)))) else (if i < 1025 then (if i < 1023 then decide (11 ≤ count1012 b) else (if i < 1024 then decide (12 ≤ count1012 b) else decide (13 ≤ count1012 b))) else (if i < 1026 then decide (14 ≤ count1012 b) else (if i < 1027 then decide (15 ≤ count1012 b) else decide (16 ≤ count1012 b))))) else (if i < 1034 then (if i < 1031 then (if i < 1029 then decide (17 ≤ count1012 b) else (if i < 1030 then decide (18 ≤ count1012 b) else decide (19 ≤ count1012 b))) else (if i < 1032 then decide (20 ≤ count1012 b) else (if i < 1033 then decide (21 ≤ count1012 b) else decide (22 ≤ count1012 b)))) else (if i < 1037 then (if i < 1035 then decide (23 ≤ count1012 b) else (if i < 1036 then decide (24 ≤ count1012 b) else decide (25 ≤ count1012 b))) else (if i < 1038 then decide (26 ≤ count1012 b) else (if i < 1039 then decide (1 ≤ count1038 b) else decide (2 ≤ count1038 b))))))) else (if i < 1063 then (if i < 1051 then (if i < 1045 then (if i < 1042 then (if i < 1041 then decide (1 ≤ count1040 b) else decide (2 ≤ count1040 b)) else (if i < 1043 then decide (3 ≤ count1040 b) else (if i < 1044 then decide (1 ≤ count1043 b) else decide (2 ≤ count1043 b)))) else (if i < 1048 then (if i < 1046 then decide (1 ≤ count1045 b) else (if i < 1047 then decide (2 ≤ count1045 b) else decide (3 ≤ count1045 b))) else (if i < 1049 then decide (1 ≤ count1048 b) else (if i < 1050 then decide (2 ≤ count1048 b) else decide (3 ≤ count1048 b))))) else (if i < 1057 then (if i < 1054 then (if i < 1052 then decide (4 ≤ count1048 b) else (if i < 1053 then decide (5 ≤ count1048 b) else decide (6 ≤ count1048 b))) else (if i < 1055 then decide (1 ≤ count1054 b) else (if i < 1056 then decide (2 ≤ count1054 b) else decide (1 ≤ count1056 b)))) else (if i < 1060 then (if i < 1058 then decide (2 ≤ count1056 b) else (if i < 1059 then decide (3 ≤ count1056 b) else decide (1 ≤ count1059 b))) else (if i < 1061 then decide (2 ≤ count1059 b) else (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b)))))) else (if i < 1074 then (if i < 1068 then (if i < 1065 then (if i < 1064 then decide (1 ≤ count1063 b) else decide (2 ≤ count1063 b)) else (if i < 1066 then decide (3 ≤ count1063 b) else (if i < 1067 then decide (4 ≤ count1063 b) else decide (1 ≤ count1067 b)))) else (if i < 1071 then (if i < 1069 then decide (2 ≤ count1067 b) else (if i < 1070 then decide (3 ≤ count1067 b) else decide (4 ≤ count1067 b))) else (if i < 1072 then decide (5 ≤ count1067 b) else (if i < 1073 then decide (6 ≤ count1067 b) else decide (7 ≤ count1067 b))))) else (if i < 1080 then (if i < 1077 then (if i < 1075 then decide (1 ≤ count1074 b) else (if i < 1076 then decide (2 ≤ count1074 b) else decide (3 ≤ count1074 b))) else (if i < 1078 then decide (4 ≤ count1074 b) else (if i < 1079 then decide (5 ≤ count1074 b) else decide (6 ≤ count1074 b)))) else (if i < 1083 then (if i < 1081 then decide (7 ≤ count1074 b) else (if i < 1082 then decide (8 ≤ count1074 b) else decide (9 ≤ count1074 b))) else (if i < 1084 then decide (10 ≤ count1074 b) else (if i < 1085 then decide (11 ≤ count1074 b) else decide (12 ≤ count1074 b)))))))))) else (if i < 1267 then (if i < 1176 then (if i < 1131 then (if i < 1108 then (if i < 1097 then (if i < 1091 then (if i < 1088 then (if i < 1087 then decide (13 ≤ count1074 b) else decide (1 ≤ count1087 b)) else (if i < 1089 then decide (2 ≤ count1087 b) else (if i < 1090 then decide (1 ≤ count1089 b) else decide (2 ≤ count1089 b)))) else (if i < 1094 then (if i < 1092 then decide (3 ≤ count1089 b) else (if i < 1093 then decide (1 ≤ count1092 b) else decide (2 ≤ count1092 b))) else (if i < 1095 then decide (1 ≤ count1094 b) else (if i < 1096 then decide (2 ≤ count1094 b) else decide (1 ≤ count1096 b))))) else (if i < 1102 then (if i < 1099 then (if i < 1098 then decide (2 ≤ count1096 b) else decide (3 ≤ count1096 b)) else (if i < 1100 then decide (4 ≤ count1096 b) else (if i < 1101 then decide (1 ≤ count1100 b) else decide (2 ≤ count1100 b)))) else (if i < 1105 then (if i < 1103 then decide (3 ≤ count1100 b) else (if i < 1104 then decide (4 ≤ count1100 b) else decide (5 ≤ count1100 b))) else (if i < 1106 then decide (6 ≤ count1100 b) else (if i < 1107 then decide (7 ≤ count1100 b) else decide (1 ≤ count1107 b)))))) else (if i < 1119 then (if i < 1113 then (if i < 1110 then (if i < 1109 then decide (2 ≤ count1107 b) else decide (1 ≤ count1109 b)) else (if i < 1111 then decide (2 ≤ count1109 b) else (if i < 1112 then decide (3 ≤ count1109 b) else decide (1 ≤ count1112 b)))) else (if i < 1116 then (if i < 1114 then decide (2 ≤ count1112 b) else (if i < 1115 then decide (1 ≤ count1114 b) else decide (2 ≤ count1114 b))) else (if i < 1117 then decide (1 ≤ count1116 b) else (if i < 1118 then decide (2 ≤ count1116 b) else decide (3 ≤ count1116 b))))) else (if i < 1125 then (if i < 1122 then (if i < 1120 then decide (4 ≤ count1116 b) else (if i < 1121 then decide (1 ≤ count1120 b) else decide (2 ≤ count1120 b))) else (if i < 1123 then decide (3 ≤ count1120 b) else (if i < 1124 then decide (4 ≤ count1120 b) else decide (5 ≤ count1120 b)))) else (if i < 1128 then (if i < 1126 then decide (6 ≤ count1120 b) else (if i < 1127 then decide (7 ≤ count1120 b) else decide (1 ≤ count1127 b))) else (if i < 1129 then decide (2 ≤ count1127 b) else (if i < 1130 then decide (3 ≤ count1127 b) else decide (4 ≤ count1127 b))))))) else (if i < 1153 then (if i < 1142 then (if i < 1136 then (if i < 1133 then (if i < 1132 then decide (5 ≤ count1127 b) else decide (6 ≤ count1127 b)) else (if i < 1134 then decide (7 ≤ count1127 b) else (if i < 1135 then decide (8 ≤ count1127 b) else decide (9 ≤ count1127 b)))) else (if i < 1139 then (if i < 1137 then decide (10 ≤ count1127 b) else (if i < 1138 then decide (11 ≤ count1127 b) else decide (12 ≤ count1127 b))) else (if i < 1140 then decide (13 ≤ count1127 b) else (if i < 1141 then decide (14 ≤ count1127 b) else decide (1 ≤ count1141 b))))) else (if i < 1147 then (if i < 1144 then (if i < 1143 then decide (2 ≤ count1141 b) else decide (3 ≤ count1141 b)) else (if i < 1145 then decide (4 ≤ count1141 b) else (if i < 1146 then decide (5 ≤ count1141 b) else decide (6 ≤ count1141 b)))) else (if i < 1150 then (if i < 1148 then decide (7 ≤ count1141 b) else (if i < 1149 then decide (8 ≤ count1141 b) else decide (9 ≤ count1141 b))) else (if i < 1151 then decide (10 ≤ count1141 b) else (if i < 1152 then decide (11 ≤ count1141 b) else decide (12 ≤ count1141 b)))))) else (if i < 1164 then (if i < 1158 then (if i < 1155 then (if i < 1154 then decide (13 ≤ count1141 b) else decide (14 ≤ count1141 b)) else (if i < 1156 then decide (15 ≤ count1141 b) else (if i < 1157 then decide (16 ≤ count1141 b) else decide (17 ≤ count1141 b)))) else (if i < 1161 then (if i < 1159 then decide (18 ≤ count1141 b) else (if i < 1160 then decide (19 ≤ count1141 b) else decide (20 ≤ count1141 b))) else (if i < 1162 then decide (21 ≤ count1141 b) else (if i < 1163 then decide (22 ≤ count1141 b) else decide (23 ≤ count1141 b))))) else (if i < 1170 then (if i < 1167 then (if i < 1165 then decide (24 ≤ count1141 b) else (if i < 1166 then decide (25 ≤ count1141 b) else decide (26 ≤ count1141 b))) else (if i < 1168 then decide (27 ≤ count1141 b) else (if i < 1169 then decide (1 ≤ count1168 b) else decide (2 ≤ count1168 b)))) else (if i < 1173 then (if i < 1171 then decide (3 ≤ count1168 b) else (if i < 1172 then decide (4 ≤ count1168 b) else decide (5 ≤ count1168 b))) else (if i < 1174 then decide (6 ≤ count1168 b) else (if i < 1175 then decide (7 ≤ count1168 b) else decide (8 ≤ count1168 b)))))))) else (if i < 1221 then (if i < 1198 then (if i < 1187 then (if i < 1181 then (if i < 1178 then (if i < 1177 then decide (9 ≤ count1168 b) else decide (10 ≤ count1168 b)) else (if i < 1179 then decide (11 ≤ count1168 b) else (if i < 1180 then decide (12 ≤ count1168 b) else decide (13 ≤ count1168 b)))) else (if i < 1184 then (if i < 1182 then decide (14 ≤ count1168 b) else (if i < 1183 then decide (15 ≤ count1168 b) else decide (16 ≤ count1168 b))) else (if i < 1185 then decide (17 ≤ count1168 b) else (if i < 1186 then decide (18 ≤ count1168 b) else decide (19 ≤ count1168 b))))) else (if i < 1192 then (if i < 1189 then (if i < 1188 then decide (20 ≤ count1168 b) else decide (21 ≤ count1168 b)) else (if i < 1190 then decide (22 ≤ count1168 b) else (if i < 1191 then decide (23 ≤ count1168 b) else decide (24 ≤ count1168 b)))) else (if i < 1195 then (if i < 1193 then decide (25 ≤ count1168 b) else (if i < 1194 then decide (26 ≤ count1168 b) else decide (27 ≤ count1168 b))) else (if i < 1196 then decide (28 ≤ count1168 b) else (if i < 1197 then decide (29 ≤ count1168 b) else decide (30 ≤ count1168 b)))))) else (if i < 1209 then (if i < 1203 then (if i < 1200 then (if i < 1199 then decide (31 ≤ count1168 b) else decide (32 ≤ count1168 b)) else (if i < 1201 then decide (33 ≤ count1168 b) else (if i < 1202 then decide (34 ≤ count1168 b) else decide (35 ≤ count1168 b)))) else (if i < 1206 then (if i < 1204 then decide (36 ≤ count1168 b) else (if i < 1205 then decide (37 ≤ count1168 b) else decide (38 ≤ count1168 b))) else (if i < 1207 then decide (39 ≤ count1168 b) else (if i < 1208 then decide (40 ≤ count1168 b) else decide (41 ≤ count1168 b))))) else (if i < 1215 then (if i < 1212 then (if i < 1210 then decide (42 ≤ count1168 b) else (if i < 1211 then decide (1 ≤ count1210 b) else decide (2 ≤ count1210 b))) else (if i < 1213 then decide (1 ≤ count1212 b) else (if i < 1214 then decide (2 ≤ count1212 b) else decide (3 ≤ count1212 b)))) else (if i < 1218 then (if i < 1216 then decide (1 ≤ count1215 b) else (if i < 1217 then decide (2 ≤ count1215 b) else decide (1 ≤ count1217 b))) else (if i < 1219 then decide (2 ≤ count1217 b) else (if i < 1220 then decide (3 ≤ count1217 b) else decide (1 ≤ count1220 b))))))) else (if i < 1244 then (if i < 1232 then (if i < 1226 then (if i < 1223 then (if i < 1222 then decide (2 ≤ count1220 b) else decide (3 ≤ count1220 b)) else (if i < 1224 then decide (4 ≤ count1220 b) else (if i < 1225 then decide (5 ≤ count1220 b) else decide (6 ≤ count1220 b)))) else (if i < 1229 then (if i < 1227 then decide (1 ≤ count1226 b) else (if i < 1228 then decide (2 ≤ count1226 b) else decide (1 ≤ count1228 b))) else (if i < 1230 then decide (2 ≤ count1228 b) else (if i < 1231 then decide (3 ≤ count1228 b) else decide (1 ≤ count1231 b))))) else (if i < 1238 then (if i < 1235 then (if i < 1233 then decide (2 ≤ count1231 b) else (if i < 1234 then decide (1 ≤ count1233 b) else decide (2 ≤ count1233 b))) else (if i < 1236 then decide (1 ≤ count1235 b) else (if i < 1237 then decide (2 ≤ count1235 b) else decide (3 ≤ count1235 b)))) else (if i < 1241 then (if i < 1239 then decide (4 ≤ count1235 b) else (if i < 1240 then decide (1 ≤ count1239 b) else decide (2 ≤ count1239 b))) else (if i < 1242 then decide (3 ≤ count1239 b) else (if i < 1243 then decide (4 ≤ count1239 b) else decide (5 ≤ count1239 b)))))) else (if i < 1255 then (if i < 1249 then (if i < 1246 then (if i < 1245 then decide (6 ≤ count1239 b) else decide (7 ≤ count1239 b)) else (if i < 1247 then decide (1 ≤ count1246 b) else (if i < 1248 then decide (2 ≤ count1246 b) else decide (3 ≤ count1246 b)))) else (if i < 1252 then (if i < 1250 then decide (4 ≤ count1246 b) else (if i < 1251 then decide (5 ≤ count1246 b) else decide (6 ≤ count1246 b))) else (if i < 1253 then decide (7 ≤ count1246 b) else (if i < 1254 then decide (8 ≤ count1246 b) else decide (9 ≤ count1246 b))))) else (if i < 1261 then (if i < 1258 then (if i < 1256 then decide (10 ≤ count1246 b) else (if i < 1257 then decide (11 ≤ count1246 b) else decide (12 ≤ count1246 b))) else (if i < 1259 then decide (13 ≤ count1246 b) else (if i < 1260 then decide (1 ≤ count1259 b) else decide (2 ≤ count1259 b)))) else (if i < 1264 then (if i < 1262 then decide (1 ≤ count1261 b) else (if i < 1263 then decide (2 ≤ count1261 b) else decide (3 ≤ count1261 b))) else (if i < 1265 then decide (1 ≤ count1264 b) else (if i < 1266 then decide (2 ≤ count1264 b) else decide (1 ≤ count1266 b))))))))) else (if i < 1358 then (if i < 1312 then (if i < 1289 then (if i < 1278 then (if i < 1272 then (if i < 1269 then (if i < 1268 then decide (2 ≤ count1266 b) else decide (3 ≤ count1266 b)) else (if i < 1270 then decide (1 ≤ count1269 b) else (if i < 1271 then decide (2 ≤ count1269 b) else decide (3 ≤ count1269 b)))) else (if i < 1275 then (if i < 1273 then decide (4 ≤ count1269 b) else (if i < 1274 then decide (5 ≤ count1269 b) else decide (6 ≤ count1269 b))) else (if i < 1276 then decide (1 ≤ count1275 b) else (if i < 1277 then decide (2 ≤ count1275 b) else decide (1 ≤ count1277 b))))) else (if i < 1283 then (if i < 1280 then (if i < 1279 then decide (2 ≤ count1277 b) else decide (3 ≤ count1277 b)) else (if i < 1281 then decide (1 ≤ count1280 b) else (if i < 1282 then decide (2 ≤ count1280 b) else decide (1 ≤ count1282 b)))) else (if i < 1286 then (if i < 1284 then decide (2 ≤ count1282 b) else (if i < 1285 then decide (1 ≤ count1284 b) else decide (2 ≤ count1284 b))) else (if i < 1287 then decide (3 ≤ count1284 b) else (if i < 1288 then decide (4 ≤ count1284 b) else decide (1 ≤ count1288 b)))))) else (if i < 1300 then (if i < 1294 then (if i < 1291 then (if i < 1290 then decide (2 ≤ count1288 b) else decide (3 ≤ count1288 b)) else (if i < 1292 then decide (4 ≤ count1288 b) else (if i < 1293 then decide (5 ≤ count1288 b) else decide (6 ≤ count1288 b)))) else (if i < 1297 then (if i < 1295 then decide (7 ≤ count1288 b) else (if i < 1296 then decide (1 ≤ count1295 b) else decide (2 ≤ count1295 b))) else (if i < 1298 then decide (3 ≤ count1295 b) else (if i < 1299 then decide (4 ≤ count1295 b) else decide (5 ≤ count1295 b))))) else (if i < 1306 then (if i < 1303 then (if i < 1301 then decide (6 ≤ count1295 b) else (if i < 1302 then decide (7 ≤ count1295 b) else decide (8 ≤ count1295 b))) else (if i < 1304 then decide (9 ≤ count1295 b) else (if i < 1305 then decide (10 ≤ count1295 b) else decide (11 ≤ count1295 b)))) else (if i < 1309 then (if i < 1307 then decide (12 ≤ count1295 b) else (if i < 1308 then decide (13 ≤ count1295 b) else decide (1 ≤ count1308 b))) else (if i < 1310 then decide (2 ≤ count1308 b) else (if i < 1311 then decide (3 ≤ count1308 b) else decide (4 ≤ count1308 b))))))) else (if i < 1335 then (if i < 1323 then (if i < 1317 then (if i < 1314 then (if i < 1313 then decide (5 ≤ count1308 b) else decide (6 ≤ count1308 b)) else (if i < 1315 then decide (7 ≤ count1308 b) else (if i < 1316 then decide (8 ≤ count1308 b) else decide (9 ≤ count1308 b)))) else (if i < 1320 then (if i < 1318 then decide (10 ≤ count1308 b) else (if i < 1319 then decide (11 ≤ count1308 b) else decide (12 ≤ count1308 b))) else (if i < 1321 then decide (13 ≤ count1308 b) else (if i < 1322 then decide (1 ≤ count1321 b) else decide (2 ≤ count1321 b))))) else (if i < 1329 then (if i < 1326 then (if i < 1324 then decide (1 ≤ count1323 b) else (if i < 1325 then decide (2 ≤ count1323 b) else decide (3 ≤ count1323 b))) else (if i < 1327 then decide (1 ≤ count1326 b) else (if i < 1328 then decide (2 ≤ count1326 b) else decide (1 ≤ count1328 b)))) else (if i < 1332 then (if i < 1330 then decide (2 ≤ count1328 b) else (if i < 1331 then decide (3 ≤ count1328 b) else decide (1 ≤ count1331 b))) else (if i < 1333 then decide (2 ≤ count1331 b) else (if i < 1334 then decide (3 ≤ count1331 b) else decide (4 ≤ count1331 b)))))) else (if i < 1346 then (if i < 1340 then (if i < 1337 then (if i < 1336 then decide (5 ≤ count1331 b) else decide (6 ≤ count1331 b)) else (if i < 1338 then decide (1 ≤ count1337 b) else (if i < 1339 then decide (2 ≤ count1337 b) else decide (1 ≤ count1339 b)))) else (if i < 1343 then (if i < 1341 then decide (2 ≤ count1339 b) else (if i < 1342 then decide (3 ≤ count1339 b) else decide (1 ≤ count1342 b))) else (if i < 1344 then decide (2 ≤ count1342 b) else (if i < 1345 then decide (1 ≤ count1344 b) else decide (2 ≤ count1344 b))))) else (if i < 1352 then (if i < 1349 then (if i < 1347 then decide (1 ≤ count1346 b) else (if i < 1348 then decide (2 ≤ count1346 b) else decide (3 ≤ count1346 b))) else (if i < 1350 then decide (4 ≤ count1346 b) else (if i < 1351 then decide (1 ≤ count1350 b) else decide (2 ≤ count1350 b)))) else (if i < 1355 then (if i < 1353 then decide (3 ≤ count1350 b) else (if i < 1354 then decide (4 ≤ count1350 b) else decide (5 ≤ count1350 b))) else (if i < 1356 then decide (6 ≤ count1350 b) else (if i < 1357 then decide (7 ≤ count1350 b) else decide (1 ≤ count1357 b)))))))) else (if i < 1403 then (if i < 1380 then (if i < 1369 then (if i < 1363 then (if i < 1360 then (if i < 1359 then decide (2 ≤ count1357 b) else decide (3 ≤ count1357 b)) else (if i < 1361 then decide (4 ≤ count1357 b) else (if i < 1362 then decide (5 ≤ count1357 b) else decide (6 ≤ count1357 b)))) else (if i < 1366 then (if i < 1364 then decide (7 ≤ count1357 b) else (if i < 1365 then decide (8 ≤ count1357 b) else decide (9 ≤ count1357 b))) else (if i < 1367 then decide (10 ≤ count1357 b) else (if i < 1368 then decide (11 ≤ count1357 b) else decide (12 ≤ count1357 b))))) else (if i < 1374 then (if i < 1371 then (if i < 1370 then decide (13 ≤ count1357 b) else decide (1 ≤ count1370 b)) else (if i < 1372 then decide (2 ≤ count1370 b) else (if i < 1373 then decide (1 ≤ count1372 b) else decide (2 ≤ count1372 b)))) else (if i < 1377 then (if i < 1375 then decide (3 ≤ count1372 b) else (if i < 1376 then decide (1 ≤ count1375 b) else decide (2 ≤ count1375 b))) else (if i < 1378 then decide (1 ≤ count1377 b) else (if i < 1379 then decide (2 ≤ count1377 b) else decide (1 ≤ count1379 b)))))) else (if i < 1391 then (if i < 1385 then (if i < 1382 then (if i < 1381 then decide (2 ≤ count1379 b) else decide (3 ≤ count1379 b)) else (if i < 1383 then decide (4 ≤ count1379 b) else (if i < 1384 then decide (1 ≤ count1383 b) else decide (2 ≤ count1383 b)))) else (if i < 1388 then (if i < 1386 then decide (3 ≤ count1383 b) else (if i < 1387 then decide (4 ≤ count1383 b) else decide (5 ≤ count1383 b))) else (if i < 1389 then decide (6 ≤ count1383 b) else (if i < 1390 then decide (7 ≤ count1383 b) else decide (1 ≤ count1390 b))))) else (if i < 1397 then (if i < 1394 then (if i < 1392 then decide (2 ≤ count1390 b) else (if i < 1393 then decide (1 ≤ count1392 b) else decide (2 ≤ count1392 b))) else (if i < 1395 then decide (3 ≤ count1392 b) else (if i < 1396 then decide (1 ≤ count1395 b) else decide (2 ≤ count1395 b)))) else (if i < 1400 then (if i < 1398 then decide (1 ≤ count1397 b) else (if i < 1399 then decide (2 ≤ count1397 b) else decide (1 ≤ count1399 b))) else (if i < 1401 then decide (2 ≤ count1399 b) else (if i < 1402 then decide (3 ≤ count1399 b) else decide (4 ≤ count1399 b))))))) else (if i < 1426 then (if i < 1414 then (if i < 1408 then (if i < 1405 then (if i < 1404 then decide (1 ≤ count1403 b) else decide (2 ≤ count1403 b)) else (if i < 1406 then decide (3 ≤ count1403 b) else (if i < 1407 then decide (4 ≤ count1403 b) else decide (5 ≤ count1403 b)))) else (if i < 1411 then (if i < 1409 then decide (6 ≤ count1403 b) else (if i < 1410 then decide (7 ≤ count1403 b) else decide (1 ≤ count1410 b))) else (if i < 1412 then decide (2 ≤ count1410 b) else (if i < 1413 then decide (3 ≤ count1410 b) else decide (4 ≤ count1410 b))))) else (if i < 1420 then (if i < 1417 then (if i < 1415 then decide (5 ≤ count1410 b) else (if i < 1416 then decide (6 ≤ count1410 b) else decide (7 ≤ count1410 b))) else (if i < 1418 then decide (8 ≤ count1410 b) else (if i < 1419 then decide (9 ≤ count1410 b) else decide (10 ≤ count1410 b)))) else (if i < 1423 then (if i < 1421 then decide (11 ≤ count1410 b) else (if i < 1422 then decide (12 ≤ count1410 b) else decide (13 ≤ count1410 b))) else (if i < 1424 then decide (1 ≤ count1423 b) else (if i < 1425 then decide (2 ≤ count1423 b) else decide (3 ≤ count1423 b)))))) else (if i < 1437 then (if i < 1431 then (if i < 1428 then (if i < 1427 then decide (4 ≤ count1423 b) else decide (5 ≤ count1423 b)) else (if i < 1429 then decide (6 ≤ count1423 b) else (if i < 1430 then decide (7 ≤ count1423 b) else decide (8 ≤ count1423 b)))) else (if i < 1434 then (if i < 1432 then decide (9 ≤ count1423 b) else (if i < 1433 then decide (10 ≤ count1423 b) else decide (11 ≤ count1423 b))) else (if i < 1435 then decide (12 ≤ count1423 b) else (if i < 1436 then decide (13 ≤ count1423 b) else decide (1 ≤ count1436 b))))) else (if i < 1443 then (if i < 1440 then (if i < 1438 then decide (2 ≤ count1436 b) else (if i < 1439 then decide (3 ≤ count1436 b) else decide (4 ≤ count1436 b))) else (if i < 1441 then decide (5 ≤ count1436 b) else (if i < 1442 then decide (6 ≤ count1436 b) else decide (7 ≤ count1436 b)))) else (if i < 1446 then (if i < 1444 then decide (8 ≤ count1436 b) else (if i < 1445 then decide (9 ≤ count1436 b) else decide (10 ≤ count1436 b))) else (if i < 1447 then decide (11 ≤ count1436 b) else (if i < 1448 then decide (12 ≤ count1436 b) else decide (13 ≤ count1436 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (18 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (20 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (22 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (24 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (26 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (28 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (69 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (73 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (82 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (84 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (85 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (89 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (91 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (92 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (93 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (130 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (133 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (134 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (135 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (136 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (137 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (138 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (142 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (146 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (147 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (148 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (149 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (153 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (155 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (156 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (157 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (226 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (229 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (230 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (233 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (234 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (242 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (243 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (244 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (245 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (249 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (251 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (252 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (253 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (289 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (291 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (307 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (354 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (357 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (358 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (361 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (362 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (370 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (371 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (372 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (373 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (377 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (379 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (380 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (384 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (385 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (387 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (393 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (395 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (397 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (398 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (399 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (400 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (402 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (403 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (404 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (406 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (408 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (410 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (412 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (413 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (414 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (450 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (456 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (457 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (458 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (462 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (466 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (473 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (475 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (476 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (477 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (498 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (502 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (504 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (506 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (508 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (24 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (26 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (91 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (146 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (147 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (157 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (242 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (243 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (291 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (357 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (358 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (361 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (372 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (373 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (377 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (380 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (395 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (398 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (400 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (408 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (450 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (456 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (466 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (473 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (476 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (477 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (504 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (1 ≤ count217 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value260 (q : Snake 81) : valuation q 260 = decide (2 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value300 (q : Snake 81) : valuation q 300 = decide (2 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
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
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value697 (q : Snake 81) : valuation q 697 = decide (1 ≤ count697 (baseVal q)) := rfl
theorem value700 (q : Snake 81) : valuation q 700 = decide (2 ≤ count699 (baseVal q)) := rfl
theorem value708 (q : Snake 81) : valuation q 708 = decide (2 ≤ count707 (baseVal q)) := rfl
theorem value718 (q : Snake 81) : valuation q 718 = decide (1 ≤ count718 (baseVal q)) := rfl
theorem value720 (q : Snake 81) : valuation q 720 = decide (1 ≤ count720 (baseVal q)) := rfl
theorem value723 (q : Snake 81) : valuation q 723 = decide (1 ≤ count723 (baseVal q)) := rfl
theorem value729 (q : Snake 81) : valuation q 729 = decide (1 ≤ count729 (baseVal q)) := rfl
theorem value730 (q : Snake 81) : valuation q 730 = decide (2 ≤ count729 (baseVal q)) := rfl
theorem value740 (q : Snake 81) : valuation q 740 = decide (1 ≤ count740 (baseVal q)) := rfl
theorem value741 (q : Snake 81) : valuation q 741 = decide (2 ≤ count740 (baseVal q)) := rfl
theorem value742 (q : Snake 81) : valuation q 742 = decide (1 ≤ count742 (baseVal q)) := rfl
theorem value744 (q : Snake 81) : valuation q 744 = decide (3 ≤ count742 (baseVal q)) := rfl
theorem value745 (q : Snake 81) : valuation q 745 = decide (1 ≤ count745 (baseVal q)) := rfl
theorem value747 (q : Snake 81) : valuation q 747 = decide (1 ≤ count747 (baseVal q)) := rfl
theorem value750 (q : Snake 81) : valuation q 750 = decide (1 ≤ count750 (baseVal q)) := rfl
theorem value753 (q : Snake 81) : valuation q 753 = decide (4 ≤ count750 (baseVal q)) := rfl
theorem value758 (q : Snake 81) : valuation q 758 = decide (1 ≤ count758 (baseVal q)) := rfl
theorem value763 (q : Snake 81) : valuation q 763 = decide (1 ≤ count763 (baseVal q)) := rfl
theorem value765 (q : Snake 81) : valuation q 765 = decide (1 ≤ count765 (baseVal q)) := rfl
theorem value769 (q : Snake 81) : valuation q 769 = decide (1 ≤ count769 (baseVal q)) := rfl
theorem value770 (q : Snake 81) : valuation q 770 = decide (2 ≤ count769 (baseVal q)) := rfl
theorem value777 (q : Snake 81) : valuation q 777 = decide (2 ≤ count776 (baseVal q)) := rfl
theorem value778 (q : Snake 81) : valuation q 778 = decide (3 ≤ count776 (baseVal q)) := rfl
theorem value780 (q : Snake 81) : valuation q 780 = decide (5 ≤ count776 (baseVal q)) := rfl
theorem value790 (q : Snake 81) : valuation q 790 = decide (4 ≤ count787 (baseVal q)) := rfl
theorem value791 (q : Snake 81) : valuation q 791 = decide (5 ≤ count787 (baseVal q)) := rfl
theorem value792 (q : Snake 81) : valuation q 792 = decide (6 ≤ count787 (baseVal q)) := rfl
theorem value845 (q : Snake 81) : valuation q 845 = decide (1 ≤ count845 (baseVal q)) := rfl
theorem value848 (q : Snake 81) : valuation q 848 = decide (2 ≤ count847 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (1 ≤ count850 (baseVal q)) := rfl
theorem value852 (q : Snake 81) : valuation q 852 = decide (1 ≤ count852 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (3 ≤ count855 (baseVal q)) := rfl
theorem value862 (q : Snake 81) : valuation q 862 = decide (2 ≤ count861 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (3 ≤ count863 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (1 ≤ count866 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (2 ≤ count866 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (1 ≤ count868 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (1 ≤ count870 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (2 ≤ count870 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (3 ≤ count874 (baseVal q)) := rfl
theorem value877 (q : Snake 81) : valuation q 877 = decide (4 ≤ count874 (baseVal q)) := rfl
theorem value878 (q : Snake 81) : valuation q 878 = decide (5 ≤ count874 (baseVal q)) := rfl
theorem value885 (q : Snake 81) : valuation q 885 = decide (5 ≤ count881 (baseVal q)) := rfl
theorem value886 (q : Snake 81) : valuation q 886 = decide (6 ≤ count881 (baseVal q)) := rfl
theorem value887 (q : Snake 81) : valuation q 887 = decide (7 ≤ count881 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (5 ≤ count892 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (6 ≤ count892 (baseVal q)) := rfl
theorem value898 (q : Snake 81) : valuation q 898 = decide (7 ≤ count892 (baseVal q)) := rfl
theorem value913 (q : Snake 81) : valuation q 913 = decide (11 ≤ count903 (baseVal q)) := rfl
theorem value1210 (q : Snake 81) : valuation q 1210 = decide (1 ≤ count1210 (baseVal q)) := rfl
theorem value1211 (q : Snake 81) : valuation q 1211 = decide (2 ≤ count1210 (baseVal q)) := rfl
theorem value1212 (q : Snake 81) : valuation q 1212 = decide (1 ≤ count1212 (baseVal q)) := rfl
theorem value1213 (q : Snake 81) : valuation q 1213 = decide (2 ≤ count1212 (baseVal q)) := rfl
theorem value1215 (q : Snake 81) : valuation q 1215 = decide (1 ≤ count1215 (baseVal q)) := rfl
theorem value1217 (q : Snake 81) : valuation q 1217 = decide (1 ≤ count1217 (baseVal q)) := rfl
theorem value1218 (q : Snake 81) : valuation q 1218 = decide (2 ≤ count1217 (baseVal q)) := rfl
theorem value1220 (q : Snake 81) : valuation q 1220 = decide (1 ≤ count1220 (baseVal q)) := rfl
theorem value1221 (q : Snake 81) : valuation q 1221 = decide (2 ≤ count1220 (baseVal q)) := rfl
theorem value1222 (q : Snake 81) : valuation q 1222 = decide (3 ≤ count1220 (baseVal q)) := rfl
theorem value1226 (q : Snake 81) : valuation q 1226 = decide (1 ≤ count1226 (baseVal q)) := rfl
theorem value1227 (q : Snake 81) : valuation q 1227 = decide (2 ≤ count1226 (baseVal q)) := rfl
theorem value1228 (q : Snake 81) : valuation q 1228 = decide (1 ≤ count1228 (baseVal q)) := rfl
theorem value1229 (q : Snake 81) : valuation q 1229 = decide (2 ≤ count1228 (baseVal q)) := rfl
theorem value1231 (q : Snake 81) : valuation q 1231 = decide (1 ≤ count1231 (baseVal q)) := rfl
theorem value1233 (q : Snake 81) : valuation q 1233 = decide (1 ≤ count1233 (baseVal q)) := rfl
theorem value1234 (q : Snake 81) : valuation q 1234 = decide (2 ≤ count1233 (baseVal q)) := rfl
theorem value1235 (q : Snake 81) : valuation q 1235 = decide (1 ≤ count1235 (baseVal q)) := rfl
theorem value1236 (q : Snake 81) : valuation q 1236 = decide (2 ≤ count1235 (baseVal q)) := rfl
theorem value1237 (q : Snake 81) : valuation q 1237 = decide (3 ≤ count1235 (baseVal q)) := rfl
theorem value1239 (q : Snake 81) : valuation q 1239 = decide (1 ≤ count1239 (baseVal q)) := rfl
theorem value1240 (q : Snake 81) : valuation q 1240 = decide (2 ≤ count1239 (baseVal q)) := rfl
theorem value1241 (q : Snake 81) : valuation q 1241 = decide (3 ≤ count1239 (baseVal q)) := rfl
theorem value1247 (q : Snake 81) : valuation q 1247 = decide (2 ≤ count1246 (baseVal q)) := rfl
theorem value1248 (q : Snake 81) : valuation q 1248 = decide (3 ≤ count1246 (baseVal q)) := rfl
theorem value1249 (q : Snake 81) : valuation q 1249 = decide (4 ≤ count1246 (baseVal q)) := rfl
theorem value1259 (q : Snake 81) : valuation q 1259 = decide (1 ≤ count1259 (baseVal q)) := rfl
theorem value1260 (q : Snake 81) : valuation q 1260 = decide (2 ≤ count1259 (baseVal q)) := rfl
theorem value1261 (q : Snake 81) : valuation q 1261 = decide (1 ≤ count1261 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (2 ≤ count1261 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (3 ≤ count1261 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (1 ≤ count1264 (baseVal q)) := rfl
theorem value1265 (q : Snake 81) : valuation q 1265 = decide (2 ≤ count1264 (baseVal q)) := rfl
theorem value1266 (q : Snake 81) : valuation q 1266 = decide (1 ≤ count1266 (baseVal q)) := rfl
theorem value1267 (q : Snake 81) : valuation q 1267 = decide (2 ≤ count1266 (baseVal q)) := rfl
theorem value1269 (q : Snake 81) : valuation q 1269 = decide (1 ≤ count1269 (baseVal q)) := rfl
theorem value1270 (q : Snake 81) : valuation q 1270 = decide (2 ≤ count1269 (baseVal q)) := rfl
theorem value1271 (q : Snake 81) : valuation q 1271 = decide (3 ≤ count1269 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (4 ≤ count1269 (baseVal q)) := rfl
theorem value1275 (q : Snake 81) : valuation q 1275 = decide (1 ≤ count1275 (baseVal q)) := rfl
theorem value1277 (q : Snake 81) : valuation q 1277 = decide (1 ≤ count1277 (baseVal q)) := rfl
theorem value1280 (q : Snake 81) : valuation q 1280 = decide (1 ≤ count1280 (baseVal q)) := rfl
theorem value1282 (q : Snake 81) : valuation q 1282 = decide (1 ≤ count1282 (baseVal q)) := rfl
theorem value1283 (q : Snake 81) : valuation q 1283 = decide (2 ≤ count1282 (baseVal q)) := rfl
theorem value1284 (q : Snake 81) : valuation q 1284 = decide (1 ≤ count1284 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (2 ≤ count1284 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (3 ≤ count1284 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (1 ≤ count1288 (baseVal q)) := rfl
theorem value1289 (q : Snake 81) : valuation q 1289 = decide (2 ≤ count1288 (baseVal q)) := rfl
theorem value1290 (q : Snake 81) : valuation q 1290 = decide (3 ≤ count1288 (baseVal q)) := rfl
theorem value1295 (q : Snake 81) : valuation q 1295 = decide (1 ≤ count1295 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (2 ≤ count1295 (baseVal q)) := rfl
theorem value1297 (q : Snake 81) : valuation q 1297 = decide (3 ≤ count1295 (baseVal q)) := rfl
theorem value1298 (q : Snake 81) : valuation q 1298 = decide (4 ≤ count1295 (baseVal q)) := rfl
theorem value1299 (q : Snake 81) : valuation q 1299 = decide (5 ≤ count1295 (baseVal q)) := rfl
theorem value1300 (q : Snake 81) : valuation q 1300 = decide (6 ≤ count1295 (baseVal q)) := rfl
theorem value1310 (q : Snake 81) : valuation q 1310 = decide (3 ≤ count1308 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (4 ≤ count1308 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (5 ≤ count1308 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (6 ≤ count1308 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (7 ≤ count1308 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (8 ≤ count1308 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (1 ≤ count1321 (baseVal q)) := rfl
theorem value1323 (q : Snake 81) : valuation q 1323 = decide (1 ≤ count1323 (baseVal q)) := rfl
theorem value1324 (q : Snake 81) : valuation q 1324 = decide (2 ≤ count1323 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (1 ≤ count1326 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (2 ≤ count1326 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (1 ≤ count1328 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (2 ≤ count1328 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (1 ≤ count1331 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (2 ≤ count1331 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (3 ≤ count1331 (baseVal q)) := rfl
theorem value1337 (q : Snake 81) : valuation q 1337 = decide (1 ≤ count1337 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (2 ≤ count1337 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (1 ≤ count1339 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (2 ≤ count1339 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (1 ≤ count1342 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (1 ≤ count1344 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (2 ≤ count1344 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (1 ≤ count1346 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (2 ≤ count1346 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (1 ≤ count1350 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (2 ≤ count1350 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (3 ≤ count1350 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (1 ≤ count1357 (baseVal q)) := rfl
theorem value1358 (q : Snake 81) : valuation q 1358 = decide (2 ≤ count1357 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (3 ≤ count1357 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (4 ≤ count1357 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (1 ≤ count1370 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (2 ≤ count1370 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (1 ≤ count1372 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (2 ≤ count1372 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (3 ≤ count1372 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (1 ≤ count1375 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (2 ≤ count1375 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (1 ≤ count1377 (baseVal q)) := rfl
theorem value1378 (q : Snake 81) : valuation q 1378 = decide (2 ≤ count1377 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (1 ≤ count1379 (baseVal q)) := rfl
theorem value1380 (q : Snake 81) : valuation q 1380 = decide (2 ≤ count1379 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (3 ≤ count1379 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (1 ≤ count1383 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (2 ≤ count1383 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (3 ≤ count1383 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (4 ≤ count1383 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (5 ≤ count1383 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (1 ≤ count1390 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (2 ≤ count1390 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (1 ≤ count1392 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (2 ≤ count1392 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (3 ≤ count1392 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (1 ≤ count1395 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (2 ≤ count1395 (baseVal q)) := rfl
theorem value1397 (q : Snake 81) : valuation q 1397 = decide (1 ≤ count1397 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (2 ≤ count1397 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (1 ≤ count1399 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (2 ≤ count1399 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (3 ≤ count1399 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (2 ≤ count1403 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (3 ≤ count1403 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (4 ≤ count1403 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (5 ≤ count1403 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (3 ≤ count1410 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (4 ≤ count1410 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (5 ≤ count1410 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (6 ≤ count1410 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (7 ≤ count1410 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (5 ≤ count1423 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (6 ≤ count1423 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (7 ≤ count1423 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (8 ≤ count1423 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (9 ≤ count1423 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (10 ≤ count1423 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (13 ≤ count1436 (baseVal q)) := rfl
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
theorem meaningNeg15 (b : Nat → Bool) : literal (valuationOf b) (-15) = decide (1 ≤ countLit b [-15]) := by
  change literal b (-15) = decide (1 ≤ countLit b [-15])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-15) <;> decide
theorem meaningNeg12 (b : Nat → Bool) : literal (valuationOf b) (-12) = decide (1 ≤ countLit b [-12]) := by
  change literal b (-12) = decide (1 ≤ countLit b [-12])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-12) <;> decide
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
theorem meaning108 (b : Nat → Bool) : literal (valuationOf b) (108) = decide (1 ≤ countLit b [108]) := by
  change literal b (108) = decide (1 ≤ countLit b [108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (108) <;> decide
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
theorem meaning131 (b : Nat → Bool) : literal (valuationOf b) (131) = decide (1 ≤ countLit b [131]) := by
  change literal b (131) = decide (1 ≤ countLit b [131])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (131) <;> decide
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
theorem meaning152 (b : Nat → Bool) : literal (valuationOf b) (152) = decide (1 ≤ countLit b [152]) := by
  change literal b (152) = decide (1 ≤ countLit b [152])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (152) <;> decide
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
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
theorem meaning173 (b : Nat → Bool) : literal (valuationOf b) (173) = decide (1 ≤ countLit b [173]) := by
  change literal b (173) = decide (1 ≤ countLit b [173])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (173) <;> decide
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
theorem meaning183 (b : Nat → Bool) : literal (valuationOf b) (183) = decide (1 ≤ countLit b [183]) := by
  change literal b (183) = decide (1 ≤ countLit b [183])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (183) <;> decide
theorem meaning189 (b : Nat → Bool) : literal (valuationOf b) (189) = decide (1 ≤ countLit b [189]) := by
  change literal b (189) = decide (1 ≤ countLit b [189])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (189) <;> decide
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
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
theorem meaning200 (b : Nat → Bool) : literal (valuationOf b) (200) = decide (1 ≤ countLit b [200]) := by
  change literal b (200) = decide (1 ≤ countLit b [200])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (200) <;> decide
theorem meaning202 (b : Nat → Bool) : literal (valuationOf b) (202) = decide (1 ≤ countLit b [202]) := by
  change literal b (202) = decide (1 ≤ countLit b [202])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (202) <;> decide
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
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) 215 = decide (1 ≤ count215 b) := rfl
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) 217 = decide (1 ≤ count217 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning260 (b : Nat → Bool) : literal (valuationOf b) 260 = decide (2 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning300 (b : Nat → Bool) : literal (valuationOf b) 300 = decide (2 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
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
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning697 (b : Nat → Bool) : literal (valuationOf b) 697 = decide (1 ≤ count697 b) := rfl
theorem meaning700 (b : Nat → Bool) : literal (valuationOf b) 700 = decide (2 ≤ count699 b) := rfl
theorem meaning708 (b : Nat → Bool) : literal (valuationOf b) 708 = decide (2 ≤ count707 b) := rfl
theorem meaning718 (b : Nat → Bool) : literal (valuationOf b) 718 = decide (1 ≤ count718 b) := rfl
theorem meaning720 (b : Nat → Bool) : literal (valuationOf b) 720 = decide (1 ≤ count720 b) := rfl
theorem meaning723 (b : Nat → Bool) : literal (valuationOf b) 723 = decide (1 ≤ count723 b) := rfl
theorem meaning729 (b : Nat → Bool) : literal (valuationOf b) 729 = decide (1 ≤ count729 b) := rfl
theorem meaning730 (b : Nat → Bool) : literal (valuationOf b) 730 = decide (2 ≤ count729 b) := rfl
theorem meaning740 (b : Nat → Bool) : literal (valuationOf b) 740 = decide (1 ≤ count740 b) := rfl
theorem meaning741 (b : Nat → Bool) : literal (valuationOf b) 741 = decide (2 ≤ count740 b) := rfl
theorem meaning742 (b : Nat → Bool) : literal (valuationOf b) 742 = decide (1 ≤ count742 b) := rfl
theorem meaning744 (b : Nat → Bool) : literal (valuationOf b) 744 = decide (3 ≤ count742 b) := rfl
theorem meaning745 (b : Nat → Bool) : literal (valuationOf b) 745 = decide (1 ≤ count745 b) := rfl
theorem meaning747 (b : Nat → Bool) : literal (valuationOf b) 747 = decide (1 ≤ count747 b) := rfl
theorem meaning750 (b : Nat → Bool) : literal (valuationOf b) 750 = decide (1 ≤ count750 b) := rfl
theorem meaning753 (b : Nat → Bool) : literal (valuationOf b) 753 = decide (4 ≤ count750 b) := rfl
theorem meaning758 (b : Nat → Bool) : literal (valuationOf b) 758 = decide (1 ≤ count758 b) := rfl
theorem meaning763 (b : Nat → Bool) : literal (valuationOf b) 763 = decide (1 ≤ count763 b) := rfl
theorem meaning765 (b : Nat → Bool) : literal (valuationOf b) 765 = decide (1 ≤ count765 b) := rfl
theorem meaning769 (b : Nat → Bool) : literal (valuationOf b) 769 = decide (1 ≤ count769 b) := rfl
theorem meaning770 (b : Nat → Bool) : literal (valuationOf b) 770 = decide (2 ≤ count769 b) := rfl
theorem meaning777 (b : Nat → Bool) : literal (valuationOf b) 777 = decide (2 ≤ count776 b) := rfl
theorem meaning778 (b : Nat → Bool) : literal (valuationOf b) 778 = decide (3 ≤ count776 b) := rfl
theorem meaning780 (b : Nat → Bool) : literal (valuationOf b) 780 = decide (5 ≤ count776 b) := rfl
theorem meaning790 (b : Nat → Bool) : literal (valuationOf b) 790 = decide (4 ≤ count787 b) := rfl
theorem meaning791 (b : Nat → Bool) : literal (valuationOf b) 791 = decide (5 ≤ count787 b) := rfl
theorem meaning792 (b : Nat → Bool) : literal (valuationOf b) 792 = decide (6 ≤ count787 b) := rfl
theorem meaning845 (b : Nat → Bool) : literal (valuationOf b) 845 = decide (1 ≤ count845 b) := rfl
theorem meaning848 (b : Nat → Bool) : literal (valuationOf b) 848 = decide (2 ≤ count847 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (1 ≤ count850 b) := rfl
theorem meaning852 (b : Nat → Bool) : literal (valuationOf b) 852 = decide (1 ≤ count852 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (3 ≤ count855 b) := rfl
theorem meaning862 (b : Nat → Bool) : literal (valuationOf b) 862 = decide (2 ≤ count861 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (3 ≤ count863 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (1 ≤ count866 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (2 ≤ count866 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (1 ≤ count868 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (1 ≤ count870 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (2 ≤ count870 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (3 ≤ count874 b) := rfl
theorem meaning877 (b : Nat → Bool) : literal (valuationOf b) 877 = decide (4 ≤ count874 b) := rfl
theorem meaning878 (b : Nat → Bool) : literal (valuationOf b) 878 = decide (5 ≤ count874 b) := rfl
theorem meaning885 (b : Nat → Bool) : literal (valuationOf b) 885 = decide (5 ≤ count881 b) := rfl
theorem meaning886 (b : Nat → Bool) : literal (valuationOf b) 886 = decide (6 ≤ count881 b) := rfl
theorem meaning887 (b : Nat → Bool) : literal (valuationOf b) 887 = decide (7 ≤ count881 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (5 ≤ count892 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (6 ≤ count892 b) := rfl
theorem meaning898 (b : Nat → Bool) : literal (valuationOf b) 898 = decide (7 ≤ count892 b) := rfl
theorem meaning913 (b : Nat → Bool) : literal (valuationOf b) 913 = decide (11 ≤ count903 b) := rfl
theorem meaning1210 (b : Nat → Bool) : literal (valuationOf b) 1210 = decide (1 ≤ count1210 b) := rfl
theorem meaning1211 (b : Nat → Bool) : literal (valuationOf b) 1211 = decide (2 ≤ count1210 b) := rfl
theorem meaning1212 (b : Nat → Bool) : literal (valuationOf b) 1212 = decide (1 ≤ count1212 b) := rfl
theorem meaning1213 (b : Nat → Bool) : literal (valuationOf b) 1213 = decide (2 ≤ count1212 b) := rfl
theorem meaning1215 (b : Nat → Bool) : literal (valuationOf b) 1215 = decide (1 ≤ count1215 b) := rfl
theorem meaning1217 (b : Nat → Bool) : literal (valuationOf b) 1217 = decide (1 ≤ count1217 b) := rfl
theorem meaning1218 (b : Nat → Bool) : literal (valuationOf b) 1218 = decide (2 ≤ count1217 b) := rfl
theorem meaning1220 (b : Nat → Bool) : literal (valuationOf b) 1220 = decide (1 ≤ count1220 b) := rfl
theorem meaning1221 (b : Nat → Bool) : literal (valuationOf b) 1221 = decide (2 ≤ count1220 b) := rfl
theorem meaning1222 (b : Nat → Bool) : literal (valuationOf b) 1222 = decide (3 ≤ count1220 b) := rfl
theorem meaning1226 (b : Nat → Bool) : literal (valuationOf b) 1226 = decide (1 ≤ count1226 b) := rfl
theorem meaning1227 (b : Nat → Bool) : literal (valuationOf b) 1227 = decide (2 ≤ count1226 b) := rfl
theorem meaning1228 (b : Nat → Bool) : literal (valuationOf b) 1228 = decide (1 ≤ count1228 b) := rfl
theorem meaning1229 (b : Nat → Bool) : literal (valuationOf b) 1229 = decide (2 ≤ count1228 b) := rfl
theorem meaning1231 (b : Nat → Bool) : literal (valuationOf b) 1231 = decide (1 ≤ count1231 b) := rfl
theorem meaning1233 (b : Nat → Bool) : literal (valuationOf b) 1233 = decide (1 ≤ count1233 b) := rfl
theorem meaning1234 (b : Nat → Bool) : literal (valuationOf b) 1234 = decide (2 ≤ count1233 b) := rfl
theorem meaning1235 (b : Nat → Bool) : literal (valuationOf b) 1235 = decide (1 ≤ count1235 b) := rfl
theorem meaning1236 (b : Nat → Bool) : literal (valuationOf b) 1236 = decide (2 ≤ count1235 b) := rfl
theorem meaning1237 (b : Nat → Bool) : literal (valuationOf b) 1237 = decide (3 ≤ count1235 b) := rfl
theorem meaning1239 (b : Nat → Bool) : literal (valuationOf b) 1239 = decide (1 ≤ count1239 b) := rfl
theorem meaning1240 (b : Nat → Bool) : literal (valuationOf b) 1240 = decide (2 ≤ count1239 b) := rfl
theorem meaning1241 (b : Nat → Bool) : literal (valuationOf b) 1241 = decide (3 ≤ count1239 b) := rfl
theorem meaning1247 (b : Nat → Bool) : literal (valuationOf b) 1247 = decide (2 ≤ count1246 b) := rfl
theorem meaning1248 (b : Nat → Bool) : literal (valuationOf b) 1248 = decide (3 ≤ count1246 b) := rfl
theorem meaning1249 (b : Nat → Bool) : literal (valuationOf b) 1249 = decide (4 ≤ count1246 b) := rfl
theorem meaning1259 (b : Nat → Bool) : literal (valuationOf b) 1259 = decide (1 ≤ count1259 b) := rfl
theorem meaning1260 (b : Nat → Bool) : literal (valuationOf b) 1260 = decide (2 ≤ count1259 b) := rfl
theorem meaning1261 (b : Nat → Bool) : literal (valuationOf b) 1261 = decide (1 ≤ count1261 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (2 ≤ count1261 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (3 ≤ count1261 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (1 ≤ count1264 b) := rfl
theorem meaning1265 (b : Nat → Bool) : literal (valuationOf b) 1265 = decide (2 ≤ count1264 b) := rfl
theorem meaning1266 (b : Nat → Bool) : literal (valuationOf b) 1266 = decide (1 ≤ count1266 b) := rfl
theorem meaning1267 (b : Nat → Bool) : literal (valuationOf b) 1267 = decide (2 ≤ count1266 b) := rfl
theorem meaning1269 (b : Nat → Bool) : literal (valuationOf b) 1269 = decide (1 ≤ count1269 b) := rfl
theorem meaning1270 (b : Nat → Bool) : literal (valuationOf b) 1270 = decide (2 ≤ count1269 b) := rfl
theorem meaning1271 (b : Nat → Bool) : literal (valuationOf b) 1271 = decide (3 ≤ count1269 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (4 ≤ count1269 b) := rfl
theorem meaning1275 (b : Nat → Bool) : literal (valuationOf b) 1275 = decide (1 ≤ count1275 b) := rfl
theorem meaning1277 (b : Nat → Bool) : literal (valuationOf b) 1277 = decide (1 ≤ count1277 b) := rfl
theorem meaning1280 (b : Nat → Bool) : literal (valuationOf b) 1280 = decide (1 ≤ count1280 b) := rfl
theorem meaning1282 (b : Nat → Bool) : literal (valuationOf b) 1282 = decide (1 ≤ count1282 b) := rfl
theorem meaning1283 (b : Nat → Bool) : literal (valuationOf b) 1283 = decide (2 ≤ count1282 b) := rfl
theorem meaning1284 (b : Nat → Bool) : literal (valuationOf b) 1284 = decide (1 ≤ count1284 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (2 ≤ count1284 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (3 ≤ count1284 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (1 ≤ count1288 b) := rfl
theorem meaning1289 (b : Nat → Bool) : literal (valuationOf b) 1289 = decide (2 ≤ count1288 b) := rfl
theorem meaning1290 (b : Nat → Bool) : literal (valuationOf b) 1290 = decide (3 ≤ count1288 b) := rfl
theorem meaning1295 (b : Nat → Bool) : literal (valuationOf b) 1295 = decide (1 ≤ count1295 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (2 ≤ count1295 b) := rfl
theorem meaning1297 (b : Nat → Bool) : literal (valuationOf b) 1297 = decide (3 ≤ count1295 b) := rfl
theorem meaning1298 (b : Nat → Bool) : literal (valuationOf b) 1298 = decide (4 ≤ count1295 b) := rfl
theorem meaning1299 (b : Nat → Bool) : literal (valuationOf b) 1299 = decide (5 ≤ count1295 b) := rfl
theorem meaning1300 (b : Nat → Bool) : literal (valuationOf b) 1300 = decide (6 ≤ count1295 b) := rfl
theorem meaning1310 (b : Nat → Bool) : literal (valuationOf b) 1310 = decide (3 ≤ count1308 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (4 ≤ count1308 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (5 ≤ count1308 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (6 ≤ count1308 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (7 ≤ count1308 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (8 ≤ count1308 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (1 ≤ count1321 b) := rfl
theorem meaning1323 (b : Nat → Bool) : literal (valuationOf b) 1323 = decide (1 ≤ count1323 b) := rfl
theorem meaning1324 (b : Nat → Bool) : literal (valuationOf b) 1324 = decide (2 ≤ count1323 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (1 ≤ count1326 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (2 ≤ count1326 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (1 ≤ count1328 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (2 ≤ count1328 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (1 ≤ count1331 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (2 ≤ count1331 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (3 ≤ count1331 b) := rfl
theorem meaning1337 (b : Nat → Bool) : literal (valuationOf b) 1337 = decide (1 ≤ count1337 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (2 ≤ count1337 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (1 ≤ count1339 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (2 ≤ count1339 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (1 ≤ count1342 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (1 ≤ count1344 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (2 ≤ count1344 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (1 ≤ count1346 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (2 ≤ count1346 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (1 ≤ count1350 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (2 ≤ count1350 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (3 ≤ count1350 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (1 ≤ count1357 b) := rfl
theorem meaning1358 (b : Nat → Bool) : literal (valuationOf b) 1358 = decide (2 ≤ count1357 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (3 ≤ count1357 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (4 ≤ count1357 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (1 ≤ count1370 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (2 ≤ count1370 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (1 ≤ count1372 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (2 ≤ count1372 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (3 ≤ count1372 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (1 ≤ count1375 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (2 ≤ count1375 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (1 ≤ count1377 b) := rfl
theorem meaning1378 (b : Nat → Bool) : literal (valuationOf b) 1378 = decide (2 ≤ count1377 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (1 ≤ count1379 b) := rfl
theorem meaning1380 (b : Nat → Bool) : literal (valuationOf b) 1380 = decide (2 ≤ count1379 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (3 ≤ count1379 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (1 ≤ count1383 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (2 ≤ count1383 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (3 ≤ count1383 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (4 ≤ count1383 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (5 ≤ count1383 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (1 ≤ count1390 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (2 ≤ count1390 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (1 ≤ count1392 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (2 ≤ count1392 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (3 ≤ count1392 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (1 ≤ count1395 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (2 ≤ count1395 b) := rfl
theorem meaning1397 (b : Nat → Bool) : literal (valuationOf b) 1397 = decide (1 ≤ count1397 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (2 ≤ count1397 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (1 ≤ count1399 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (2 ≤ count1399 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (3 ≤ count1399 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (2 ≤ count1403 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (3 ≤ count1403 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (4 ≤ count1403 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (5 ≤ count1403 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (3 ≤ count1410 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (4 ≤ count1410 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (5 ≤ count1410 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (6 ≤ count1410 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (7 ≤ count1410 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (5 ≤ count1423 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (6 ≤ count1423 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (7 ≤ count1423 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (8 ≤ count1423 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (9 ≤ count1423 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (10 ≤ count1423 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (13 ≤ count1436 b) := rfl
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
end Snake9.Regrowth.E112094
