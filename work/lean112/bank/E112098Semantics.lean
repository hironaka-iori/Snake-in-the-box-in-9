import E112098Data
namespace Snake9.Regrowth.E112098
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 101 then (if i < 50 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (18 : Vertex)) else decide (InPath q (68 : Vertex)))) else (if i < 4 then decide (InPath q (69 : Vertex)) else (if i < 5 then decide (InPath q (70 : Vertex)) else decide (InPath q (72 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (73 : Vertex)) else (if i < 8 then decide (InPath q (74 : Vertex)) else decide (InPath q (78 : Vertex)))) else (if i < 10 then decide (InPath q (82 : Vertex)) else (if i < 11 then decide (InPath q (83 : Vertex)) else decide (InPath q (84 : Vertex)))))) else (if i < 18 then (if i < 15 then (if i < 13 then decide (InPath q (85 : Vertex)) else (if i < 14 then decide (InPath q (90 : Vertex)) else decide (InPath q (91 : Vertex)))) else (if i < 16 then decide (InPath q (93 : Vertex)) else (if i < 17 then decide (InPath q (95 : Vertex)) else decide (InPath q (132 : Vertex))))) else (if i < 21 then (if i < 19 then decide (InPath q (133 : Vertex)) else (if i < 20 then decide (InPath q (134 : Vertex)) else decide (InPath q (136 : Vertex)))) else (if i < 23 then (if i < 22 then decide (InPath q (137 : Vertex)) else decide (InPath q (138 : Vertex))) else (if i < 24 then decide (InPath q (142 : Vertex)) else decide (InPath q (146 : Vertex))))))) else (if i < 37 then (if i < 31 then (if i < 28 then (if i < 26 then decide (InPath q (147 : Vertex)) else (if i < 27 then decide (InPath q (148 : Vertex)) else decide (InPath q (149 : Vertex)))) else (if i < 29 then decide (InPath q (154 : Vertex)) else (if i < 30 then decide (InPath q (155 : Vertex)) else decide (InPath q (157 : Vertex))))) else (if i < 34 then (if i < 32 then decide (InPath q (159 : Vertex)) else (if i < 33 then decide (InPath q (225 : Vertex)) else decide (InPath q (228 : Vertex)))) else (if i < 35 then decide (InPath q (229 : Vertex)) else (if i < 36 then decide (InPath q (230 : Vertex)) else decide (InPath q (232 : Vertex)))))) else (if i < 43 then (if i < 40 then (if i < 38 then decide (InPath q (233 : Vertex)) else (if i < 39 then decide (InPath q (234 : Vertex)) else decide (InPath q (238 : Vertex)))) else (if i < 41 then decide (InPath q (242 : Vertex)) else (if i < 42 then decide (InPath q (243 : Vertex)) else decide (InPath q (244 : Vertex))))) else (if i < 46 then (if i < 44 then decide (InPath q (245 : Vertex)) else (if i < 45 then decide (InPath q (250 : Vertex)) else decide (InPath q (251 : Vertex)))) else (if i < 48 then (if i < 47 then decide (InPath q (253 : Vertex)) else decide (InPath q (255 : Vertex))) else (if i < 49 then decide (InPath q (290 : Vertex)) else decide (InPath q (291 : Vertex)))))))) else (if i < 75 then (if i < 62 then (if i < 56 then (if i < 53 then (if i < 51 then decide (InPath q (295 : Vertex)) else (if i < 52 then decide (InPath q (297 : Vertex)) else decide (InPath q (301 : Vertex)))) else (if i < 54 then decide (InPath q (303 : Vertex)) else (if i < 55 then decide (InPath q (307 : Vertex)) else decide (InPath q (353 : Vertex))))) else (if i < 59 then (if i < 57 then decide (InPath q (356 : Vertex)) else (if i < 58 then decide (InPath q (357 : Vertex)) else decide (InPath q (358 : Vertex)))) else (if i < 60 then decide (InPath q (360 : Vertex)) else (if i < 61 then decide (InPath q (361 : Vertex)) else decide (InPath q (362 : Vertex)))))) else (if i < 68 then (if i < 65 then (if i < 63 then decide (InPath q (366 : Vertex)) else (if i < 64 then decide (InPath q (370 : Vertex)) else decide (InPath q (371 : Vertex)))) else (if i < 66 then decide (InPath q (373 : Vertex)) else (if i < 67 then decide (InPath q (379 : Vertex)) else decide (InPath q (381 : Vertex))))) else (if i < 71 then (if i < 69 then decide (InPath q (383 : Vertex)) else (if i < 70 then decide (InPath q (384 : Vertex)) else decide (InPath q (385 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (386 : Vertex)) else decide (InPath q (387 : Vertex))) else (if i < 74 then decide (InPath q (391 : Vertex)) else decide (InPath q (393 : Vertex))))))) else (if i < 88 then (if i < 81 then (if i < 78 then (if i < 76 then decide (InPath q (396 : Vertex)) else (if i < 77 then decide (InPath q (397 : Vertex)) else decide (InPath q (398 : Vertex)))) else (if i < 79 then decide (InPath q (399 : Vertex)) else (if i < 80 then decide (InPath q (400 : Vertex)) else decide (InPath q (401 : Vertex))))) else (if i < 84 then (if i < 82 then decide (InPath q (402 : Vertex)) else (if i < 83 then decide (InPath q (403 : Vertex)) else decide (InPath q (404 : Vertex)))) else (if i < 86 then (if i < 85 then decide (InPath q (410 : Vertex)) else decide (InPath q (412 : Vertex))) else (if i < 87 then decide (InPath q (414 : Vertex)) else decide (InPath q (449 : Vertex)))))) else (if i < 94 then (if i < 91 then (if i < 89 then decide (InPath q (452 : Vertex)) else (if i < 90 then decide (InPath q (453 : Vertex)) else decide (InPath q (454 : Vertex)))) else (if i < 92 then decide (InPath q (456 : Vertex)) else (if i < 93 then decide (InPath q (458 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 97 then (if i < 95 then decide (InPath q (466 : Vertex)) else (if i < 96 then decide (InPath q (468 : Vertex)) else decide (InPath q (474 : Vertex)))) else (if i < 99 then (if i < 98 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex))) else (if i < 100 then decide (InPath q (482 : Vertex)) else decide (InPath q (497 : Vertex))))))))) else (if i < 152 then (if i < 126 then (if i < 113 then (if i < 107 then (if i < 104 then (if i < 102 then decide (InPath q (498 : Vertex)) else (if i < 103 then decide (BallClauseLogic.Endpoint q (18 : Vertex)) else decide (BallClauseLogic.Endpoint q (68 : Vertex)))) else (if i < 105 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else (if i < 106 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (72 : Vertex))))) else (if i < 110 then (if i < 108 then decide (BallClauseLogic.Endpoint q (73 : Vertex)) else (if i < 109 then decide (BallClauseLogic.Endpoint q (74 : Vertex)) else decide (BallClauseLogic.Endpoint q (78 : Vertex)))) else (if i < 111 then decide (BallClauseLogic.Endpoint q (82 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (83 : Vertex)) else decide (BallClauseLogic.Endpoint q (84 : Vertex)))))) else (if i < 119 then (if i < 116 then (if i < 114 then decide (BallClauseLogic.Endpoint q (85 : Vertex)) else (if i < 115 then decide (BallClauseLogic.Endpoint q (90 : Vertex)) else decide (BallClauseLogic.Endpoint q (91 : Vertex)))) else (if i < 117 then decide (BallClauseLogic.Endpoint q (93 : Vertex)) else (if i < 118 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex))))) else (if i < 122 then (if i < 120 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else (if i < 121 then decide (BallClauseLogic.Endpoint q (134 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex)))) else (if i < 124 then (if i < 123 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (138 : Vertex))) else (if i < 125 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (146 : Vertex))))))) else (if i < 139 then (if i < 132 then (if i < 129 then (if i < 127 then decide (BallClauseLogic.Endpoint q (147 : Vertex)) else (if i < 128 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (149 : Vertex)))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else (if i < 131 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else decide (BallClauseLogic.Endpoint q (157 : Vertex))))) else (if i < 135 then (if i < 133 then decide (BallClauseLogic.Endpoint q (159 : Vertex)) else (if i < 134 then decide (BallClauseLogic.Endpoint q (225 : Vertex)) else decide (BallClauseLogic.Endpoint q (228 : Vertex)))) else (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (232 : Vertex)) else decide (BallClauseLogic.Endpoint q (233 : Vertex)))))) else (if i < 145 then (if i < 142 then (if i < 140 then decide (BallClauseLogic.Endpoint q (234 : Vertex)) else (if i < 141 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else decide (BallClauseLogic.Endpoint q (242 : Vertex)))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (243 : Vertex)) else (if i < 144 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else decide (BallClauseLogic.Endpoint q (245 : Vertex))))) else (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (250 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (253 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else decide (BallClauseLogic.Endpoint q (290 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (291 : Vertex)) else decide (BallClauseLogic.Endpoint q (295 : Vertex)))))))) else (if i < 177 then (if i < 164 then (if i < 158 then (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (297 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (301 : Vertex)) else decide (BallClauseLogic.Endpoint q (303 : Vertex)))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (307 : Vertex)) else (if i < 157 then decide (BallClauseLogic.Endpoint q (353 : Vertex)) else decide (BallClauseLogic.Endpoint q (356 : Vertex))))) else (if i < 161 then (if i < 159 then decide (BallClauseLogic.Endpoint q (357 : Vertex)) else (if i < 160 then decide (BallClauseLogic.Endpoint q (358 : Vertex)) else decide (BallClauseLogic.Endpoint q (360 : Vertex)))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (361 : Vertex)) else (if i < 163 then decide (BallClauseLogic.Endpoint q (362 : Vertex)) else decide (BallClauseLogic.Endpoint q (366 : Vertex)))))) else (if i < 170 then (if i < 167 then (if i < 165 then decide (BallClauseLogic.Endpoint q (370 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (371 : Vertex)) else decide (BallClauseLogic.Endpoint q (373 : Vertex)))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else (if i < 169 then decide (BallClauseLogic.Endpoint q (381 : Vertex)) else decide (BallClauseLogic.Endpoint q (383 : Vertex))))) else (if i < 173 then (if i < 171 then decide (BallClauseLogic.Endpoint q (384 : Vertex)) else (if i < 172 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (386 : Vertex)))) else (if i < 175 then (if i < 174 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (391 : Vertex))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (393 : Vertex)) else decide (BallClauseLogic.Endpoint q (396 : Vertex))))))) else (if i < 190 then (if i < 183 then (if i < 180 then (if i < 178 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else (if i < 179 then decide (BallClauseLogic.Endpoint q (398 : Vertex)) else decide (BallClauseLogic.Endpoint q (399 : Vertex)))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (400 : Vertex)) else (if i < 182 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (402 : Vertex))))) else (if i < 186 then (if i < 184 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else (if i < 185 then decide (BallClauseLogic.Endpoint q (404 : Vertex)) else decide (BallClauseLogic.Endpoint q (410 : Vertex)))) else (if i < 188 then (if i < 187 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex))) else (if i < 189 then decide (BallClauseLogic.Endpoint q (449 : Vertex)) else decide (BallClauseLogic.Endpoint q (452 : Vertex)))))) else (if i < 196 then (if i < 193 then (if i < 191 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else (if i < 192 then decide (BallClauseLogic.Endpoint q (454 : Vertex)) else decide (BallClauseLogic.Endpoint q (456 : Vertex)))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (458 : Vertex)) else (if i < 195 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (466 : Vertex))))) else (if i < 199 then (if i < 197 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else (if i < 198 then decide (BallClauseLogic.Endpoint q (474 : Vertex)) else decide (BallClauseLogic.Endpoint q (480 : Vertex)))) else (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (482 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count203 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count205 (b : Nat → Bool) : Nat := countLit b [102, 103, 104]
def count207 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count209 (b : Nat → Bool) : Nat := countLit b [105, 106, 107]
def count211 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 105, 106, 107]
def count213 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count215 (b : Nat → Bool) : Nat := countLit b [108, 109, 110]
def count217 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count219 (b : Nat → Bool) : Nat := countLit b [111, 112, 113]
def count221 (b : Nat → Bool) : Nat := countLit b [108, 109, 110, 111, 112, 113]
def count223 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
def count225 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count227 (b : Nat → Bool) : Nat := countLit b [114, 115, 116]
def count229 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count231 (b : Nat → Bool) : Nat := countLit b [117, 118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [114, 115, 116, 117, 118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count237 (b : Nat → Bool) : Nat := countLit b [120, 121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count241 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126]
def count245 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]
def count249 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126]
def count251 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [130, 131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [148, 150]
def count289 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count291 (b : Nat → Bool) : Nat := countLit b [148, 150, 151, 152]
def count293 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 150, 151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 150, 151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count313 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [165, 166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count341 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177]
def count343 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [178, 179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [181, 182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188, 189]
def count367 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]
def count371 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count373 (b : Nat → Bool) : Nat := countLit b [190, 191, 192]
def count375 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count377 (b : Nat → Bool) : Nat := countLit b [193, 194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count383 (b : Nat → Bool) : Nat := countLit b [196, 197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count387 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202]
def count391 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201, 202]
def count393 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
def count397 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
def count399 (b : Nat → Bool) : Nat := countLit b [102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
def count401 (b : Nat → Bool) : Nat := countLit b [2, 5]
def count403 (b : Nat → Bool) : Nat := countLit b [1, 2, 5]
def count406 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count408 (b : Nat → Bool) : Nat := countLit b [8, 10, 12]
def count411 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 12]
def count417 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count419 (b : Nat → Bool) : Nat := countLit b [13, 16, 17]
def count422 (b : Nat → Bool) : Nat := countLit b [23, 25]
def count424 (b : Nat → Bool) : Nat := countLit b [20, 23, 25]
def count427 (b : Nat → Bool) : Nat := countLit b [13, 16, 17, 20, 23, 25]
def count433 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 12, 13, 16, 17, 20, 23, 25]
def count445 (b : Nat → Bool) : Nat := countLit b [28, 31]
def count447 (b : Nat → Bool) : Nat := countLit b [27, 28, 31]
def count450 (b : Nat → Bool) : Nat := countLit b [33, 36]
def count452 (b : Nat → Bool) : Nat := countLit b [32, 33, 36]
def count455 (b : Nat → Bool) : Nat := countLit b [27, 28, 31, 32, 33, 36]
def count461 (b : Nat → Bool) : Nat := countLit b [41, 43]
def count463 (b : Nat → Bool) : Nat := countLit b [39, 41, 43]
def count466 (b : Nat → Bool) : Nat := countLit b [44, 47]
def count468 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count470 (b : Nat → Bool) : Nat := countLit b [44, 47, 49, 51]
def count474 (b : Nat → Bool) : Nat := countLit b [39, 41, 43, 44, 47, 49, 51]
def count481 (b : Nat → Bool) : Nat := countLit b [27, 28, 31, 32, 33, 36, 39, 41, 43, 44, 47, 49, 51]
def count494 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 12, 13, 16, 17, 20, 23, 25, 27, 28, 31, 32, 33, 36, 39, 41, 43, 44, 47, 49, 51]
def count519 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count521 (b : Nat → Bool) : Nat := countLit b [53, 55, 56]
def count524 (b : Nat → Bool) : Nat := countLit b [62, 64]
def count526 (b : Nat → Bool) : Nat := countLit b [59, 62, 64]
def count529 (b : Nat → Bool) : Nat := countLit b [53, 55, 56, 59, 62, 64]
def count535 (b : Nat → Bool) : Nat := countLit b [68, 69]
def count537 (b : Nat → Bool) : Nat := countLit b [65, 68, 69]
def count540 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count542 (b : Nat → Bool) : Nat := countLit b [72, 74, 75]
def count545 (b : Nat → Bool) : Nat := countLit b [65, 68, 69, 72, 74, 75]
def count551 (b : Nat → Bool) : Nat := countLit b [53, 55, 56, 59, 62, 64, 65, 68, 69, 72, 74, 75]
def count563 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count565 (b : Nat → Bool) : Nat := countLit b [78, 80, 81]
def count568 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count570 (b : Nat → Bool) : Nat := countLit b [83, 86, 87]
def count573 (b : Nat → Bool) : Nat := countLit b [78, 80, 81, 83, 86, 87]
def count579 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count581 (b : Nat → Bool) : Nat := countLit b [88, 91, 93]
def count584 (b : Nat → Bool) : Nat := countLit b [96, 97]
def count586 (b : Nat → Bool) : Nat := countLit b [100, 101]
def count588 (b : Nat → Bool) : Nat := countLit b [96, 97, 100, 101]
def count592 (b : Nat → Bool) : Nat := countLit b [88, 91, 93, 96, 97, 100, 101]
def count599 (b : Nat → Bool) : Nat := countLit b [78, 80, 81, 83, 86, 87, 88, 91, 93, 96, 97, 100, 101]
def count612 (b : Nat → Bool) : Nat := countLit b [53, 55, 56, 59, 62, 64, 65, 68, 69, 72, 74, 75, 78, 80, 81, 83, 86, 87, 88, 91, 93, 96, 97, 100, 101]
def count637 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 8, 10, 12, 13, 16, 17, 20, 23, 25, 27, 28, 31, 32, 33, 36, 39, 41, 43, 44, 47, 49, 51, 53, 55, 56, 59, 62, 64, 65, 68, 69, 72, 74, 75, 78, 80, 81, 83, 86, 87, 88, 91, 93, 96, 97, 100, 101]
def count679 (b : Nat → Bool) : Nat := countLit b [-2, -5]
def count681 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5]
def count684 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count686 (b : Nat → Bool) : Nat := countLit b [-8, -10, -12]
def count689 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -12]
def count695 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count697 (b : Nat → Bool) : Nat := countLit b [-13, -16, -17]
def count700 (b : Nat → Bool) : Nat := countLit b [-23, -25]
def count702 (b : Nat → Bool) : Nat := countLit b [-20, -23, -25]
def count705 (b : Nat → Bool) : Nat := countLit b [-13, -16, -17, -20, -23, -25]
def count711 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -12, -13, -16, -17, -20, -23, -25]
def count721 (b : Nat → Bool) : Nat := countLit b [-28, -31]
def count723 (b : Nat → Bool) : Nat := countLit b [-27, -28, -31]
def count726 (b : Nat → Bool) : Nat := countLit b [-33, -36]
def count728 (b : Nat → Bool) : Nat := countLit b [-32, -33, -36]
def count731 (b : Nat → Bool) : Nat := countLit b [-27, -28, -31, -32, -33, -36]
def count737 (b : Nat → Bool) : Nat := countLit b [-41, -43]
def count739 (b : Nat → Bool) : Nat := countLit b [-39, -41, -43]
def count742 (b : Nat → Bool) : Nat := countLit b [-44, -47]
def count744 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count746 (b : Nat → Bool) : Nat := countLit b [-44, -47, -49, -51]
def count750 (b : Nat → Bool) : Nat := countLit b [-39, -41, -43, -44, -47, -49, -51]
def count757 (b : Nat → Bool) : Nat := countLit b [-27, -28, -31, -32, -33, -36, -39, -41, -43, -44, -47, -49, -51]
def count767 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -12, -13, -16, -17, -20, -23, -25, -27, -28, -31, -32, -33, -36, -39, -41, -43, -44, -47, -49, -51]
def count777 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count779 (b : Nat → Bool) : Nat := countLit b [-53, -55, -56]
def count782 (b : Nat → Bool) : Nat := countLit b [-62, -64]
def count784 (b : Nat → Bool) : Nat := countLit b [-59, -62, -64]
def count787 (b : Nat → Bool) : Nat := countLit b [-53, -55, -56, -59, -62, -64]
def count793 (b : Nat → Bool) : Nat := countLit b [-68, -69]
def count795 (b : Nat → Bool) : Nat := countLit b [-65, -68, -69]
def count798 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count800 (b : Nat → Bool) : Nat := countLit b [-72, -74, -75]
def count803 (b : Nat → Bool) : Nat := countLit b [-65, -68, -69, -72, -74, -75]
def count809 (b : Nat → Bool) : Nat := countLit b [-53, -55, -56, -59, -62, -64, -65, -68, -69, -72, -74, -75]
def count819 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count821 (b : Nat → Bool) : Nat := countLit b [-78, -80, -81]
def count824 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count826 (b : Nat → Bool) : Nat := countLit b [-83, -86, -87]
def count829 (b : Nat → Bool) : Nat := countLit b [-78, -80, -81, -83, -86, -87]
def count835 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count837 (b : Nat → Bool) : Nat := countLit b [-88, -91, -93]
def count840 (b : Nat → Bool) : Nat := countLit b [-96, -97]
def count842 (b : Nat → Bool) : Nat := countLit b [-100, -101]
def count844 (b : Nat → Bool) : Nat := countLit b [-96, -97, -100, -101]
def count848 (b : Nat → Bool) : Nat := countLit b [-88, -91, -93, -96, -97, -100, -101]
def count855 (b : Nat → Bool) : Nat := countLit b [-78, -80, -81, -83, -86, -87, -88, -91, -93, -96, -97, -100, -101]
def count865 (b : Nat → Bool) : Nat := countLit b [-53, -55, -56, -59, -62, -64, -65, -68, -69, -72, -74, -75, -78, -80, -81, -83, -86, -87, -88, -91, -93, -96, -97, -100, -101]
def count875 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -8, -10, -12, -13, -16, -17, -20, -23, -25, -27, -28, -31, -32, -33, -36, -39, -41, -43, -44, -47, -49, -51, -53, -55, -56, -59, -62, -64, -65, -68, -69, -72, -74, -75, -78, -80, -81, -83, -86, -87, -88, -91, -93, -96, -97, -100, -101]
def count885 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count887 (b : Nat → Bool) : Nat := countLit b [3, 4, 6]
def count890 (b : Nat → Bool) : Nat := countLit b [9, 11]
def count892 (b : Nat → Bool) : Nat := countLit b [7, 9, 11]
def count895 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11]
def count901 (b : Nat → Bool) : Nat := countLit b [15, 18]
def count903 (b : Nat → Bool) : Nat := countLit b [14, 15, 18]
def count906 (b : Nat → Bool) : Nat := countLit b [21, 22]
def count908 (b : Nat → Bool) : Nat := countLit b [19, 21, 22]
def count911 (b : Nat → Bool) : Nat := countLit b [14, 15, 18, 19, 21, 22]
def count917 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11, 14, 15, 18, 19, 21, 22]
def count929 (b : Nat → Bool) : Nat := countLit b [26, 29]
def count931 (b : Nat → Bool) : Nat := countLit b [24, 26, 29]
def count934 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count936 (b : Nat → Bool) : Nat := countLit b [30, 34, 35]
def count939 (b : Nat → Bool) : Nat := countLit b [24, 26, 29, 30, 34, 35]
def count945 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count947 (b : Nat → Bool) : Nat := countLit b [37, 38, 40]
def count950 (b : Nat → Bool) : Nat := countLit b [42, 45]
def count952 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count954 (b : Nat → Bool) : Nat := countLit b [42, 45, 46, 48]
def count958 (b : Nat → Bool) : Nat := countLit b [37, 38, 40, 42, 45, 46, 48]
def count965 (b : Nat → Bool) : Nat := countLit b [24, 26, 29, 30, 34, 35, 37, 38, 40, 42, 45, 46, 48]
def count978 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11, 14, 15, 18, 19, 21, 22, 24, 26, 29, 30, 34, 35, 37, 38, 40, 42, 45, 46, 48]
def count1003 (b : Nat → Bool) : Nat := countLit b [52, 54]
def count1005 (b : Nat → Bool) : Nat := countLit b [50, 52, 54]
def count1008 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count1010 (b : Nat → Bool) : Nat := countLit b [57, 58, 60]
def count1013 (b : Nat → Bool) : Nat := countLit b [50, 52, 54, 57, 58, 60]
def count1019 (b : Nat → Bool) : Nat := countLit b [63, 66]
def count1021 (b : Nat → Bool) : Nat := countLit b [61, 63, 66]
def count1024 (b : Nat → Bool) : Nat := countLit b [67, 70]
def count1026 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count1028 (b : Nat → Bool) : Nat := countLit b [67, 70, 71, 73]
def count1032 (b : Nat → Bool) : Nat := countLit b [61, 63, 66, 67, 70, 71, 73]
def count1039 (b : Nat → Bool) : Nat := countLit b [50, 52, 54, 57, 58, 60, 61, 63, 66, 67, 70, 71, 73]
def count1052 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count1054 (b : Nat → Bool) : Nat := countLit b [76, 77, 79]
def count1057 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count1059 (b : Nat → Bool) : Nat := countLit b [82, 84, 85]
def count1062 (b : Nat → Bool) : Nat := countLit b [76, 77, 79, 82, 84, 85]
def count1068 (b : Nat → Bool) : Nat := countLit b [90, 92]
def count1070 (b : Nat → Bool) : Nat := countLit b [89, 90, 92]
def count1073 (b : Nat → Bool) : Nat := countLit b [94, 95]
def count1075 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count1077 (b : Nat → Bool) : Nat := countLit b [94, 95, 98, 99]
def count1081 (b : Nat → Bool) : Nat := countLit b [89, 90, 92, 94, 95, 98, 99]
def count1088 (b : Nat → Bool) : Nat := countLit b [76, 77, 79, 82, 84, 85, 89, 90, 92, 94, 95, 98, 99]
def count1101 (b : Nat → Bool) : Nat := countLit b [50, 52, 54, 57, 58, 60, 61, 63, 66, 67, 70, 71, 73, 76, 77, 79, 82, 84, 85, 89, 90, 92, 94, 95, 98, 99]
def count1127 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 7, 9, 11, 14, 15, 18, 19, 21, 22, 24, 26, 29, 30, 34, 35, 37, 38, 40, 42, 45, 46, 48, 50, 52, 54, 57, 58, 60, 61, 63, 66, 67, 70, 71, 73, 76, 77, 79, 82, 84, 85, 89, 90, 92, 94, 95, 98, 99]
def count1169 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count1171 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6]
def count1174 (b : Nat → Bool) : Nat := countLit b [-9, -11]
def count1176 (b : Nat → Bool) : Nat := countLit b [-7, -9, -11]
def count1179 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11]
def count1185 (b : Nat → Bool) : Nat := countLit b [-15, -18]
def count1187 (b : Nat → Bool) : Nat := countLit b [-14, -15, -18]
def count1190 (b : Nat → Bool) : Nat := countLit b [-21, -22]
def count1192 (b : Nat → Bool) : Nat := countLit b [-19, -21, -22]
def count1195 (b : Nat → Bool) : Nat := countLit b [-14, -15, -18, -19, -21, -22]
def count1201 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22]
def count1212 (b : Nat → Bool) : Nat := countLit b [-26, -29]
def count1214 (b : Nat → Bool) : Nat := countLit b [-24, -26, -29]
def count1217 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count1219 (b : Nat → Bool) : Nat := countLit b [-30, -34, -35]
def count1222 (b : Nat → Bool) : Nat := countLit b [-24, -26, -29, -30, -34, -35]
def count1228 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1230 (b : Nat → Bool) : Nat := countLit b [-37, -38, -40]
def count1233 (b : Nat → Bool) : Nat := countLit b [-42, -45]
def count1235 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count1237 (b : Nat → Bool) : Nat := countLit b [-42, -45, -46, -48]
def count1241 (b : Nat → Bool) : Nat := countLit b [-37, -38, -40, -42, -45, -46, -48]
def count1248 (b : Nat → Bool) : Nat := countLit b [-24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]
def count1259 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48]
def count1270 (b : Nat → Bool) : Nat := countLit b [-52, -54]
def count1272 (b : Nat → Bool) : Nat := countLit b [-50, -52, -54]
def count1275 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count1277 (b : Nat → Bool) : Nat := countLit b [-57, -58, -60]
def count1280 (b : Nat → Bool) : Nat := countLit b [-50, -52, -54, -57, -58, -60]
def count1286 (b : Nat → Bool) : Nat := countLit b [-63, -66]
def count1288 (b : Nat → Bool) : Nat := countLit b [-61, -63, -66]
def count1291 (b : Nat → Bool) : Nat := countLit b [-67, -70]
def count1293 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count1295 (b : Nat → Bool) : Nat := countLit b [-67, -70, -71, -73]
def count1299 (b : Nat → Bool) : Nat := countLit b [-61, -63, -66, -67, -70, -71, -73]
def count1306 (b : Nat → Bool) : Nat := countLit b [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73]
def count1317 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count1319 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79]
def count1322 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count1324 (b : Nat → Bool) : Nat := countLit b [-82, -84, -85]
def count1327 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79, -82, -84, -85]
def count1333 (b : Nat → Bool) : Nat := countLit b [-90, -92]
def count1335 (b : Nat → Bool) : Nat := countLit b [-89, -90, -92]
def count1338 (b : Nat → Bool) : Nat := countLit b [-94, -95]
def count1340 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count1342 (b : Nat → Bool) : Nat := countLit b [-94, -95, -98, -99]
def count1346 (b : Nat → Bool) : Nat := countLit b [-89, -90, -92, -94, -95, -98, -99]
def count1353 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]
def count1364 (b : Nat → Bool) : Nat := countLit b [-50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]
def count1375 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -7, -9, -11, -14, -15, -18, -19, -21, -22, -24, -26, -29, -30, -34, -35, -37, -38, -40, -42, -45, -46, -48, -50, -52, -54, -57, -58, -60, -61, -63, -66, -67, -70, -71, -73, -76, -77, -79, -82, -84, -85, -89, -90, -92, -94, -95, -98, -99]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 693 then (if i < 346 then (if i < 173 then (if i < 86 then (if i < 43 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 7 then (if i < 6 then b 5 else b 6) else (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)))) else (if i < 15 then (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else (if i < 14 then b 13 else b 14))) else (if i < 18 then (if i < 16 then b 15 else (if i < 17 then b 16 else b 17)) else (if i < 19 then b 18 else (if i < 20 then b 19 else b 20))))) else (if i < 32 then (if i < 26 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else (if i < 25 then b 24 else b 25))) else (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)))) else (if i < 37 then (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else (if i < 36 then b 35 else b 36))) else (if i < 40 then (if i < 38 then b 37 else (if i < 39 then b 38 else b 39)) else (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)))))) else (if i < 64 then (if i < 53 then (if i < 48 then (if i < 45 then (if i < 44 then b 43 else b 44) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47))) else (if i < 50 then (if i < 49 then b 48 else b 49) else (if i < 51 then b 50 else (if i < 52 then b 51 else b 52)))) else (if i < 58 then (if i < 55 then (if i < 54 then b 53 else b 54) else (if i < 56 then b 55 else (if i < 57 then b 56 else b 57))) else (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 62 then b 61 else (if i < 63 then b 62 else b 63))))) else (if i < 75 then (if i < 69 then (if i < 66 then (if i < 65 then b 64 else b 65) else (if i < 67 then b 66 else (if i < 68 then b 67 else b 68))) else (if i < 72 then (if i < 70 then b 69 else (if i < 71 then b 70 else b 71)) else (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)))) else (if i < 80 then (if i < 77 then (if i < 76 then b 75 else b 76) else (if i < 78 then b 77 else (if i < 79 then b 78 else b 79))) else (if i < 83 then (if i < 81 then b 80 else (if i < 82 then b 81 else b 82)) else (if i < 84 then b 83 else (if i < 85 then b 84 else b 85))))))) else (if i < 129 then (if i < 107 then (if i < 96 then (if i < 91 then (if i < 88 then (if i < 87 then b 86 else b 87) else (if i < 89 then b 88 else (if i < 90 then b 89 else b 90))) else (if i < 93 then (if i < 92 then b 91 else b 92) else (if i < 94 then b 93 else (if i < 95 then b 94 else b 95)))) else (if i < 101 then (if i < 98 then (if i < 97 then b 96 else b 97) else (if i < 99 then b 98 else (if i < 100 then b 99 else b 100))) else (if i < 104 then (if i < 102 then b 101 else (if i < 103 then b 102 else b 103)) else (if i < 105 then b 104 else (if i < 106 then b 105 else b 106))))) else (if i < 118 then (if i < 112 then (if i < 109 then (if i < 108 then b 107 else b 108) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111))) else (if i < 115 then (if i < 113 then b 112 else (if i < 114 then b 113 else b 114)) else (if i < 116 then b 115 else (if i < 117 then b 116 else b 117)))) else (if i < 123 then (if i < 120 then (if i < 119 then b 118 else b 119) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122))) else (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 127 then b 126 else (if i < 128 then b 127 else b 128)))))) else (if i < 151 then (if i < 140 then (if i < 134 then (if i < 131 then (if i < 130 then b 129 else b 130) else (if i < 132 then b 131 else (if i < 133 then b 132 else b 133))) else (if i < 137 then (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)) else (if i < 138 then b 137 else (if i < 139 then b 138 else b 139)))) else (if i < 145 then (if i < 142 then (if i < 141 then b 140 else b 141) else (if i < 143 then b 142 else (if i < 144 then b 143 else b 144))) else (if i < 148 then (if i < 146 then b 145 else (if i < 147 then b 146 else b 147)) else (if i < 149 then b 148 else (if i < 150 then b 149 else b 150))))) else (if i < 162 then (if i < 156 then (if i < 153 then (if i < 152 then b 151 else b 152) else (if i < 154 then b 153 else (if i < 155 then b 154 else b 155))) else (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)))) else (if i < 167 then (if i < 164 then (if i < 163 then b 162 else b 163) else (if i < 165 then b 164 else (if i < 166 then b 165 else b 166))) else (if i < 170 then (if i < 168 then b 167 else (if i < 169 then b 168 else b 169)) else (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)))))))) else (if i < 259 then (if i < 216 then (if i < 194 then (if i < 183 then (if i < 178 then (if i < 175 then (if i < 174 then b 173 else b 174) else (if i < 176 then b 175 else (if i < 177 then b 176 else b 177))) else (if i < 180 then (if i < 179 then b 178 else b 179) else (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)))) else (if i < 188 then (if i < 185 then (if i < 184 then b 183 else b 184) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187))) else (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 192 then b 191 else (if i < 193 then b 192 else b 193))))) else (if i < 205 then (if i < 199 then (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else (if i < 198 then b 197 else b 198))) else (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 203 then b 202 else (if i < 204 then decide (1 ≤ count203 b) else decide (2 ≤ count203 b))))) else (if i < 210 then (if i < 207 then (if i < 206 then decide (1 ≤ count205 b) else decide (2 ≤ count205 b)) else (if i < 208 then decide (1 ≤ count207 b) else (if i < 209 then decide (2 ≤ count207 b) else decide (1 ≤ count209 b)))) else (if i < 213 then (if i < 211 then decide (2 ≤ count209 b) else (if i < 212 then decide (1 ≤ count211 b) else decide (2 ≤ count211 b))) else (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))))))) else (if i < 237 then (if i < 226 then (if i < 221 then (if i < 218 then (if i < 217 then decide (2 ≤ count215 b) else decide (1 ≤ count217 b)) else (if i < 219 then decide (2 ≤ count217 b) else (if i < 220 then decide (1 ≤ count219 b) else decide (2 ≤ count219 b)))) else (if i < 223 then (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b)) else (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b))))) else (if i < 231 then (if i < 228 then (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b)) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b)))) else (if i < 234 then (if i < 232 then decide (1 ≤ count231 b) else (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b))) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b)))))) else (if i < 248 then (if i < 242 then (if i < 239 then (if i < 238 then decide (1 ≤ count237 b) else decide (2 ≤ count237 b)) else (if i < 240 then decide (1 ≤ count239 b) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b)))) else (if i < 245 then (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b))) else (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b))))) else (if i < 253 then (if i < 250 then (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b)) else (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)))) else (if i < 256 then (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b))) else (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)))))))) else (if i < 302 then (if i < 280 then (if i < 269 then (if i < 264 then (if i < 261 then (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)) else (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)))) else (if i < 266 then (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b)) else (if i < 267 then decide (2 ≤ count265 b) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b))))) else (if i < 274 then (if i < 271 then (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)) else (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)))) else (if i < 277 then (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))) else (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)))))) else (if i < 291 then (if i < 285 then (if i < 282 then (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)) else (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)))) else (if i < 288 then (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))) else (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))))) else (if i < 296 then (if i < 293 then (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)) else (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)))) else (if i < 299 then (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b))) else (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))))))) else (if i < 324 then (if i < 313 then (if i < 307 then (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)))) else (if i < 310 then (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b))) else (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))))) else (if i < 318 then (if i < 315 then (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b)) else (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)))) else (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)))))) else (if i < 335 then (if i < 329 then (if i < 326 then (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b)) else (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)))) else (if i < 332 then (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))) else (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))))) else (if i < 340 then (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)))) else (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b)))))))))) else (if i < 519 then (if i < 432 then (if i < 389 then (if i < 367 then (if i < 356 then (if i < 351 then (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b)))) else (if i < 353 then (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b)) else (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b))))) else (if i < 361 then (if i < 358 then (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b)) else (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))) else (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)))))) else (if i < 378 then (if i < 372 then (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)))) else (if i < 375 then (if i < 373 then decide (2 ≤ count371 b) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b))) else (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))))) else (if i < 383 then (if i < 380 then (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))) else (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))))))) else (if i < 410 then (if i < 399 then (if i < 394 then (if i < 391 then (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)) else (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b)))) else (if i < 396 then (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)) else (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b))))) else (if i < 404 then (if i < 401 then (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)) else (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))) else (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (3 ≤ count403 b) else decide (1 ≤ count406 b))) else (if i < 408 then decide (2 ≤ count406 b) else (if i < 409 then decide (1 ≤ count408 b) else decide (2 ≤ count408 b)))))) else (if i < 421 then (if i < 415 then (if i < 412 then (if i < 411 then decide (3 ≤ count408 b) else decide (1 ≤ count411 b)) else (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (3 ≤ count411 b) else decide (4 ≤ count411 b)))) else (if i < 418 then (if i < 416 then decide (5 ≤ count411 b) else (if i < 417 then decide (6 ≤ count411 b) else decide (1 ≤ count417 b))) else (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))))) else (if i < 426 then (if i < 423 then (if i < 422 then decide (3 ≤ count419 b) else decide (1 ≤ count422 b)) else (if i < 424 then decide (2 ≤ count422 b) else (if i < 425 then decide (1 ≤ count424 b) else decide (2 ≤ count424 b)))) else (if i < 429 then (if i < 427 then decide (3 ≤ count424 b) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b))) else (if i < 430 then decide (3 ≤ count427 b) else (if i < 431 then decide (4 ≤ count427 b) else decide (5 ≤ count427 b)))))))) else (if i < 475 then (if i < 453 then (if i < 442 then (if i < 437 then (if i < 434 then (if i < 433 then decide (6 ≤ count427 b) else decide (1 ≤ count433 b)) else (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (3 ≤ count433 b) else decide (4 ≤ count433 b)))) else (if i < 439 then (if i < 438 then decide (5 ≤ count433 b) else decide (6 ≤ count433 b)) else (if i < 440 then decide (7 ≤ count433 b) else (if i < 441 then decide (8 ≤ count433 b) else decide (9 ≤ count433 b))))) else (if i < 447 then (if i < 444 then (if i < 443 then decide (10 ≤ count433 b) else decide (11 ≤ count433 b)) else (if i < 445 then decide (12 ≤ count433 b) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b)))) else (if i < 450 then (if i < 448 then decide (1 ≤ count447 b) else (if i < 449 then decide (2 ≤ count447 b) else decide (3 ≤ count447 b))) else (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (1 ≤ count452 b)))))) else (if i < 464 then (if i < 458 then (if i < 455 then (if i < 454 then decide (2 ≤ count452 b) else decide (3 ≤ count452 b)) else (if i < 456 then decide (1 ≤ count455 b) else (if i < 457 then decide (2 ≤ count455 b) else decide (3 ≤ count455 b)))) else (if i < 461 then (if i < 459 then decide (4 ≤ count455 b) else (if i < 460 then decide (5 ≤ count455 b) else decide (6 ≤ count455 b))) else (if i < 462 then decide (1 ≤ count461 b) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b))))) else (if i < 469 then (if i < 466 then (if i < 465 then decide (2 ≤ count463 b) else decide (3 ≤ count463 b)) else (if i < 467 then decide (1 ≤ count466 b) else (if i < 468 then decide (2 ≤ count466 b) else decide (1 ≤ count468 b)))) else (if i < 472 then (if i < 470 then decide (2 ≤ count468 b) else (if i < 471 then decide (1 ≤ count470 b) else decide (2 ≤ count470 b))) else (if i < 473 then decide (3 ≤ count470 b) else (if i < 474 then decide (4 ≤ count470 b) else decide (1 ≤ count474 b))))))) else (if i < 497 then (if i < 486 then (if i < 480 then (if i < 477 then (if i < 476 then decide (2 ≤ count474 b) else decide (3 ≤ count474 b)) else (if i < 478 then decide (4 ≤ count474 b) else (if i < 479 then decide (5 ≤ count474 b) else decide (6 ≤ count474 b)))) else (if i < 483 then (if i < 481 then decide (7 ≤ count474 b) else (if i < 482 then decide (1 ≤ count481 b) else decide (2 ≤ count481 b))) else (if i < 484 then decide (3 ≤ count481 b) else (if i < 485 then decide (4 ≤ count481 b) else decide (5 ≤ count481 b))))) else (if i < 491 then (if i < 488 then (if i < 487 then decide (6 ≤ count481 b) else decide (7 ≤ count481 b)) else (if i < 489 then decide (8 ≤ count481 b) else (if i < 490 then decide (9 ≤ count481 b) else decide (10 ≤ count481 b)))) else (if i < 494 then (if i < 492 then decide (11 ≤ count481 b) else (if i < 493 then decide (12 ≤ count481 b) else decide (13 ≤ count481 b))) else (if i < 495 then decide (1 ≤ count494 b) else (if i < 496 then decide (2 ≤ count494 b) else decide (3 ≤ count494 b)))))) else (if i < 508 then (if i < 502 then (if i < 499 then (if i < 498 then decide (4 ≤ count494 b) else decide (5 ≤ count494 b)) else (if i < 500 then decide (6 ≤ count494 b) else (if i < 501 then decide (7 ≤ count494 b) else decide (8 ≤ count494 b)))) else (if i < 505 then (if i < 503 then decide (9 ≤ count494 b) else (if i < 504 then decide (10 ≤ count494 b) else decide (11 ≤ count494 b))) else (if i < 506 then decide (12 ≤ count494 b) else (if i < 507 then decide (13 ≤ count494 b) else decide (14 ≤ count494 b))))) else (if i < 513 then (if i < 510 then (if i < 509 then decide (15 ≤ count494 b) else decide (16 ≤ count494 b)) else (if i < 511 then decide (17 ≤ count494 b) else (if i < 512 then decide (18 ≤ count494 b) else decide (19 ≤ count494 b)))) else (if i < 516 then (if i < 514 then decide (20 ≤ count494 b) else (if i < 515 then decide (21 ≤ count494 b) else decide (22 ≤ count494 b))) else (if i < 517 then decide (23 ≤ count494 b) else (if i < 518 then decide (24 ≤ count494 b) else decide (25 ≤ count494 b))))))))) else (if i < 606 then (if i < 562 then (if i < 540 then (if i < 529 then (if i < 524 then (if i < 521 then (if i < 520 then decide (1 ≤ count519 b) else decide (2 ≤ count519 b)) else (if i < 522 then decide (1 ≤ count521 b) else (if i < 523 then decide (2 ≤ count521 b) else decide (3 ≤ count521 b)))) else (if i < 526 then (if i < 525 then decide (1 ≤ count524 b) else decide (2 ≤ count524 b)) else (if i < 527 then decide (1 ≤ count526 b) else (if i < 528 then decide (2 ≤ count526 b) else decide (3 ≤ count526 b))))) else (if i < 534 then (if i < 531 then (if i < 530 then decide (1 ≤ count529 b) else decide (2 ≤ count529 b)) else (if i < 532 then decide (3 ≤ count529 b) else (if i < 533 then decide (4 ≤ count529 b) else decide (5 ≤ count529 b)))) else (if i < 537 then (if i < 535 then decide (6 ≤ count529 b) else (if i < 536 then decide (1 ≤ count535 b) else decide (2 ≤ count535 b))) else (if i < 538 then decide (1 ≤ count537 b) else (if i < 539 then decide (2 ≤ count537 b) else decide (3 ≤ count537 b)))))) else (if i < 551 then (if i < 545 then (if i < 542 then (if i < 541 then decide (1 ≤ count540 b) else decide (2 ≤ count540 b)) else (if i < 543 then decide (1 ≤ count542 b) else (if i < 544 then decide (2 ≤ count542 b) else decide (3 ≤ count542 b)))) else (if i < 548 then (if i < 546 then decide (1 ≤ count545 b) else (if i < 547 then decide (2 ≤ count545 b) else decide (3 ≤ count545 b))) else (if i < 549 then decide (4 ≤ count545 b) else (if i < 550 then decide (5 ≤ count545 b) else decide (6 ≤ count545 b))))) else (if i < 556 then (if i < 553 then (if i < 552 then decide (1 ≤ count551 b) else decide (2 ≤ count551 b)) else (if i < 554 then decide (3 ≤ count551 b) else (if i < 555 then decide (4 ≤ count551 b) else decide (5 ≤ count551 b)))) else (if i < 559 then (if i < 557 then decide (6 ≤ count551 b) else (if i < 558 then decide (7 ≤ count551 b) else decide (8 ≤ count551 b))) else (if i < 560 then decide (9 ≤ count551 b) else (if i < 561 then decide (10 ≤ count551 b) else decide (11 ≤ count551 b))))))) else (if i < 584 then (if i < 573 then (if i < 567 then (if i < 564 then (if i < 563 then decide (12 ≤ count551 b) else decide (1 ≤ count563 b)) else (if i < 565 then decide (2 ≤ count563 b) else (if i < 566 then decide (1 ≤ count565 b) else decide (2 ≤ count565 b)))) else (if i < 570 then (if i < 568 then decide (3 ≤ count565 b) else (if i < 569 then decide (1 ≤ count568 b) else decide (2 ≤ count568 b))) else (if i < 571 then decide (1 ≤ count570 b) else (if i < 572 then decide (2 ≤ count570 b) else decide (3 ≤ count570 b))))) else (if i < 578 then (if i < 575 then (if i < 574 then decide (1 ≤ count573 b) else decide (2 ≤ count573 b)) else (if i < 576 then decide (3 ≤ count573 b) else (if i < 577 then decide (4 ≤ count573 b) else decide (5 ≤ count573 b)))) else (if i < 581 then (if i < 579 then decide (6 ≤ count573 b) else (if i < 580 then decide (1 ≤ count579 b) else decide (2 ≤ count579 b))) else (if i < 582 then decide (1 ≤ count581 b) else (if i < 583 then decide (2 ≤ count581 b) else decide (3 ≤ count581 b)))))) else (if i < 595 then (if i < 589 then (if i < 586 then (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b)) else (if i < 587 then decide (1 ≤ count586 b) else (if i < 588 then decide (2 ≤ count586 b) else decide (1 ≤ count588 b)))) else (if i < 592 then (if i < 590 then decide (2 ≤ count588 b) else (if i < 591 then decide (3 ≤ count588 b) else decide (4 ≤ count588 b))) else (if i < 593 then decide (1 ≤ count592 b) else (if i < 594 then decide (2 ≤ count592 b) else decide (3 ≤ count592 b))))) else (if i < 600 then (if i < 597 then (if i < 596 then decide (4 ≤ count592 b) else decide (5 ≤ count592 b)) else (if i < 598 then decide (6 ≤ count592 b) else (if i < 599 then decide (7 ≤ count592 b) else decide (1 ≤ count599 b)))) else (if i < 603 then (if i < 601 then decide (2 ≤ count599 b) else (if i < 602 then decide (3 ≤ count599 b) else decide (4 ≤ count599 b))) else (if i < 604 then decide (5 ≤ count599 b) else (if i < 605 then decide (6 ≤ count599 b) else decide (7 ≤ count599 b)))))))) else (if i < 649 then (if i < 627 then (if i < 616 then (if i < 611 then (if i < 608 then (if i < 607 then decide (8 ≤ count599 b) else decide (9 ≤ count599 b)) else (if i < 609 then decide (10 ≤ count599 b) else (if i < 610 then decide (11 ≤ count599 b) else decide (12 ≤ count599 b)))) else (if i < 613 then (if i < 612 then decide (13 ≤ count599 b) else decide (1 ≤ count612 b)) else (if i < 614 then decide (2 ≤ count612 b) else (if i < 615 then decide (3 ≤ count612 b) else decide (4 ≤ count612 b))))) else (if i < 621 then (if i < 618 then (if i < 617 then decide (5 ≤ count612 b) else decide (6 ≤ count612 b)) else (if i < 619 then decide (7 ≤ count612 b) else (if i < 620 then decide (8 ≤ count612 b) else decide (9 ≤ count612 b)))) else (if i < 624 then (if i < 622 then decide (10 ≤ count612 b) else (if i < 623 then decide (11 ≤ count612 b) else decide (12 ≤ count612 b))) else (if i < 625 then decide (13 ≤ count612 b) else (if i < 626 then decide (14 ≤ count612 b) else decide (15 ≤ count612 b)))))) else (if i < 638 then (if i < 632 then (if i < 629 then (if i < 628 then decide (16 ≤ count612 b) else decide (17 ≤ count612 b)) else (if i < 630 then decide (18 ≤ count612 b) else (if i < 631 then decide (19 ≤ count612 b) else decide (20 ≤ count612 b)))) else (if i < 635 then (if i < 633 then decide (21 ≤ count612 b) else (if i < 634 then decide (22 ≤ count612 b) else decide (23 ≤ count612 b))) else (if i < 636 then decide (24 ≤ count612 b) else (if i < 637 then decide (25 ≤ count612 b) else decide (1 ≤ count637 b))))) else (if i < 643 then (if i < 640 then (if i < 639 then decide (2 ≤ count637 b) else decide (3 ≤ count637 b)) else (if i < 641 then decide (4 ≤ count637 b) else (if i < 642 then decide (5 ≤ count637 b) else decide (6 ≤ count637 b)))) else (if i < 646 then (if i < 644 then decide (7 ≤ count637 b) else (if i < 645 then decide (8 ≤ count637 b) else decide (9 ≤ count637 b))) else (if i < 647 then decide (10 ≤ count637 b) else (if i < 648 then decide (11 ≤ count637 b) else decide (12 ≤ count637 b))))))) else (if i < 671 then (if i < 660 then (if i < 654 then (if i < 651 then (if i < 650 then decide (13 ≤ count637 b) else decide (14 ≤ count637 b)) else (if i < 652 then decide (15 ≤ count637 b) else (if i < 653 then decide (16 ≤ count637 b) else decide (17 ≤ count637 b)))) else (if i < 657 then (if i < 655 then decide (18 ≤ count637 b) else (if i < 656 then decide (19 ≤ count637 b) else decide (20 ≤ count637 b))) else (if i < 658 then decide (21 ≤ count637 b) else (if i < 659 then decide (22 ≤ count637 b) else decide (23 ≤ count637 b))))) else (if i < 665 then (if i < 662 then (if i < 661 then decide (24 ≤ count637 b) else decide (25 ≤ count637 b)) else (if i < 663 then decide (26 ≤ count637 b) else (if i < 664 then decide (27 ≤ count637 b) else decide (28 ≤ count637 b)))) else (if i < 668 then (if i < 666 then decide (29 ≤ count637 b) else (if i < 667 then decide (30 ≤ count637 b) else decide (31 ≤ count637 b))) else (if i < 669 then decide (32 ≤ count637 b) else (if i < 670 then decide (33 ≤ count637 b) else decide (34 ≤ count637 b)))))) else (if i < 682 then (if i < 676 then (if i < 673 then (if i < 672 then decide (35 ≤ count637 b) else decide (36 ≤ count637 b)) else (if i < 674 then decide (37 ≤ count637 b) else (if i < 675 then decide (38 ≤ count637 b) else decide (39 ≤ count637 b)))) else (if i < 679 then (if i < 677 then decide (40 ≤ count637 b) else (if i < 678 then decide (41 ≤ count637 b) else decide (42 ≤ count637 b))) else (if i < 680 then decide (1 ≤ count679 b) else (if i < 681 then decide (2 ≤ count679 b) else decide (1 ≤ count681 b))))) else (if i < 687 then (if i < 684 then (if i < 683 then decide (2 ≤ count681 b) else decide (3 ≤ count681 b)) else (if i < 685 then decide (1 ≤ count684 b) else (if i < 686 then decide (2 ≤ count684 b) else decide (1 ≤ count686 b)))) else (if i < 690 then (if i < 688 then decide (2 ≤ count686 b) else (if i < 689 then decide (3 ≤ count686 b) else decide (1 ≤ count689 b))) else (if i < 691 then decide (2 ≤ count689 b) else (if i < 692 then decide (3 ≤ count689 b) else decide (4 ≤ count689 b))))))))))) else (if i < 1039 then (if i < 866 then (if i < 779 then (if i < 736 then (if i < 714 then (if i < 703 then (if i < 698 then (if i < 695 then (if i < 694 then decide (5 ≤ count689 b) else decide (6 ≤ count689 b)) else (if i < 696 then decide (1 ≤ count695 b) else (if i < 697 then decide (2 ≤ count695 b) else decide (1 ≤ count697 b)))) else (if i < 700 then (if i < 699 then decide (2 ≤ count697 b) else decide (3 ≤ count697 b)) else (if i < 701 then decide (1 ≤ count700 b) else (if i < 702 then decide (2 ≤ count700 b) else decide (1 ≤ count702 b))))) else (if i < 708 then (if i < 705 then (if i < 704 then decide (2 ≤ count702 b) else decide (3 ≤ count702 b)) else (if i < 706 then decide (1 ≤ count705 b) else (if i < 707 then decide (2 ≤ count705 b) else decide (3 ≤ count705 b)))) else (if i < 711 then (if i < 709 then decide (4 ≤ count705 b) else (if i < 710 then decide (5 ≤ count705 b) else decide (6 ≤ count705 b))) else (if i < 712 then decide (1 ≤ count711 b) else (if i < 713 then decide (2 ≤ count711 b) else decide (3 ≤ count711 b)))))) else (if i < 725 then (if i < 719 then (if i < 716 then (if i < 715 then decide (4 ≤ count711 b) else decide (5 ≤ count711 b)) else (if i < 717 then decide (6 ≤ count711 b) else (if i < 718 then decide (7 ≤ count711 b) else decide (8 ≤ count711 b)))) else (if i < 722 then (if i < 720 then decide (9 ≤ count711 b) else (if i < 721 then decide (10 ≤ count711 b) else decide (1 ≤ count721 b))) else (if i < 723 then decide (2 ≤ count721 b) else (if i < 724 then decide (1 ≤ count723 b) else decide (2 ≤ count723 b))))) else (if i < 730 then (if i < 727 then (if i < 726 then decide (3 ≤ count723 b) else decide (1 ≤ count726 b)) else (if i < 728 then decide (2 ≤ count726 b) else (if i < 729 then decide (1 ≤ count728 b) else decide (2 ≤ count728 b)))) else (if i < 733 then (if i < 731 then decide (3 ≤ count728 b) else (if i < 732 then decide (1 ≤ count731 b) else decide (2 ≤ count731 b))) else (if i < 734 then decide (3 ≤ count731 b) else (if i < 735 then decide (4 ≤ count731 b) else decide (5 ≤ count731 b))))))) else (if i < 757 then (if i < 746 then (if i < 741 then (if i < 738 then (if i < 737 then decide (6 ≤ count731 b) else decide (1 ≤ count737 b)) else (if i < 739 then decide (2 ≤ count737 b) else (if i < 740 then decide (1 ≤ count739 b) else decide (2 ≤ count739 b)))) else (if i < 743 then (if i < 742 then decide (3 ≤ count739 b) else decide (1 ≤ count742 b)) else (if i < 744 then decide (2 ≤ count742 b) else (if i < 745 then decide (1 ≤ count744 b) else decide (2 ≤ count744 b))))) else (if i < 751 then (if i < 748 then (if i < 747 then decide (1 ≤ count746 b) else decide (2 ≤ count746 b)) else (if i < 749 then decide (3 ≤ count746 b) else (if i < 750 then decide (4 ≤ count746 b) else decide (1 ≤ count750 b)))) else (if i < 754 then (if i < 752 then decide (2 ≤ count750 b) else (if i < 753 then decide (3 ≤ count750 b) else decide (4 ≤ count750 b))) else (if i < 755 then decide (5 ≤ count750 b) else (if i < 756 then decide (6 ≤ count750 b) else decide (7 ≤ count750 b)))))) else (if i < 768 then (if i < 762 then (if i < 759 then (if i < 758 then decide (1 ≤ count757 b) else decide (2 ≤ count757 b)) else (if i < 760 then decide (3 ≤ count757 b) else (if i < 761 then decide (4 ≤ count757 b) else decide (5 ≤ count757 b)))) else (if i < 765 then (if i < 763 then decide (6 ≤ count757 b) else (if i < 764 then decide (7 ≤ count757 b) else decide (8 ≤ count757 b))) else (if i < 766 then decide (9 ≤ count757 b) else (if i < 767 then decide (10 ≤ count757 b) else decide (1 ≤ count767 b))))) else (if i < 773 then (if i < 770 then (if i < 769 then decide (2 ≤ count767 b) else decide (3 ≤ count767 b)) else (if i < 771 then decide (4 ≤ count767 b) else (if i < 772 then decide (5 ≤ count767 b) else decide (6 ≤ count767 b)))) else (if i < 776 then (if i < 774 then decide (7 ≤ count767 b) else (if i < 775 then decide (8 ≤ count767 b) else decide (9 ≤ count767 b))) else (if i < 777 then decide (10 ≤ count767 b) else (if i < 778 then decide (1 ≤ count777 b) else decide (2 ≤ count777 b)))))))) else (if i < 822 then (if i < 800 then (if i < 789 then (if i < 784 then (if i < 781 then (if i < 780 then decide (1 ≤ count779 b) else decide (2 ≤ count779 b)) else (if i < 782 then decide (3 ≤ count779 b) else (if i < 783 then decide (1 ≤ count782 b) else decide (2 ≤ count782 b)))) else (if i < 786 then (if i < 785 then decide (1 ≤ count784 b) else decide (2 ≤ count784 b)) else (if i < 787 then decide (3 ≤ count784 b) else (if i < 788 then decide (1 ≤ count787 b) else decide (2 ≤ count787 b))))) else (if i < 794 then (if i < 791 then (if i < 790 then decide (3 ≤ count787 b) else decide (4 ≤ count787 b)) else (if i < 792 then decide (5 ≤ count787 b) else (if i < 793 then decide (6 ≤ count787 b) else decide (1 ≤ count793 b)))) else (if i < 797 then (if i < 795 then decide (2 ≤ count793 b) else (if i < 796 then decide (1 ≤ count795 b) else decide (2 ≤ count795 b))) else (if i < 798 then decide (3 ≤ count795 b) else (if i < 799 then decide (1 ≤ count798 b) else decide (2 ≤ count798 b)))))) else (if i < 811 then (if i < 805 then (if i < 802 then (if i < 801 then decide (1 ≤ count800 b) else decide (2 ≤ count800 b)) else (if i < 803 then decide (3 ≤ count800 b) else (if i < 804 then decide (1 ≤ count803 b) else decide (2 ≤ count803 b)))) else (if i < 808 then (if i < 806 then decide (3 ≤ count803 b) else (if i < 807 then decide (4 ≤ count803 b) else decide (5 ≤ count803 b))) else (if i < 809 then decide (6 ≤ count803 b) else (if i < 810 then decide (1 ≤ count809 b) else decide (2 ≤ count809 b))))) else (if i < 816 then (if i < 813 then (if i < 812 then decide (3 ≤ count809 b) else decide (4 ≤ count809 b)) else (if i < 814 then decide (5 ≤ count809 b) else (if i < 815 then decide (6 ≤ count809 b) else decide (7 ≤ count809 b)))) else (if i < 819 then (if i < 817 then decide (8 ≤ count809 b) else (if i < 818 then decide (9 ≤ count809 b) else decide (10 ≤ count809 b))) else (if i < 820 then decide (1 ≤ count819 b) else (if i < 821 then decide (2 ≤ count819 b) else decide (1 ≤ count821 b))))))) else (if i < 844 then (if i < 833 then (if i < 827 then (if i < 824 then (if i < 823 then decide (2 ≤ count821 b) else decide (3 ≤ count821 b)) else (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (1 ≤ count826 b)))) else (if i < 830 then (if i < 828 then decide (2 ≤ count826 b) else (if i < 829 then decide (3 ≤ count826 b) else decide (1 ≤ count829 b))) else (if i < 831 then decide (2 ≤ count829 b) else (if i < 832 then decide (3 ≤ count829 b) else decide (4 ≤ count829 b))))) else (if i < 838 then (if i < 835 then (if i < 834 then decide (5 ≤ count829 b) else decide (6 ≤ count829 b)) else (if i < 836 then decide (1 ≤ count835 b) else (if i < 837 then decide (2 ≤ count835 b) else decide (1 ≤ count837 b)))) else (if i < 841 then (if i < 839 then decide (2 ≤ count837 b) else (if i < 840 then decide (3 ≤ count837 b) else decide (1 ≤ count840 b))) else (if i < 842 then decide (2 ≤ count840 b) else (if i < 843 then decide (1 ≤ count842 b) else decide (2 ≤ count842 b)))))) else (if i < 855 then (if i < 849 then (if i < 846 then (if i < 845 then decide (1 ≤ count844 b) else decide (2 ≤ count844 b)) else (if i < 847 then decide (3 ≤ count844 b) else (if i < 848 then decide (4 ≤ count844 b) else decide (1 ≤ count848 b)))) else (if i < 852 then (if i < 850 then decide (2 ≤ count848 b) else (if i < 851 then decide (3 ≤ count848 b) else decide (4 ≤ count848 b))) else (if i < 853 then decide (5 ≤ count848 b) else (if i < 854 then decide (6 ≤ count848 b) else decide (7 ≤ count848 b))))) else (if i < 860 then (if i < 857 then (if i < 856 then decide (1 ≤ count855 b) else decide (2 ≤ count855 b)) else (if i < 858 then decide (3 ≤ count855 b) else (if i < 859 then decide (4 ≤ count855 b) else decide (5 ≤ count855 b)))) else (if i < 863 then (if i < 861 then decide (6 ≤ count855 b) else (if i < 862 then decide (7 ≤ count855 b) else decide (8 ≤ count855 b))) else (if i < 864 then decide (9 ≤ count855 b) else (if i < 865 then decide (10 ≤ count855 b) else decide (1 ≤ count865 b))))))))) else (if i < 952 then (if i < 909 then (if i < 887 then (if i < 876 then (if i < 871 then (if i < 868 then (if i < 867 then decide (2 ≤ count865 b) else decide (3 ≤ count865 b)) else (if i < 869 then decide (4 ≤ count865 b) else (if i < 870 then decide (5 ≤ count865 b) else decide (6 ≤ count865 b)))) else (if i < 873 then (if i < 872 then decide (7 ≤ count865 b) else decide (8 ≤ count865 b)) else (if i < 874 then decide (9 ≤ count865 b) else (if i < 875 then decide (10 ≤ count865 b) else decide (1 ≤ count875 b))))) else (if i < 881 then (if i < 878 then (if i < 877 then decide (2 ≤ count875 b) else decide (3 ≤ count875 b)) else (if i < 879 then decide (4 ≤ count875 b) else (if i < 880 then decide (5 ≤ count875 b) else decide (6 ≤ count875 b)))) else (if i < 884 then (if i < 882 then decide (7 ≤ count875 b) else (if i < 883 then decide (8 ≤ count875 b) else decide (9 ≤ count875 b))) else (if i < 885 then decide (10 ≤ count875 b) else (if i < 886 then decide (1 ≤ count885 b) else decide (2 ≤ count885 b)))))) else (if i < 898 then (if i < 892 then (if i < 889 then (if i < 888 then decide (1 ≤ count887 b) else decide (2 ≤ count887 b)) else (if i < 890 then decide (3 ≤ count887 b) else (if i < 891 then decide (1 ≤ count890 b) else decide (2 ≤ count890 b)))) else (if i < 895 then (if i < 893 then decide (1 ≤ count892 b) else (if i < 894 then decide (2 ≤ count892 b) else decide (3 ≤ count892 b))) else (if i < 896 then decide (1 ≤ count895 b) else (if i < 897 then decide (2 ≤ count895 b) else decide (3 ≤ count895 b))))) else (if i < 903 then (if i < 900 then (if i < 899 then decide (4 ≤ count895 b) else decide (5 ≤ count895 b)) else (if i < 901 then decide (6 ≤ count895 b) else (if i < 902 then decide (1 ≤ count901 b) else decide (2 ≤ count901 b)))) else (if i < 906 then (if i < 904 then decide (1 ≤ count903 b) else (if i < 905 then decide (2 ≤ count903 b) else decide (3 ≤ count903 b))) else (if i < 907 then decide (1 ≤ count906 b) else (if i < 908 then decide (2 ≤ count906 b) else decide (1 ≤ count908 b))))))) else (if i < 930 then (if i < 919 then (if i < 914 then (if i < 911 then (if i < 910 then decide (2 ≤ count908 b) else decide (3 ≤ count908 b)) else (if i < 912 then decide (1 ≤ count911 b) else (if i < 913 then decide (2 ≤ count911 b) else decide (3 ≤ count911 b)))) else (if i < 916 then (if i < 915 then decide (4 ≤ count911 b) else decide (5 ≤ count911 b)) else (if i < 917 then decide (6 ≤ count911 b) else (if i < 918 then decide (1 ≤ count917 b) else decide (2 ≤ count917 b))))) else (if i < 924 then (if i < 921 then (if i < 920 then decide (3 ≤ count917 b) else decide (4 ≤ count917 b)) else (if i < 922 then decide (5 ≤ count917 b) else (if i < 923 then decide (6 ≤ count917 b) else decide (7 ≤ count917 b)))) else (if i < 927 then (if i < 925 then decide (8 ≤ count917 b) else (if i < 926 then decide (9 ≤ count917 b) else decide (10 ≤ count917 b))) else (if i < 928 then decide (11 ≤ count917 b) else (if i < 929 then decide (12 ≤ count917 b) else decide (1 ≤ count929 b)))))) else (if i < 941 then (if i < 935 then (if i < 932 then (if i < 931 then decide (2 ≤ count929 b) else decide (1 ≤ count931 b)) else (if i < 933 then decide (2 ≤ count931 b) else (if i < 934 then decide (3 ≤ count931 b) else decide (1 ≤ count934 b)))) else (if i < 938 then (if i < 936 then decide (2 ≤ count934 b) else (if i < 937 then decide (1 ≤ count936 b) else decide (2 ≤ count936 b))) else (if i < 939 then decide (3 ≤ count936 b) else (if i < 940 then decide (1 ≤ count939 b) else decide (2 ≤ count939 b))))) else (if i < 946 then (if i < 943 then (if i < 942 then decide (3 ≤ count939 b) else decide (4 ≤ count939 b)) else (if i < 944 then decide (5 ≤ count939 b) else (if i < 945 then decide (6 ≤ count939 b) else decide (1 ≤ count945 b)))) else (if i < 949 then (if i < 947 then decide (2 ≤ count945 b) else (if i < 948 then decide (1 ≤ count947 b) else decide (2 ≤ count947 b))) else (if i < 950 then decide (3 ≤ count947 b) else (if i < 951 then decide (1 ≤ count950 b) else decide (2 ≤ count950 b)))))))) else (if i < 995 then (if i < 973 then (if i < 962 then (if i < 957 then (if i < 954 then (if i < 953 then decide (1 ≤ count952 b) else decide (2 ≤ count952 b)) else (if i < 955 then decide (1 ≤ count954 b) else (if i < 956 then decide (2 ≤ count954 b) else decide (3 ≤ count954 b)))) else (if i < 959 then (if i < 958 then decide (4 ≤ count954 b) else decide (1 ≤ count958 b)) else (if i < 960 then decide (2 ≤ count958 b) else (if i < 961 then decide (3 ≤ count958 b) else decide (4 ≤ count958 b))))) else (if i < 967 then (if i < 964 then (if i < 963 then decide (5 ≤ count958 b) else decide (6 ≤ count958 b)) else (if i < 965 then decide (7 ≤ count958 b) else (if i < 966 then decide (1 ≤ count965 b) else decide (2 ≤ count965 b)))) else (if i < 970 then (if i < 968 then decide (3 ≤ count965 b) else (if i < 969 then decide (4 ≤ count965 b) else decide (5 ≤ count965 b))) else (if i < 971 then decide (6 ≤ count965 b) else (if i < 972 then decide (7 ≤ count965 b) else decide (8 ≤ count965 b)))))) else (if i < 984 then (if i < 978 then (if i < 975 then (if i < 974 then decide (9 ≤ count965 b) else decide (10 ≤ count965 b)) else (if i < 976 then decide (11 ≤ count965 b) else (if i < 977 then decide (12 ≤ count965 b) else decide (13 ≤ count965 b)))) else (if i < 981 then (if i < 979 then decide (1 ≤ count978 b) else (if i < 980 then decide (2 ≤ count978 b) else decide (3 ≤ count978 b))) else (if i < 982 then decide (4 ≤ count978 b) else (if i < 983 then decide (5 ≤ count978 b) else decide (6 ≤ count978 b))))) else (if i < 989 then (if i < 986 then (if i < 985 then decide (7 ≤ count978 b) else decide (8 ≤ count978 b)) else (if i < 987 then decide (9 ≤ count978 b) else (if i < 988 then decide (10 ≤ count978 b) else decide (11 ≤ count978 b)))) else (if i < 992 then (if i < 990 then decide (12 ≤ count978 b) else (if i < 991 then decide (13 ≤ count978 b) else decide (14 ≤ count978 b))) else (if i < 993 then decide (15 ≤ count978 b) else (if i < 994 then decide (16 ≤ count978 b) else decide (17 ≤ count978 b))))))) else (if i < 1017 then (if i < 1006 then (if i < 1000 then (if i < 997 then (if i < 996 then decide (18 ≤ count978 b) else decide (19 ≤ count978 b)) else (if i < 998 then decide (20 ≤ count978 b) else (if i < 999 then decide (21 ≤ count978 b) else decide (22 ≤ count978 b)))) else (if i < 1003 then (if i < 1001 then decide (23 ≤ count978 b) else (if i < 1002 then decide (24 ≤ count978 b) else decide (25 ≤ count978 b))) else (if i < 1004 then decide (1 ≤ count1003 b) else (if i < 1005 then decide (2 ≤ count1003 b) else decide (1 ≤ count1005 b))))) else (if i < 1011 then (if i < 1008 then (if i < 1007 then decide (2 ≤ count1005 b) else decide (3 ≤ count1005 b)) else (if i < 1009 then decide (1 ≤ count1008 b) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (1 ≤ count1010 b)))) else (if i < 1014 then (if i < 1012 then decide (2 ≤ count1010 b) else (if i < 1013 then decide (3 ≤ count1010 b) else decide (1 ≤ count1013 b))) else (if i < 1015 then decide (2 ≤ count1013 b) else (if i < 1016 then decide (3 ≤ count1013 b) else decide (4 ≤ count1013 b)))))) else (if i < 1028 then (if i < 1022 then (if i < 1019 then (if i < 1018 then decide (5 ≤ count1013 b) else decide (6 ≤ count1013 b)) else (if i < 1020 then decide (1 ≤ count1019 b) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (1 ≤ count1021 b)))) else (if i < 1025 then (if i < 1023 then decide (2 ≤ count1021 b) else (if i < 1024 then decide (3 ≤ count1021 b) else decide (1 ≤ count1024 b))) else (if i < 1026 then decide (2 ≤ count1024 b) else (if i < 1027 then decide (1 ≤ count1026 b) else decide (2 ≤ count1026 b))))) else (if i < 1033 then (if i < 1030 then (if i < 1029 then decide (1 ≤ count1028 b) else decide (2 ≤ count1028 b)) else (if i < 1031 then decide (3 ≤ count1028 b) else (if i < 1032 then decide (4 ≤ count1028 b) else decide (1 ≤ count1032 b)))) else (if i < 1036 then (if i < 1034 then decide (2 ≤ count1032 b) else (if i < 1035 then decide (3 ≤ count1032 b) else decide (4 ≤ count1032 b))) else (if i < 1037 then decide (5 ≤ count1032 b) else (if i < 1038 then decide (6 ≤ count1032 b) else decide (7 ≤ count1032 b)))))))))) else (if i < 1212 then (if i < 1125 then (if i < 1082 then (if i < 1060 then (if i < 1049 then (if i < 1044 then (if i < 1041 then (if i < 1040 then decide (1 ≤ count1039 b) else decide (2 ≤ count1039 b)) else (if i < 1042 then decide (3 ≤ count1039 b) else (if i < 1043 then decide (4 ≤ count1039 b) else decide (5 ≤ count1039 b)))) else (if i < 1046 then (if i < 1045 then decide (6 ≤ count1039 b) else decide (7 ≤ count1039 b)) else (if i < 1047 then decide (8 ≤ count1039 b) else (if i < 1048 then decide (9 ≤ count1039 b) else decide (10 ≤ count1039 b))))) else (if i < 1054 then (if i < 1051 then (if i < 1050 then decide (11 ≤ count1039 b) else decide (12 ≤ count1039 b)) else (if i < 1052 then decide (13 ≤ count1039 b) else (if i < 1053 then decide (1 ≤ count1052 b) else decide (2 ≤ count1052 b)))) else (if i < 1057 then (if i < 1055 then decide (1 ≤ count1054 b) else (if i < 1056 then decide (2 ≤ count1054 b) else decide (3 ≤ count1054 b))) else (if i < 1058 then decide (1 ≤ count1057 b) else (if i < 1059 then decide (2 ≤ count1057 b) else decide (1 ≤ count1059 b)))))) else (if i < 1071 then (if i < 1065 then (if i < 1062 then (if i < 1061 then decide (2 ≤ count1059 b) else decide (3 ≤ count1059 b)) else (if i < 1063 then decide (1 ≤ count1062 b) else (if i < 1064 then decide (2 ≤ count1062 b) else decide (3 ≤ count1062 b)))) else (if i < 1068 then (if i < 1066 then decide (4 ≤ count1062 b) else (if i < 1067 then decide (5 ≤ count1062 b) else decide (6 ≤ count1062 b))) else (if i < 1069 then decide (1 ≤ count1068 b) else (if i < 1070 then decide (2 ≤ count1068 b) else decide (1 ≤ count1070 b))))) else (if i < 1076 then (if i < 1073 then (if i < 1072 then decide (2 ≤ count1070 b) else decide (3 ≤ count1070 b)) else (if i < 1074 then decide (1 ≤ count1073 b) else (if i < 1075 then decide (2 ≤ count1073 b) else decide (1 ≤ count1075 b)))) else (if i < 1079 then (if i < 1077 then decide (2 ≤ count1075 b) else (if i < 1078 then decide (1 ≤ count1077 b) else decide (2 ≤ count1077 b))) else (if i < 1080 then decide (3 ≤ count1077 b) else (if i < 1081 then decide (4 ≤ count1077 b) else decide (1 ≤ count1081 b))))))) else (if i < 1103 then (if i < 1092 then (if i < 1087 then (if i < 1084 then (if i < 1083 then decide (2 ≤ count1081 b) else decide (3 ≤ count1081 b)) else (if i < 1085 then decide (4 ≤ count1081 b) else (if i < 1086 then decide (5 ≤ count1081 b) else decide (6 ≤ count1081 b)))) else (if i < 1089 then (if i < 1088 then decide (7 ≤ count1081 b) else decide (1 ≤ count1088 b)) else (if i < 1090 then decide (2 ≤ count1088 b) else (if i < 1091 then decide (3 ≤ count1088 b) else decide (4 ≤ count1088 b))))) else (if i < 1097 then (if i < 1094 then (if i < 1093 then decide (5 ≤ count1088 b) else decide (6 ≤ count1088 b)) else (if i < 1095 then decide (7 ≤ count1088 b) else (if i < 1096 then decide (8 ≤ count1088 b) else decide (9 ≤ count1088 b)))) else (if i < 1100 then (if i < 1098 then decide (10 ≤ count1088 b) else (if i < 1099 then decide (11 ≤ count1088 b) else decide (12 ≤ count1088 b))) else (if i < 1101 then decide (13 ≤ count1088 b) else (if i < 1102 then decide (1 ≤ count1101 b) else decide (2 ≤ count1101 b)))))) else (if i < 1114 then (if i < 1108 then (if i < 1105 then (if i < 1104 then decide (3 ≤ count1101 b) else decide (4 ≤ count1101 b)) else (if i < 1106 then decide (5 ≤ count1101 b) else (if i < 1107 then decide (6 ≤ count1101 b) else decide (7 ≤ count1101 b)))) else (if i < 1111 then (if i < 1109 then decide (8 ≤ count1101 b) else (if i < 1110 then decide (9 ≤ count1101 b) else decide (10 ≤ count1101 b))) else (if i < 1112 then decide (11 ≤ count1101 b) else (if i < 1113 then decide (12 ≤ count1101 b) else decide (13 ≤ count1101 b))))) else (if i < 1119 then (if i < 1116 then (if i < 1115 then decide (14 ≤ count1101 b) else decide (15 ≤ count1101 b)) else (if i < 1117 then decide (16 ≤ count1101 b) else (if i < 1118 then decide (17 ≤ count1101 b) else decide (18 ≤ count1101 b)))) else (if i < 1122 then (if i < 1120 then decide (19 ≤ count1101 b) else (if i < 1121 then decide (20 ≤ count1101 b) else decide (21 ≤ count1101 b))) else (if i < 1123 then decide (22 ≤ count1101 b) else (if i < 1124 then decide (23 ≤ count1101 b) else decide (24 ≤ count1101 b)))))))) else (if i < 1168 then (if i < 1146 then (if i < 1135 then (if i < 1130 then (if i < 1127 then (if i < 1126 then decide (25 ≤ count1101 b) else decide (26 ≤ count1101 b)) else (if i < 1128 then decide (1 ≤ count1127 b) else (if i < 1129 then decide (2 ≤ count1127 b) else decide (3 ≤ count1127 b)))) else (if i < 1132 then (if i < 1131 then decide (4 ≤ count1127 b) else decide (5 ≤ count1127 b)) else (if i < 1133 then decide (6 ≤ count1127 b) else (if i < 1134 then decide (7 ≤ count1127 b) else decide (8 ≤ count1127 b))))) else (if i < 1140 then (if i < 1137 then (if i < 1136 then decide (9 ≤ count1127 b) else decide (10 ≤ count1127 b)) else (if i < 1138 then decide (11 ≤ count1127 b) else (if i < 1139 then decide (12 ≤ count1127 b) else decide (13 ≤ count1127 b)))) else (if i < 1143 then (if i < 1141 then decide (14 ≤ count1127 b) else (if i < 1142 then decide (15 ≤ count1127 b) else decide (16 ≤ count1127 b))) else (if i < 1144 then decide (17 ≤ count1127 b) else (if i < 1145 then decide (18 ≤ count1127 b) else decide (19 ≤ count1127 b)))))) else (if i < 1157 then (if i < 1151 then (if i < 1148 then (if i < 1147 then decide (20 ≤ count1127 b) else decide (21 ≤ count1127 b)) else (if i < 1149 then decide (22 ≤ count1127 b) else (if i < 1150 then decide (23 ≤ count1127 b) else decide (24 ≤ count1127 b)))) else (if i < 1154 then (if i < 1152 then decide (25 ≤ count1127 b) else (if i < 1153 then decide (26 ≤ count1127 b) else decide (27 ≤ count1127 b))) else (if i < 1155 then decide (28 ≤ count1127 b) else (if i < 1156 then decide (29 ≤ count1127 b) else decide (30 ≤ count1127 b))))) else (if i < 1162 then (if i < 1159 then (if i < 1158 then decide (31 ≤ count1127 b) else decide (32 ≤ count1127 b)) else (if i < 1160 then decide (33 ≤ count1127 b) else (if i < 1161 then decide (34 ≤ count1127 b) else decide (35 ≤ count1127 b)))) else (if i < 1165 then (if i < 1163 then decide (36 ≤ count1127 b) else (if i < 1164 then decide (37 ≤ count1127 b) else decide (38 ≤ count1127 b))) else (if i < 1166 then decide (39 ≤ count1127 b) else (if i < 1167 then decide (40 ≤ count1127 b) else decide (41 ≤ count1127 b))))))) else (if i < 1190 then (if i < 1179 then (if i < 1173 then (if i < 1170 then (if i < 1169 then decide (42 ≤ count1127 b) else decide (1 ≤ count1169 b)) else (if i < 1171 then decide (2 ≤ count1169 b) else (if i < 1172 then decide (1 ≤ count1171 b) else decide (2 ≤ count1171 b)))) else (if i < 1176 then (if i < 1174 then decide (3 ≤ count1171 b) else (if i < 1175 then decide (1 ≤ count1174 b) else decide (2 ≤ count1174 b))) else (if i < 1177 then decide (1 ≤ count1176 b) else (if i < 1178 then decide (2 ≤ count1176 b) else decide (3 ≤ count1176 b))))) else (if i < 1184 then (if i < 1181 then (if i < 1180 then decide (1 ≤ count1179 b) else decide (2 ≤ count1179 b)) else (if i < 1182 then decide (3 ≤ count1179 b) else (if i < 1183 then decide (4 ≤ count1179 b) else decide (5 ≤ count1179 b)))) else (if i < 1187 then (if i < 1185 then decide (6 ≤ count1179 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))) else (if i < 1188 then decide (1 ≤ count1187 b) else (if i < 1189 then decide (2 ≤ count1187 b) else decide (3 ≤ count1187 b)))))) else (if i < 1201 then (if i < 1195 then (if i < 1192 then (if i < 1191 then decide (1 ≤ count1190 b) else decide (2 ≤ count1190 b)) else (if i < 1193 then decide (1 ≤ count1192 b) else (if i < 1194 then decide (2 ≤ count1192 b) else decide (3 ≤ count1192 b)))) else (if i < 1198 then (if i < 1196 then decide (1 ≤ count1195 b) else (if i < 1197 then decide (2 ≤ count1195 b) else decide (3 ≤ count1195 b))) else (if i < 1199 then decide (4 ≤ count1195 b) else (if i < 1200 then decide (5 ≤ count1195 b) else decide (6 ≤ count1195 b))))) else (if i < 1206 then (if i < 1203 then (if i < 1202 then decide (1 ≤ count1201 b) else decide (2 ≤ count1201 b)) else (if i < 1204 then decide (3 ≤ count1201 b) else (if i < 1205 then decide (4 ≤ count1201 b) else decide (5 ≤ count1201 b)))) else (if i < 1209 then (if i < 1207 then decide (6 ≤ count1201 b) else (if i < 1208 then decide (7 ≤ count1201 b) else decide (8 ≤ count1201 b))) else (if i < 1210 then decide (9 ≤ count1201 b) else (if i < 1211 then decide (10 ≤ count1201 b) else decide (11 ≤ count1201 b))))))))) else (if i < 1299 then (if i < 1255 then (if i < 1233 then (if i < 1222 then (if i < 1217 then (if i < 1214 then (if i < 1213 then decide (1 ≤ count1212 b) else decide (2 ≤ count1212 b)) else (if i < 1215 then decide (1 ≤ count1214 b) else (if i < 1216 then decide (2 ≤ count1214 b) else decide (3 ≤ count1214 b)))) else (if i < 1219 then (if i < 1218 then decide (1 ≤ count1217 b) else decide (2 ≤ count1217 b)) else (if i < 1220 then decide (1 ≤ count1219 b) else (if i < 1221 then decide (2 ≤ count1219 b) else decide (3 ≤ count1219 b))))) else (if i < 1227 then (if i < 1224 then (if i < 1223 then decide (1 ≤ count1222 b) else decide (2 ≤ count1222 b)) else (if i < 1225 then decide (3 ≤ count1222 b) else (if i < 1226 then decide (4 ≤ count1222 b) else decide (5 ≤ count1222 b)))) else (if i < 1230 then (if i < 1228 then decide (6 ≤ count1222 b) else (if i < 1229 then decide (1 ≤ count1228 b) else decide (2 ≤ count1228 b))) else (if i < 1231 then decide (1 ≤ count1230 b) else (if i < 1232 then decide (2 ≤ count1230 b) else decide (3 ≤ count1230 b)))))) else (if i < 1244 then (if i < 1238 then (if i < 1235 then (if i < 1234 then decide (1 ≤ count1233 b) else decide (2 ≤ count1233 b)) else (if i < 1236 then decide (1 ≤ count1235 b) else (if i < 1237 then decide (2 ≤ count1235 b) else decide (1 ≤ count1237 b)))) else (if i < 1241 then (if i < 1239 then decide (2 ≤ count1237 b) else (if i < 1240 then decide (3 ≤ count1237 b) else decide (4 ≤ count1237 b))) else (if i < 1242 then decide (1 ≤ count1241 b) else (if i < 1243 then decide (2 ≤ count1241 b) else decide (3 ≤ count1241 b))))) else (if i < 1249 then (if i < 1246 then (if i < 1245 then decide (4 ≤ count1241 b) else decide (5 ≤ count1241 b)) else (if i < 1247 then decide (6 ≤ count1241 b) else (if i < 1248 then decide (7 ≤ count1241 b) else decide (1 ≤ count1248 b)))) else (if i < 1252 then (if i < 1250 then decide (2 ≤ count1248 b) else (if i < 1251 then decide (3 ≤ count1248 b) else decide (4 ≤ count1248 b))) else (if i < 1253 then decide (5 ≤ count1248 b) else (if i < 1254 then decide (6 ≤ count1248 b) else decide (7 ≤ count1248 b))))))) else (if i < 1277 then (if i < 1266 then (if i < 1260 then (if i < 1257 then (if i < 1256 then decide (8 ≤ count1248 b) else decide (9 ≤ count1248 b)) else (if i < 1258 then decide (10 ≤ count1248 b) else (if i < 1259 then decide (11 ≤ count1248 b) else decide (1 ≤ count1259 b)))) else (if i < 1263 then (if i < 1261 then decide (2 ≤ count1259 b) else (if i < 1262 then decide (3 ≤ count1259 b) else decide (4 ≤ count1259 b))) else (if i < 1264 then decide (5 ≤ count1259 b) else (if i < 1265 then decide (6 ≤ count1259 b) else decide (7 ≤ count1259 b))))) else (if i < 1271 then (if i < 1268 then (if i < 1267 then decide (8 ≤ count1259 b) else decide (9 ≤ count1259 b)) else (if i < 1269 then decide (10 ≤ count1259 b) else (if i < 1270 then decide (11 ≤ count1259 b) else decide (1 ≤ count1270 b)))) else (if i < 1274 then (if i < 1272 then decide (2 ≤ count1270 b) else (if i < 1273 then decide (1 ≤ count1272 b) else decide (2 ≤ count1272 b))) else (if i < 1275 then decide (3 ≤ count1272 b) else (if i < 1276 then decide (1 ≤ count1275 b) else decide (2 ≤ count1275 b)))))) else (if i < 1288 then (if i < 1282 then (if i < 1279 then (if i < 1278 then decide (1 ≤ count1277 b) else decide (2 ≤ count1277 b)) else (if i < 1280 then decide (3 ≤ count1277 b) else (if i < 1281 then decide (1 ≤ count1280 b) else decide (2 ≤ count1280 b)))) else (if i < 1285 then (if i < 1283 then decide (3 ≤ count1280 b) else (if i < 1284 then decide (4 ≤ count1280 b) else decide (5 ≤ count1280 b))) else (if i < 1286 then decide (6 ≤ count1280 b) else (if i < 1287 then decide (1 ≤ count1286 b) else decide (2 ≤ count1286 b))))) else (if i < 1293 then (if i < 1290 then (if i < 1289 then decide (1 ≤ count1288 b) else decide (2 ≤ count1288 b)) else (if i < 1291 then decide (3 ≤ count1288 b) else (if i < 1292 then decide (1 ≤ count1291 b) else decide (2 ≤ count1291 b)))) else (if i < 1296 then (if i < 1294 then decide (1 ≤ count1293 b) else (if i < 1295 then decide (2 ≤ count1293 b) else decide (1 ≤ count1295 b))) else (if i < 1297 then decide (2 ≤ count1295 b) else (if i < 1298 then decide (3 ≤ count1295 b) else decide (4 ≤ count1295 b)))))))) else (if i < 1342 then (if i < 1320 then (if i < 1309 then (if i < 1304 then (if i < 1301 then (if i < 1300 then decide (1 ≤ count1299 b) else decide (2 ≤ count1299 b)) else (if i < 1302 then decide (3 ≤ count1299 b) else (if i < 1303 then decide (4 ≤ count1299 b) else decide (5 ≤ count1299 b)))) else (if i < 1306 then (if i < 1305 then decide (6 ≤ count1299 b) else decide (7 ≤ count1299 b)) else (if i < 1307 then decide (1 ≤ count1306 b) else (if i < 1308 then decide (2 ≤ count1306 b) else decide (3 ≤ count1306 b))))) else (if i < 1314 then (if i < 1311 then (if i < 1310 then decide (4 ≤ count1306 b) else decide (5 ≤ count1306 b)) else (if i < 1312 then decide (6 ≤ count1306 b) else (if i < 1313 then decide (7 ≤ count1306 b) else decide (8 ≤ count1306 b)))) else (if i < 1317 then (if i < 1315 then decide (9 ≤ count1306 b) else (if i < 1316 then decide (10 ≤ count1306 b) else decide (11 ≤ count1306 b))) else (if i < 1318 then decide (1 ≤ count1317 b) else (if i < 1319 then decide (2 ≤ count1317 b) else decide (1 ≤ count1319 b)))))) else (if i < 1331 then (if i < 1325 then (if i < 1322 then (if i < 1321 then decide (2 ≤ count1319 b) else decide (3 ≤ count1319 b)) else (if i < 1323 then decide (1 ≤ count1322 b) else (if i < 1324 then decide (2 ≤ count1322 b) else decide (1 ≤ count1324 b)))) else (if i < 1328 then (if i < 1326 then decide (2 ≤ count1324 b) else (if i < 1327 then decide (3 ≤ count1324 b) else decide (1 ≤ count1327 b))) else (if i < 1329 then decide (2 ≤ count1327 b) else (if i < 1330 then decide (3 ≤ count1327 b) else decide (4 ≤ count1327 b))))) else (if i < 1336 then (if i < 1333 then (if i < 1332 then decide (5 ≤ count1327 b) else decide (6 ≤ count1327 b)) else (if i < 1334 then decide (1 ≤ count1333 b) else (if i < 1335 then decide (2 ≤ count1333 b) else decide (1 ≤ count1335 b)))) else (if i < 1339 then (if i < 1337 then decide (2 ≤ count1335 b) else (if i < 1338 then decide (3 ≤ count1335 b) else decide (1 ≤ count1338 b))) else (if i < 1340 then decide (2 ≤ count1338 b) else (if i < 1341 then decide (1 ≤ count1340 b) else decide (2 ≤ count1340 b))))))) else (if i < 1364 then (if i < 1353 then (if i < 1347 then (if i < 1344 then (if i < 1343 then decide (1 ≤ count1342 b) else decide (2 ≤ count1342 b)) else (if i < 1345 then decide (3 ≤ count1342 b) else (if i < 1346 then decide (4 ≤ count1342 b) else decide (1 ≤ count1346 b)))) else (if i < 1350 then (if i < 1348 then decide (2 ≤ count1346 b) else (if i < 1349 then decide (3 ≤ count1346 b) else decide (4 ≤ count1346 b))) else (if i < 1351 then decide (5 ≤ count1346 b) else (if i < 1352 then decide (6 ≤ count1346 b) else decide (7 ≤ count1346 b))))) else (if i < 1358 then (if i < 1355 then (if i < 1354 then decide (1 ≤ count1353 b) else decide (2 ≤ count1353 b)) else (if i < 1356 then decide (3 ≤ count1353 b) else (if i < 1357 then decide (4 ≤ count1353 b) else decide (5 ≤ count1353 b)))) else (if i < 1361 then (if i < 1359 then decide (6 ≤ count1353 b) else (if i < 1360 then decide (7 ≤ count1353 b) else decide (8 ≤ count1353 b))) else (if i < 1362 then decide (9 ≤ count1353 b) else (if i < 1363 then decide (10 ≤ count1353 b) else decide (11 ≤ count1353 b)))))) else (if i < 1375 then (if i < 1369 then (if i < 1366 then (if i < 1365 then decide (1 ≤ count1364 b) else decide (2 ≤ count1364 b)) else (if i < 1367 then decide (3 ≤ count1364 b) else (if i < 1368 then decide (4 ≤ count1364 b) else decide (5 ≤ count1364 b)))) else (if i < 1372 then (if i < 1370 then decide (6 ≤ count1364 b) else (if i < 1371 then decide (7 ≤ count1364 b) else decide (8 ≤ count1364 b))) else (if i < 1373 then decide (9 ≤ count1364 b) else (if i < 1374 then decide (10 ≤ count1364 b) else decide (11 ≤ count1364 b))))) else (if i < 1380 then (if i < 1377 then (if i < 1376 then decide (1 ≤ count1375 b) else decide (2 ≤ count1375 b)) else (if i < 1378 then decide (3 ≤ count1375 b) else (if i < 1379 then decide (4 ≤ count1375 b) else decide (5 ≤ count1375 b)))) else (if i < 1383 then (if i < 1381 then decide (6 ≤ count1375 b) else (if i < 1382 then decide (7 ≤ count1375 b) else decide (8 ≤ count1375 b))) else (if i < 1384 then decide (9 ≤ count1375 b) else (if i < 1385 then decide (10 ≤ count1375 b) else decide (11 ≤ count1375 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (68 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (69 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (73 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (84 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (85 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (132 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (133 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (134 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (136 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (137 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (138 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (142 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (146 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (147 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (148 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (149 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (154 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (155 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (157 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (225 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (228 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (229 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (230 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (233 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (234 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (242 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (244 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (245 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (250 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (251 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (253 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (290 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (291 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (295 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (307 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (370 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (385 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (386 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (387 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (391 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (393 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (396 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (397 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (398 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (400 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (401 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (402 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (403 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (404 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (410 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (412 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (414 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (452 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (453 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (454 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (458 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (466 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (468 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (474 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (482 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (498 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (157 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (242 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (253 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (370 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value1169 (q : Snake 81) : valuation q 1169 = decide (1 ≤ count1169 (baseVal q)) := rfl
theorem value1171 (q : Snake 81) : valuation q 1171 = decide (1 ≤ count1171 (baseVal q)) := rfl
theorem value1172 (q : Snake 81) : valuation q 1172 = decide (2 ≤ count1171 (baseVal q)) := rfl
theorem value1174 (q : Snake 81) : valuation q 1174 = decide (1 ≤ count1174 (baseVal q)) := rfl
theorem value1176 (q : Snake 81) : valuation q 1176 = decide (1 ≤ count1176 (baseVal q)) := rfl
theorem value1180 (q : Snake 81) : valuation q 1180 = decide (2 ≤ count1179 (baseVal q)) := rfl
theorem value1185 (q : Snake 81) : valuation q 1185 = decide (1 ≤ count1185 (baseVal q)) := rfl
theorem value1187 (q : Snake 81) : valuation q 1187 = decide (1 ≤ count1187 (baseVal q)) := rfl
theorem value1190 (q : Snake 81) : valuation q 1190 = decide (1 ≤ count1190 (baseVal q)) := rfl
theorem value1192 (q : Snake 81) : valuation q 1192 = decide (1 ≤ count1192 (baseVal q)) := rfl
theorem value1195 (q : Snake 81) : valuation q 1195 = decide (1 ≤ count1195 (baseVal q)) := rfl
theorem value1196 (q : Snake 81) : valuation q 1196 = decide (2 ≤ count1195 (baseVal q)) := rfl
theorem value1202 (q : Snake 81) : valuation q 1202 = decide (2 ≤ count1201 (baseVal q)) := rfl
theorem value1203 (q : Snake 81) : valuation q 1203 = decide (3 ≤ count1201 (baseVal q)) := rfl
theorem value1204 (q : Snake 81) : valuation q 1204 = decide (4 ≤ count1201 (baseVal q)) := rfl
theorem value1212 (q : Snake 81) : valuation q 1212 = decide (1 ≤ count1212 (baseVal q)) := rfl
theorem value1213 (q : Snake 81) : valuation q 1213 = decide (2 ≤ count1212 (baseVal q)) := rfl
theorem value1214 (q : Snake 81) : valuation q 1214 = decide (1 ≤ count1214 (baseVal q)) := rfl
theorem value1215 (q : Snake 81) : valuation q 1215 = decide (2 ≤ count1214 (baseVal q)) := rfl
theorem value1217 (q : Snake 81) : valuation q 1217 = decide (1 ≤ count1217 (baseVal q)) := rfl
theorem value1219 (q : Snake 81) : valuation q 1219 = decide (1 ≤ count1219 (baseVal q)) := rfl
theorem value1220 (q : Snake 81) : valuation q 1220 = decide (2 ≤ count1219 (baseVal q)) := rfl
theorem value1222 (q : Snake 81) : valuation q 1222 = decide (1 ≤ count1222 (baseVal q)) := rfl
theorem value1223 (q : Snake 81) : valuation q 1223 = decide (2 ≤ count1222 (baseVal q)) := rfl
theorem value1224 (q : Snake 81) : valuation q 1224 = decide (3 ≤ count1222 (baseVal q)) := rfl
theorem value1228 (q : Snake 81) : valuation q 1228 = decide (1 ≤ count1228 (baseVal q)) := rfl
theorem value1230 (q : Snake 81) : valuation q 1230 = decide (1 ≤ count1230 (baseVal q)) := rfl
theorem value1233 (q : Snake 81) : valuation q 1233 = decide (1 ≤ count1233 (baseVal q)) := rfl
theorem value1235 (q : Snake 81) : valuation q 1235 = decide (1 ≤ count1235 (baseVal q)) := rfl
theorem value1237 (q : Snake 81) : valuation q 1237 = decide (1 ≤ count1237 (baseVal q)) := rfl
theorem value1238 (q : Snake 81) : valuation q 1238 = decide (2 ≤ count1237 (baseVal q)) := rfl
theorem value1241 (q : Snake 81) : valuation q 1241 = decide (1 ≤ count1241 (baseVal q)) := rfl
theorem value1242 (q : Snake 81) : valuation q 1242 = decide (2 ≤ count1241 (baseVal q)) := rfl
theorem value1248 (q : Snake 81) : valuation q 1248 = decide (1 ≤ count1248 (baseVal q)) := rfl
theorem value1249 (q : Snake 81) : valuation q 1249 = decide (2 ≤ count1248 (baseVal q)) := rfl
theorem value1250 (q : Snake 81) : valuation q 1250 = decide (3 ≤ count1248 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (4 ≤ count1259 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (5 ≤ count1259 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (6 ≤ count1259 (baseVal q)) := rfl
theorem value1270 (q : Snake 81) : valuation q 1270 = decide (1 ≤ count1270 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (1 ≤ count1272 (baseVal q)) := rfl
theorem value1280 (q : Snake 81) : valuation q 1280 = decide (1 ≤ count1280 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (1 ≤ count1286 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (1 ≤ count1288 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (1 ≤ count1291 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (1 ≤ count1293 (baseVal q)) := rfl
theorem value1294 (q : Snake 81) : valuation q 1294 = decide (2 ≤ count1293 (baseVal q)) := rfl
theorem value1295 (q : Snake 81) : valuation q 1295 = decide (1 ≤ count1295 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (2 ≤ count1295 (baseVal q)) := rfl
theorem value1299 (q : Snake 81) : valuation q 1299 = decide (1 ≤ count1299 (baseVal q)) := rfl
theorem value1300 (q : Snake 81) : valuation q 1300 = decide (2 ≤ count1299 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (3 ≤ count1299 (baseVal q)) := rfl
theorem value1307 (q : Snake 81) : valuation q 1307 = decide (2 ≤ count1306 (baseVal q)) := rfl
theorem value1308 (q : Snake 81) : valuation q 1308 = decide (3 ≤ count1306 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (4 ≤ count1306 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (1 ≤ count1317 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (2 ≤ count1317 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (1 ≤ count1319 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (2 ≤ count1319 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (3 ≤ count1319 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (1 ≤ count1322 (baseVal q)) := rfl
theorem value1324 (q : Snake 81) : valuation q 1324 = decide (1 ≤ count1324 (baseVal q)) := rfl
theorem value1325 (q : Snake 81) : valuation q 1325 = decide (2 ≤ count1324 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (1 ≤ count1327 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (2 ≤ count1327 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (3 ≤ count1327 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (4 ≤ count1327 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (1 ≤ count1333 (baseVal q)) := rfl
theorem value1335 (q : Snake 81) : valuation q 1335 = decide (1 ≤ count1335 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (1 ≤ count1338 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (2 ≤ count1338 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (1 ≤ count1342 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (2 ≤ count1342 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (3 ≤ count1342 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (1 ≤ count1346 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (2 ≤ count1346 (baseVal q)) := rfl
theorem value1348 (q : Snake 81) : valuation q 1348 = decide (3 ≤ count1346 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (2 ≤ count1353 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (3 ≤ count1353 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (4 ≤ count1353 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (5 ≤ count1353 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (5 ≤ count1364 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (6 ≤ count1364 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (7 ≤ count1364 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (11 ≤ count1375 (baseVal q)) := rfl
theorem meaningNeg99 (b : Nat → Bool) : literal (valuationOf b) (-99) = decide (1 ≤ countLit b [-99]) := by
  change literal b (-99) = decide (1 ≤ countLit b [-99])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-99) <;> decide
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
theorem meaningNeg82 (b : Nat → Bool) : literal (valuationOf b) (-82) = decide (1 ≤ countLit b [-82]) := by
  change literal b (-82) = decide (1 ≤ countLit b [-82])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-82) <;> decide
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
theorem meaningNeg63 (b : Nat → Bool) : literal (valuationOf b) (-63) = decide (1 ≤ countLit b [-63]) := by
  change literal b (-63) = decide (1 ≤ countLit b [-63])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-63) <;> decide
theorem meaningNeg54 (b : Nat → Bool) : literal (valuationOf b) (-54) = decide (1 ≤ countLit b [-54]) := by
  change literal b (-54) = decide (1 ≤ countLit b [-54])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-54) <;> decide
theorem meaningNeg50 (b : Nat → Bool) : literal (valuationOf b) (-50) = decide (1 ≤ countLit b [-50]) := by
  change literal b (-50) = decide (1 ≤ countLit b [-50])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-50) <;> decide
theorem meaningNeg46 (b : Nat → Bool) : literal (valuationOf b) (-46) = decide (1 ≤ countLit b [-46]) := by
  change literal b (-46) = decide (1 ≤ countLit b [-46])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-46) <;> decide
theorem meaningNeg45 (b : Nat → Bool) : literal (valuationOf b) (-45) = decide (1 ≤ countLit b [-45]) := by
  change literal b (-45) = decide (1 ≤ countLit b [-45])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-45) <;> decide
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
theorem meaningNeg11 (b : Nat → Bool) : literal (valuationOf b) (-11) = decide (1 ≤ countLit b [-11]) := by
  change literal b (-11) = decide (1 ≤ countLit b [-11])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-11) <;> decide
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
theorem meaning1169 (b : Nat → Bool) : literal (valuationOf b) 1169 = decide (1 ≤ count1169 b) := rfl
theorem meaning1171 (b : Nat → Bool) : literal (valuationOf b) 1171 = decide (1 ≤ count1171 b) := rfl
theorem meaning1172 (b : Nat → Bool) : literal (valuationOf b) 1172 = decide (2 ≤ count1171 b) := rfl
theorem meaning1174 (b : Nat → Bool) : literal (valuationOf b) 1174 = decide (1 ≤ count1174 b) := rfl
theorem meaning1176 (b : Nat → Bool) : literal (valuationOf b) 1176 = decide (1 ≤ count1176 b) := rfl
theorem meaning1180 (b : Nat → Bool) : literal (valuationOf b) 1180 = decide (2 ≤ count1179 b) := rfl
theorem meaning1185 (b : Nat → Bool) : literal (valuationOf b) 1185 = decide (1 ≤ count1185 b) := rfl
theorem meaning1187 (b : Nat → Bool) : literal (valuationOf b) 1187 = decide (1 ≤ count1187 b) := rfl
theorem meaning1190 (b : Nat → Bool) : literal (valuationOf b) 1190 = decide (1 ≤ count1190 b) := rfl
theorem meaning1192 (b : Nat → Bool) : literal (valuationOf b) 1192 = decide (1 ≤ count1192 b) := rfl
theorem meaning1195 (b : Nat → Bool) : literal (valuationOf b) 1195 = decide (1 ≤ count1195 b) := rfl
theorem meaning1196 (b : Nat → Bool) : literal (valuationOf b) 1196 = decide (2 ≤ count1195 b) := rfl
theorem meaning1202 (b : Nat → Bool) : literal (valuationOf b) 1202 = decide (2 ≤ count1201 b) := rfl
theorem meaning1203 (b : Nat → Bool) : literal (valuationOf b) 1203 = decide (3 ≤ count1201 b) := rfl
theorem meaning1204 (b : Nat → Bool) : literal (valuationOf b) 1204 = decide (4 ≤ count1201 b) := rfl
theorem meaning1212 (b : Nat → Bool) : literal (valuationOf b) 1212 = decide (1 ≤ count1212 b) := rfl
theorem meaning1213 (b : Nat → Bool) : literal (valuationOf b) 1213 = decide (2 ≤ count1212 b) := rfl
theorem meaning1214 (b : Nat → Bool) : literal (valuationOf b) 1214 = decide (1 ≤ count1214 b) := rfl
theorem meaning1215 (b : Nat → Bool) : literal (valuationOf b) 1215 = decide (2 ≤ count1214 b) := rfl
theorem meaning1217 (b : Nat → Bool) : literal (valuationOf b) 1217 = decide (1 ≤ count1217 b) := rfl
theorem meaning1219 (b : Nat → Bool) : literal (valuationOf b) 1219 = decide (1 ≤ count1219 b) := rfl
theorem meaning1220 (b : Nat → Bool) : literal (valuationOf b) 1220 = decide (2 ≤ count1219 b) := rfl
theorem meaning1222 (b : Nat → Bool) : literal (valuationOf b) 1222 = decide (1 ≤ count1222 b) := rfl
theorem meaning1223 (b : Nat → Bool) : literal (valuationOf b) 1223 = decide (2 ≤ count1222 b) := rfl
theorem meaning1224 (b : Nat → Bool) : literal (valuationOf b) 1224 = decide (3 ≤ count1222 b) := rfl
theorem meaning1228 (b : Nat → Bool) : literal (valuationOf b) 1228 = decide (1 ≤ count1228 b) := rfl
theorem meaning1230 (b : Nat → Bool) : literal (valuationOf b) 1230 = decide (1 ≤ count1230 b) := rfl
theorem meaning1233 (b : Nat → Bool) : literal (valuationOf b) 1233 = decide (1 ≤ count1233 b) := rfl
theorem meaning1235 (b : Nat → Bool) : literal (valuationOf b) 1235 = decide (1 ≤ count1235 b) := rfl
theorem meaning1237 (b : Nat → Bool) : literal (valuationOf b) 1237 = decide (1 ≤ count1237 b) := rfl
theorem meaning1238 (b : Nat → Bool) : literal (valuationOf b) 1238 = decide (2 ≤ count1237 b) := rfl
theorem meaning1241 (b : Nat → Bool) : literal (valuationOf b) 1241 = decide (1 ≤ count1241 b) := rfl
theorem meaning1242 (b : Nat → Bool) : literal (valuationOf b) 1242 = decide (2 ≤ count1241 b) := rfl
theorem meaning1248 (b : Nat → Bool) : literal (valuationOf b) 1248 = decide (1 ≤ count1248 b) := rfl
theorem meaning1249 (b : Nat → Bool) : literal (valuationOf b) 1249 = decide (2 ≤ count1248 b) := rfl
theorem meaning1250 (b : Nat → Bool) : literal (valuationOf b) 1250 = decide (3 ≤ count1248 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (4 ≤ count1259 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (5 ≤ count1259 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (6 ≤ count1259 b) := rfl
theorem meaning1270 (b : Nat → Bool) : literal (valuationOf b) 1270 = decide (1 ≤ count1270 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (1 ≤ count1272 b) := rfl
theorem meaning1280 (b : Nat → Bool) : literal (valuationOf b) 1280 = decide (1 ≤ count1280 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (1 ≤ count1286 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (1 ≤ count1288 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (1 ≤ count1291 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (1 ≤ count1293 b) := rfl
theorem meaning1294 (b : Nat → Bool) : literal (valuationOf b) 1294 = decide (2 ≤ count1293 b) := rfl
theorem meaning1295 (b : Nat → Bool) : literal (valuationOf b) 1295 = decide (1 ≤ count1295 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (2 ≤ count1295 b) := rfl
theorem meaning1299 (b : Nat → Bool) : literal (valuationOf b) 1299 = decide (1 ≤ count1299 b) := rfl
theorem meaning1300 (b : Nat → Bool) : literal (valuationOf b) 1300 = decide (2 ≤ count1299 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (3 ≤ count1299 b) := rfl
theorem meaning1307 (b : Nat → Bool) : literal (valuationOf b) 1307 = decide (2 ≤ count1306 b) := rfl
theorem meaning1308 (b : Nat → Bool) : literal (valuationOf b) 1308 = decide (3 ≤ count1306 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (4 ≤ count1306 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (1 ≤ count1317 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (2 ≤ count1317 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (1 ≤ count1319 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (2 ≤ count1319 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (3 ≤ count1319 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (1 ≤ count1322 b) := rfl
theorem meaning1324 (b : Nat → Bool) : literal (valuationOf b) 1324 = decide (1 ≤ count1324 b) := rfl
theorem meaning1325 (b : Nat → Bool) : literal (valuationOf b) 1325 = decide (2 ≤ count1324 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (1 ≤ count1327 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (2 ≤ count1327 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (3 ≤ count1327 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (4 ≤ count1327 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (1 ≤ count1333 b) := rfl
theorem meaning1335 (b : Nat → Bool) : literal (valuationOf b) 1335 = decide (1 ≤ count1335 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (1 ≤ count1338 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (2 ≤ count1338 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (1 ≤ count1342 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (2 ≤ count1342 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (3 ≤ count1342 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (1 ≤ count1346 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (2 ≤ count1346 b) := rfl
theorem meaning1348 (b : Nat → Bool) : literal (valuationOf b) 1348 = decide (3 ≤ count1346 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (2 ≤ count1353 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (3 ≤ count1353 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (4 ≤ count1353 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (5 ≤ count1353 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (5 ≤ count1364 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (6 ≤ count1364 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (7 ≤ count1364 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (11 ≤ count1375 b) := rfl
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
end Snake9.Regrowth.E112098
