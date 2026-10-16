import E112118Data
namespace Snake9.Regrowth.E112118
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 98 then (if i < 49 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (36 : Vertex)) else decide (InPath q (39 : Vertex)))) else (if i < 4 then decide (InPath q (44 : Vertex)) else (if i < 5 then decide (InPath q (52 : Vertex)) else decide (InPath q (53 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (55 : Vertex)) else (if i < 8 then decide (InPath q (72 : Vertex)) else decide (InPath q (130 : Vertex)))) else (if i < 10 then decide (InPath q (132 : Vertex)) else (if i < 11 then decide (InPath q (135 : Vertex)) else decide (InPath q (136 : Vertex)))))) else (if i < 18 then (if i < 15 then (if i < 13 then decide (InPath q (137 : Vertex)) else (if i < 14 then decide (InPath q (138 : Vertex)) else decide (InPath q (140 : Vertex)))) else (if i < 16 then decide (InPath q (142 : Vertex)) else (if i < 17 then decide (InPath q (148 : Vertex)) else decide (InPath q (149 : Vertex))))) else (if i < 21 then (if i < 19 then decide (InPath q (151 : Vertex)) else (if i < 20 then decide (InPath q (153 : Vertex)) else decide (InPath q (154 : Vertex)))) else (if i < 22 then decide (InPath q (155 : Vertex)) else (if i < 23 then decide (InPath q (159 : Vertex)) else decide (InPath q (192 : Vertex))))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then decide (InPath q (193 : Vertex)) else (if i < 26 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex)))) else (if i < 28 then decide (InPath q (201 : Vertex)) else (if i < 29 then decide (InPath q (205 : Vertex)) else decide (InPath q (207 : Vertex))))) else (if i < 33 then (if i < 31 then decide (InPath q (209 : Vertex)) else (if i < 32 then decide (InPath q (210 : Vertex)) else decide (InPath q (211 : Vertex)))) else (if i < 34 then decide (InPath q (214 : Vertex)) else (if i < 35 then decide (InPath q (218 : Vertex)) else decide (InPath q (220 : Vertex)))))) else (if i < 42 then (if i < 39 then (if i < 37 then decide (InPath q (221 : Vertex)) else (if i < 38 then decide (InPath q (222 : Vertex)) else decide (InPath q (288 : Vertex)))) else (if i < 40 then decide (InPath q (289 : Vertex)) else (if i < 41 then decide (InPath q (294 : Vertex)) else decide (InPath q (295 : Vertex))))) else (if i < 45 then (if i < 43 then decide (InPath q (296 : Vertex)) else (if i < 44 then decide (InPath q (301 : Vertex)) else decide (InPath q (303 : Vertex)))) else (if i < 47 then (if i < 46 then decide (InPath q (305 : Vertex)) else decide (InPath q (306 : Vertex))) else (if i < 48 then decide (InPath q (307 : Vertex)) else decide (InPath q (310 : Vertex)))))))) else (if i < 73 then (if i < 61 then (if i < 55 then (if i < 52 then (if i < 50 then decide (InPath q (316 : Vertex)) else (if i < 51 then decide (InPath q (317 : Vertex)) else decide (InPath q (318 : Vertex)))) else (if i < 53 then decide (InPath q (320 : Vertex)) else (if i < 54 then decide (InPath q (321 : Vertex)) else decide (InPath q (327 : Vertex))))) else (if i < 58 then (if i < 56 then decide (InPath q (328 : Vertex)) else (if i < 57 then decide (InPath q (329 : Vertex)) else decide (InPath q (333 : Vertex)))) else (if i < 59 then decide (InPath q (335 : Vertex)) else (if i < 60 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex)))))) else (if i < 67 then (if i < 64 then (if i < 62 then decide (InPath q (339 : Vertex)) else (if i < 63 then decide (InPath q (340 : Vertex)) else decide (InPath q (342 : Vertex)))) else (if i < 65 then decide (InPath q (346 : Vertex)) else (if i < 66 then decide (InPath q (348 : Vertex)) else decide (InPath q (349 : Vertex))))) else (if i < 70 then (if i < 68 then decide (InPath q (350 : Vertex)) else (if i < 69 then decide (InPath q (390 : Vertex)) else decide (InPath q (392 : Vertex)))) else (if i < 71 then decide (InPath q (393 : Vertex)) else (if i < 72 then decide (InPath q (397 : Vertex)) else decide (InPath q (399 : Vertex))))))) else (if i < 85 then (if i < 79 then (if i < 76 then (if i < 74 then decide (InPath q (406 : Vertex)) else (if i < 75 then decide (InPath q (410 : Vertex)) else decide (InPath q (412 : Vertex)))) else (if i < 77 then decide (InPath q (413 : Vertex)) else (if i < 78 then decide (InPath q (414 : Vertex)) else decide (InPath q (418 : Vertex))))) else (if i < 82 then (if i < 80 then decide (InPath q (422 : Vertex)) else (if i < 81 then decide (InPath q (424 : Vertex)) else decide (InPath q (428 : Vertex)))) else (if i < 83 then decide (InPath q (430 : Vertex)) else (if i < 84 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex)))))) else (if i < 91 then (if i < 88 then (if i < 86 then decide (InPath q (486 : Vertex)) else (if i < 87 then decide (InPath q (487 : Vertex)) else decide (InPath q (488 : Vertex)))) else (if i < 89 then decide (InPath q (489 : Vertex)) else (if i < 90 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 94 then (if i < 92 then decide (InPath q (497 : Vertex)) else (if i < 93 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 96 then (if i < 95 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 97 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 147 then (if i < 122 then (if i < 110 then (if i < 104 then (if i < 101 then (if i < 99 then decide (InPath q (510 : Vertex)) else (if i < 100 then decide (BallClauseLogic.Endpoint q (36 : Vertex)) else decide (BallClauseLogic.Endpoint q (39 : Vertex)))) else (if i < 102 then decide (BallClauseLogic.Endpoint q (44 : Vertex)) else (if i < 103 then decide (BallClauseLogic.Endpoint q (52 : Vertex)) else decide (BallClauseLogic.Endpoint q (53 : Vertex))))) else (if i < 107 then (if i < 105 then decide (BallClauseLogic.Endpoint q (55 : Vertex)) else (if i < 106 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex)))) else (if i < 108 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else (if i < 109 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex)))))) else (if i < 116 then (if i < 113 then (if i < 111 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (140 : Vertex)))) else (if i < 114 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else (if i < 115 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (149 : Vertex))))) else (if i < 119 then (if i < 117 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else (if i < 118 then decide (BallClauseLogic.Endpoint q (153 : Vertex)) else decide (BallClauseLogic.Endpoint q (154 : Vertex)))) else (if i < 120 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else (if i < 121 then decide (BallClauseLogic.Endpoint q (159 : Vertex)) else decide (BallClauseLogic.Endpoint q (192 : Vertex))))))) else (if i < 134 then (if i < 128 then (if i < 125 then (if i < 123 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (200 : Vertex)))) else (if i < 126 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else (if i < 127 then decide (BallClauseLogic.Endpoint q (205 : Vertex)) else decide (BallClauseLogic.Endpoint q (207 : Vertex))))) else (if i < 131 then (if i < 129 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else (if i < 130 then decide (BallClauseLogic.Endpoint q (210 : Vertex)) else decide (BallClauseLogic.Endpoint q (211 : Vertex)))) else (if i < 132 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else (if i < 133 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (220 : Vertex)))))) else (if i < 140 then (if i < 137 then (if i < 135 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else (if i < 136 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else decide (BallClauseLogic.Endpoint q (288 : Vertex)))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (289 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (294 : Vertex)) else decide (BallClauseLogic.Endpoint q (295 : Vertex))))) else (if i < 143 then (if i < 141 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else (if i < 142 then decide (BallClauseLogic.Endpoint q (301 : Vertex)) else decide (BallClauseLogic.Endpoint q (303 : Vertex)))) else (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (305 : Vertex)) else decide (BallClauseLogic.Endpoint q (306 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (307 : Vertex)) else decide (BallClauseLogic.Endpoint q (310 : Vertex)))))))) else (if i < 172 then (if i < 159 then (if i < 153 then (if i < 150 then (if i < 148 then decide (BallClauseLogic.Endpoint q (316 : Vertex)) else (if i < 149 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex)))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else (if i < 152 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (327 : Vertex))))) else (if i < 156 then (if i < 154 then decide (BallClauseLogic.Endpoint q (328 : Vertex)) else (if i < 155 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else decide (BallClauseLogic.Endpoint q (333 : Vertex)))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (335 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (338 : Vertex)))))) else (if i < 165 then (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (339 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (340 : Vertex)) else decide (BallClauseLogic.Endpoint q (342 : Vertex)))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else decide (BallClauseLogic.Endpoint q (349 : Vertex))))) else (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (350 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (390 : Vertex)) else decide (BallClauseLogic.Endpoint q (392 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (393 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (399 : Vertex)) else decide (BallClauseLogic.Endpoint q (406 : Vertex))))))) else (if i < 184 then (if i < 178 then (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (410 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex)))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex))))) else (if i < 181 then (if i < 179 then decide (BallClauseLogic.Endpoint q (424 : Vertex)) else (if i < 180 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else decide (BallClauseLogic.Endpoint q (430 : Vertex)))) else (if i < 182 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else (if i < 183 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex)))))) else (if i < 190 then (if i < 187 then (if i < 185 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else (if i < 186 then decide (BallClauseLogic.Endpoint q (488 : Vertex)) else decide (BallClauseLogic.Endpoint q (489 : Vertex)))) else (if i < 188 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else (if i < 189 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 193 then (if i < 191 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else (if i < 192 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count197 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count199 (b : Nat → Bool) : Nat := countLit b [99, 100, 102]
def count201 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count203 (b : Nat → Bool) : Nat := countLit b [103, 104, 105]
def count205 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 103, 104, 105]
def count207 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count209 (b : Nat → Bool) : Nat := countLit b [106, 107, 108]
def count211 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count213 (b : Nat → Bool) : Nat := countLit b [109, 110, 111]
def count215 (b : Nat → Bool) : Nat := countLit b [106, 107, 108, 109, 110, 111]
def count217 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111]
def count219 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count221 (b : Nat → Bool) : Nat := countLit b [112, 113, 114]
def count223 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count225 (b : Nat → Bool) : Nat := countLit b [115, 116, 117]
def count227 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count231 (b : Nat → Bool) : Nat := countLit b [118, 119, 120]
def count233 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count235 (b : Nat → Bool) : Nat := countLit b [121, 122, 123]
def count237 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123]
def count239 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
def count241 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count245 (b : Nat → Bool) : Nat := countLit b [124, 125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count249 (b : Nat → Bool) : Nat := countLit b [127, 128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count255 (b : Nat → Bool) : Nat := countLit b [130, 131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count259 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count261 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count273 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count281 (b : Nat → Bool) : Nat := countLit b [145, 146, 147]
def count283 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145, 146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153]
def count301 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count303 (b : Nat → Bool) : Nat := countLit b [154, 155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count307 (b : Nat → Bool) : Nat := countLit b [157, 158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 170, 171]
def count331 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count343 (b : Nat → Bool) : Nat := countLit b [175, 176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count349 (b : Nat → Bool) : Nat := countLit b [178, 179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count353 (b : Nat → Bool) : Nat := countLit b [181, 182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188, 189]
def count367 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count371 (b : Nat → Bool) : Nat := countLit b [190, 191, 192]
def count373 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count375 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count377 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196]
def count379 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196]
def count381 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196]
def count387 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196]
def count389 (b : Nat → Bool) : Nat := countLit b [2, 5]
def count391 (b : Nat → Bool) : Nat := countLit b [1, 2, 5]
def count394 (b : Nat → Bool) : Nat := countLit b [8, 9]
def count396 (b : Nat → Bool) : Nat := countLit b [7, 8, 9]
def count399 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 8, 9]
def count405 (b : Nat → Bool) : Nat := countLit b [11, 15]
def count407 (b : Nat → Bool) : Nat := countLit b [10, 11, 15]
def count410 (b : Nat → Bool) : Nat := countLit b [19, 20]
def count412 (b : Nat → Bool) : Nat := countLit b [17, 19, 20]
def count415 (b : Nat → Bool) : Nat := countLit b [10, 11, 15, 17, 19, 20]
def count421 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 8, 9, 10, 11, 15, 17, 19, 20]
def count433 (b : Nat → Bool) : Nat := countLit b [23, 27]
def count435 (b : Nat → Bool) : Nat := countLit b [22, 23, 27]
def count438 (b : Nat → Bool) : Nat := countLit b [30, 31]
def count440 (b : Nat → Bool) : Nat := countLit b [29, 30, 31]
def count443 (b : Nat → Bool) : Nat := countLit b [22, 23, 27, 29, 30, 31]
def count449 (b : Nat → Bool) : Nat := countLit b [37, 38]
def count451 (b : Nat → Bool) : Nat := countLit b [36, 37, 38]
def count454 (b : Nat → Bool) : Nat := countLit b [40, 44]
def count456 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count458 (b : Nat → Bool) : Nat := countLit b [40, 44, 45, 46]
def count462 (b : Nat → Bool) : Nat := countLit b [36, 37, 38, 40, 44, 45, 46]
def count469 (b : Nat → Bool) : Nat := countLit b [22, 23, 27, 29, 30, 31, 36, 37, 38, 40, 44, 45, 46]
def count482 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 8, 9, 10, 11, 15, 17, 19, 20, 22, 23, 27, 29, 30, 31, 36, 37, 38, 40, 44, 45, 46]
def count507 (b : Nat → Bool) : Nat := countLit b [51, 52]
def count509 (b : Nat → Bool) : Nat := countLit b [50, 51, 52]
def count512 (b : Nat → Bool) : Nat := countLit b [58, 59]
def count514 (b : Nat → Bool) : Nat := countLit b [56, 58, 59]
def count517 (b : Nat → Bool) : Nat := countLit b [50, 51, 52, 56, 58, 59]
def count523 (b : Nat → Bool) : Nat := countLit b [62, 66]
def count525 (b : Nat → Bool) : Nat := countLit b [60, 62, 66]
def count528 (b : Nat → Bool) : Nat := countLit b [67, 68]
def count530 (b : Nat → Bool) : Nat := countLit b [70, 72]
def count532 (b : Nat → Bool) : Nat := countLit b [67, 68, 70, 72]
def count536 (b : Nat → Bool) : Nat := countLit b [60, 62, 66, 67, 68, 70, 72]
def count543 (b : Nat → Bool) : Nat := countLit b [50, 51, 52, 56, 58, 59, 60, 62, 66, 67, 68, 70, 72]
def count556 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count558 (b : Nat → Bool) : Nat := countLit b [76, 77, 78]
def count561 (b : Nat → Bool) : Nat := countLit b [82, 83]
def count563 (b : Nat → Bool) : Nat := countLit b [80, 82, 83]
def count566 (b : Nat → Bool) : Nat := countLit b [76, 77, 78, 80, 82, 83]
def count572 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count574 (b : Nat → Bool) : Nat := countLit b [85, 88, 90]
def count577 (b : Nat → Bool) : Nat := countLit b [91, 92]
def count579 (b : Nat → Bool) : Nat := countLit b [97, 98]
def count581 (b : Nat → Bool) : Nat := countLit b [91, 92, 97, 98]
def count585 (b : Nat → Bool) : Nat := countLit b [85, 88, 90, 91, 92, 97, 98]
def count592 (b : Nat → Bool) : Nat := countLit b [76, 77, 78, 80, 82, 83, 85, 88, 90, 91, 92, 97, 98]
def count605 (b : Nat → Bool) : Nat := countLit b [50, 51, 52, 56, 58, 59, 60, 62, 66, 67, 68, 70, 72, 76, 77, 78, 80, 82, 83, 85, 88, 90, 91, 92, 97, 98]
def count631 (b : Nat → Bool) : Nat := countLit b [1, 2, 5, 7, 8, 9, 10, 11, 15, 17, 19, 20, 22, 23, 27, 29, 30, 31, 36, 37, 38, 40, 44, 45, 46, 50, 51, 52, 56, 58, 59, 60, 62, 66, 67, 68, 70, 72, 76, 77, 78, 80, 82, 83, 85, 88, 90, 91, 92, 97, 98]
def count673 (b : Nat → Bool) : Nat := countLit b [-2, -5]
def count675 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5]
def count678 (b : Nat → Bool) : Nat := countLit b [-8, -9]
def count680 (b : Nat → Bool) : Nat := countLit b [-7, -8, -9]
def count683 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -8, -9]
def count689 (b : Nat → Bool) : Nat := countLit b [-11, -15]
def count691 (b : Nat → Bool) : Nat := countLit b [-10, -11, -15]
def count694 (b : Nat → Bool) : Nat := countLit b [-19, -20]
def count696 (b : Nat → Bool) : Nat := countLit b [-17, -19, -20]
def count699 (b : Nat → Bool) : Nat := countLit b [-10, -11, -15, -17, -19, -20]
def count705 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -8, -9, -10, -11, -15, -17, -19, -20]
def count716 (b : Nat → Bool) : Nat := countLit b [-23, -27]
def count718 (b : Nat → Bool) : Nat := countLit b [-22, -23, -27]
def count721 (b : Nat → Bool) : Nat := countLit b [-30, -31]
def count723 (b : Nat → Bool) : Nat := countLit b [-29, -30, -31]
def count726 (b : Nat → Bool) : Nat := countLit b [-22, -23, -27, -29, -30, -31]
def count732 (b : Nat → Bool) : Nat := countLit b [-37, -38]
def count734 (b : Nat → Bool) : Nat := countLit b [-36, -37, -38]
def count737 (b : Nat → Bool) : Nat := countLit b [-40, -44]
def count739 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count741 (b : Nat → Bool) : Nat := countLit b [-40, -44, -45, -46]
def count745 (b : Nat → Bool) : Nat := countLit b [-36, -37, -38, -40, -44, -45, -46]
def count752 (b : Nat → Bool) : Nat := countLit b [-22, -23, -27, -29, -30, -31, -36, -37, -38, -40, -44, -45, -46]
def count763 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -8, -9, -10, -11, -15, -17, -19, -20, -22, -23, -27, -29, -30, -31, -36, -37, -38, -40, -44, -45, -46]
def count774 (b : Nat → Bool) : Nat := countLit b [-51, -52]
def count776 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52]
def count779 (b : Nat → Bool) : Nat := countLit b [-58, -59]
def count781 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59]
def count784 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52, -56, -58, -59]
def count790 (b : Nat → Bool) : Nat := countLit b [-62, -66]
def count792 (b : Nat → Bool) : Nat := countLit b [-60, -62, -66]
def count795 (b : Nat → Bool) : Nat := countLit b [-67, -68]
def count797 (b : Nat → Bool) : Nat := countLit b [-70, -72]
def count799 (b : Nat → Bool) : Nat := countLit b [-67, -68, -70, -72]
def count803 (b : Nat → Bool) : Nat := countLit b [-60, -62, -66, -67, -68, -70, -72]
def count810 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52, -56, -58, -59, -60, -62, -66, -67, -68, -70, -72]
def count821 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count823 (b : Nat → Bool) : Nat := countLit b [-76, -77, -78]
def count826 (b : Nat → Bool) : Nat := countLit b [-82, -83]
def count828 (b : Nat → Bool) : Nat := countLit b [-80, -82, -83]
def count831 (b : Nat → Bool) : Nat := countLit b [-76, -77, -78, -80, -82, -83]
def count837 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count839 (b : Nat → Bool) : Nat := countLit b [-85, -88, -90]
def count842 (b : Nat → Bool) : Nat := countLit b [-91, -92]
def count844 (b : Nat → Bool) : Nat := countLit b [-97, -98]
def count846 (b : Nat → Bool) : Nat := countLit b [-91, -92, -97, -98]
def count850 (b : Nat → Bool) : Nat := countLit b [-85, -88, -90, -91, -92, -97, -98]
def count857 (b : Nat → Bool) : Nat := countLit b [-76, -77, -78, -80, -82, -83, -85, -88, -90, -91, -92, -97, -98]
def count868 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52, -56, -58, -59, -60, -62, -66, -67, -68, -70, -72, -76, -77, -78, -80, -82, -83, -85, -88, -90, -91, -92, -97, -98]
def count879 (b : Nat → Bool) : Nat := countLit b [-1, -2, -5, -7, -8, -9, -10, -11, -15, -17, -19, -20, -22, -23, -27, -29, -30, -31, -36, -37, -38, -40, -44, -45, -46, -50, -51, -52, -56, -58, -59, -60, -62, -66, -67, -68, -70, -72, -76, -77, -78, -80, -82, -83, -85, -88, -90, -91, -92, -97, -98]
def count890 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count892 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count894 (b : Nat → Bool) : Nat := countLit b [6, 12, 13]
def count897 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 12, 13]
def count902 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count904 (b : Nat → Bool) : Nat := countLit b [14, 16, 18]
def count907 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count909 (b : Nat → Bool) : Nat := countLit b [21, 24, 25]
def count912 (b : Nat → Bool) : Nat := countLit b [14, 16, 18, 21, 24, 25]
def count918 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 12, 13, 14, 16, 18, 21, 24, 25]
def count929 (b : Nat → Bool) : Nat := countLit b [28, 32]
def count931 (b : Nat → Bool) : Nat := countLit b [26, 28, 32]
def count934 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count936 (b : Nat → Bool) : Nat := countLit b [33, 34, 35]
def count939 (b : Nat → Bool) : Nat := countLit b [26, 28, 32, 33, 34, 35]
def count945 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count947 (b : Nat → Bool) : Nat := countLit b [39, 41, 42]
def count950 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count952 (b : Nat → Bool) : Nat := countLit b [43, 47, 48]
def count955 (b : Nat → Bool) : Nat := countLit b [39, 41, 42, 43, 47, 48]
def count961 (b : Nat → Bool) : Nat := countLit b [26, 28, 32, 33, 34, 35, 39, 41, 42, 43, 47, 48]
def count973 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 12, 13, 14, 16, 18, 21, 24, 25, 26, 28, 32, 33, 34, 35, 39, 41, 42, 43, 47, 48]
def count996 (b : Nat → Bool) : Nat := countLit b [53, 54]
def count998 (b : Nat → Bool) : Nat := countLit b [49, 53, 54]
def count1001 (b : Nat → Bool) : Nat := countLit b [57, 61]
def count1003 (b : Nat → Bool) : Nat := countLit b [55, 57, 61]
def count1006 (b : Nat → Bool) : Nat := countLit b [49, 53, 54, 55, 57, 61]
def count1012 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count1014 (b : Nat → Bool) : Nat := countLit b [63, 64, 65]
def count1017 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count1019 (b : Nat → Bool) : Nat := countLit b [69, 71, 73]
def count1022 (b : Nat → Bool) : Nat := countLit b [63, 64, 65, 69, 71, 73]
def count1028 (b : Nat → Bool) : Nat := countLit b [49, 53, 54, 55, 57, 61, 63, 64, 65, 69, 71, 73]
def count1040 (b : Nat → Bool) : Nat := countLit b [75, 79]
def count1042 (b : Nat → Bool) : Nat := countLit b [74, 75, 79]
def count1045 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count1047 (b : Nat → Bool) : Nat := countLit b [81, 84, 86]
def count1050 (b : Nat → Bool) : Nat := countLit b [74, 75, 79, 81, 84, 86]
def count1056 (b : Nat → Bool) : Nat := countLit b [89, 93]
def count1058 (b : Nat → Bool) : Nat := countLit b [87, 89, 93]
def count1061 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count1063 (b : Nat → Bool) : Nat := countLit b [94, 95, 96]
def count1066 (b : Nat → Bool) : Nat := countLit b [87, 89, 93, 94, 95, 96]
def count1072 (b : Nat → Bool) : Nat := countLit b [74, 75, 79, 81, 84, 86, 87, 89, 93, 94, 95, 96]
def count1084 (b : Nat → Bool) : Nat := countLit b [49, 53, 54, 55, 57, 61, 63, 64, 65, 69, 71, 73, 74, 75, 79, 81, 84, 86, 87, 89, 93, 94, 95, 96]
def count1108 (b : Nat → Bool) : Nat := countLit b [3, 4, 6, 12, 13, 14, 16, 18, 21, 24, 25, 26, 28, 32, 33, 34, 35, 39, 41, 42, 43, 47, 48, 49, 53, 54, 55, 57, 61, 63, 64, 65, 69, 71, 73, 74, 75, 79, 81, 84, 86, 87, 89, 93, 94, 95, 96]
def count1150 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count1152 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count1154 (b : Nat → Bool) : Nat := countLit b [-6, -12, -13]
def count1157 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -12, -13]
def count1162 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1164 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18]
def count1167 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count1169 (b : Nat → Bool) : Nat := countLit b [-21, -24, -25]
def count1172 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18, -21, -24, -25]
def count1178 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25]
def count1185 (b : Nat → Bool) : Nat := countLit b [-28, -32]
def count1187 (b : Nat → Bool) : Nat := countLit b [-26, -28, -32]
def count1190 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count1192 (b : Nat → Bool) : Nat := countLit b [-33, -34, -35]
def count1195 (b : Nat → Bool) : Nat := countLit b [-26, -28, -32, -33, -34, -35]
def count1201 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count1203 (b : Nat → Bool) : Nat := countLit b [-39, -41, -42]
def count1206 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count1208 (b : Nat → Bool) : Nat := countLit b [-43, -47, -48]
def count1211 (b : Nat → Bool) : Nat := countLit b [-39, -41, -42, -43, -47, -48]
def count1217 (b : Nat → Bool) : Nat := countLit b [-26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]
def count1224 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48]
def count1231 (b : Nat → Bool) : Nat := countLit b [-53, -54]
def count1233 (b : Nat → Bool) : Nat := countLit b [-49, -53, -54]
def count1236 (b : Nat → Bool) : Nat := countLit b [-57, -61]
def count1238 (b : Nat → Bool) : Nat := countLit b [-55, -57, -61]
def count1241 (b : Nat → Bool) : Nat := countLit b [-49, -53, -54, -55, -57, -61]
def count1247 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count1249 (b : Nat → Bool) : Nat := countLit b [-63, -64, -65]
def count1252 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count1254 (b : Nat → Bool) : Nat := countLit b [-69, -71, -73]
def count1257 (b : Nat → Bool) : Nat := countLit b [-63, -64, -65, -69, -71, -73]
def count1263 (b : Nat → Bool) : Nat := countLit b [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73]
def count1270 (b : Nat → Bool) : Nat := countLit b [-75, -79]
def count1272 (b : Nat → Bool) : Nat := countLit b [-74, -75, -79]
def count1275 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count1277 (b : Nat → Bool) : Nat := countLit b [-81, -84, -86]
def count1280 (b : Nat → Bool) : Nat := countLit b [-74, -75, -79, -81, -84, -86]
def count1286 (b : Nat → Bool) : Nat := countLit b [-89, -93]
def count1288 (b : Nat → Bool) : Nat := countLit b [-87, -89, -93]
def count1291 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count1293 (b : Nat → Bool) : Nat := countLit b [-94, -95, -96]
def count1296 (b : Nat → Bool) : Nat := countLit b [-87, -89, -93, -94, -95, -96]
def count1302 (b : Nat → Bool) : Nat := countLit b [-74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]
def count1309 (b : Nat → Bool) : Nat := countLit b [-49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]
def count1316 (b : Nat → Bool) : Nat := countLit b [-3, -4, -6, -12, -13, -14, -16, -18, -21, -24, -25, -26, -28, -32, -33, -34, -35, -39, -41, -42, -43, -47, -48, -49, -53, -54, -55, -57, -61, -63, -64, -65, -69, -71, -73, -74, -75, -79, -81, -84, -86, -87, -89, -93, -94, -95, -96]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 661 then (if i < 330 then (if i < 165 then (if i < 82 then (if i < 41 then (if i < 20 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 7 then (if i < 6 then b 5 else b 6) else (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)))) else (if i < 15 then (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else (if i < 14 then b 13 else b 14))) else (if i < 17 then (if i < 16 then b 15 else b 16) else (if i < 18 then b 17 else (if i < 19 then b 18 else b 19))))) else (if i < 30 then (if i < 25 then (if i < 22 then (if i < 21 then b 20 else b 21) else (if i < 23 then b 22 else (if i < 24 then b 23 else b 24))) else (if i < 27 then (if i < 26 then b 25 else b 26) else (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)))) else (if i < 35 then (if i < 32 then (if i < 31 then b 30 else b 31) else (if i < 33 then b 32 else (if i < 34 then b 33 else b 34))) else (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 39 then b 38 else (if i < 40 then b 39 else b 40)))))) else (if i < 61 then (if i < 51 then (if i < 46 then (if i < 43 then (if i < 42 then b 41 else b 42) else (if i < 44 then b 43 else (if i < 45 then b 44 else b 45))) else (if i < 48 then (if i < 47 then b 46 else b 47) else (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)))) else (if i < 56 then (if i < 53 then (if i < 52 then b 51 else b 52) else (if i < 54 then b 53 else (if i < 55 then b 54 else b 55))) else (if i < 58 then (if i < 57 then b 56 else b 57) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60))))) else (if i < 71 then (if i < 66 then (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else (if i < 65 then b 64 else b 65))) else (if i < 68 then (if i < 67 then b 66 else b 67) else (if i < 69 then b 68 else (if i < 70 then b 69 else b 70)))) else (if i < 76 then (if i < 73 then (if i < 72 then b 71 else b 72) else (if i < 74 then b 73 else (if i < 75 then b 74 else b 75))) else (if i < 79 then (if i < 77 then b 76 else (if i < 78 then b 77 else b 78)) else (if i < 80 then b 79 else (if i < 81 then b 80 else b 81))))))) else (if i < 123 then (if i < 102 then (if i < 92 then (if i < 87 then (if i < 84 then (if i < 83 then b 82 else b 83) else (if i < 85 then b 84 else (if i < 86 then b 85 else b 86))) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else (if i < 91 then b 90 else b 91)))) else (if i < 97 then (if i < 94 then (if i < 93 then b 92 else b 93) else (if i < 95 then b 94 else (if i < 96 then b 95 else b 96))) else (if i < 99 then (if i < 98 then b 97 else b 98) else (if i < 100 then b 99 else (if i < 101 then b 100 else b 101))))) else (if i < 112 then (if i < 107 then (if i < 104 then (if i < 103 then b 102 else b 103) else (if i < 105 then b 104 else (if i < 106 then b 105 else b 106))) else (if i < 109 then (if i < 108 then b 107 else b 108) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111)))) else (if i < 117 then (if i < 114 then (if i < 113 then b 112 else b 113) else (if i < 115 then b 114 else (if i < 116 then b 115 else b 116))) else (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)))))) else (if i < 144 then (if i < 133 then (if i < 128 then (if i < 125 then (if i < 124 then b 123 else b 124) else (if i < 126 then b 125 else (if i < 127 then b 126 else b 127))) else (if i < 130 then (if i < 129 then b 128 else b 129) else (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)))) else (if i < 138 then (if i < 135 then (if i < 134 then b 133 else b 134) else (if i < 136 then b 135 else (if i < 137 then b 136 else b 137))) else (if i < 141 then (if i < 139 then b 138 else (if i < 140 then b 139 else b 140)) else (if i < 142 then b 141 else (if i < 143 then b 142 else b 143))))) else (if i < 154 then (if i < 149 then (if i < 146 then (if i < 145 then b 144 else b 145) else (if i < 147 then b 146 else (if i < 148 then b 147 else b 148))) else (if i < 151 then (if i < 150 then b 149 else b 150) else (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)))) else (if i < 159 then (if i < 156 then (if i < 155 then b 154 else b 155) else (if i < 157 then b 156 else (if i < 158 then b 157 else b 158))) else (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)))))))) else (if i < 247 then (if i < 206 then (if i < 185 then (if i < 175 then (if i < 170 then (if i < 167 then (if i < 166 then b 165 else b 166) else (if i < 168 then b 167 else (if i < 169 then b 168 else b 169))) else (if i < 172 then (if i < 171 then b 170 else b 171) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174)))) else (if i < 180 then (if i < 177 then (if i < 176 then b 175 else b 176) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179))) else (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else (if i < 184 then b 183 else b 184))))) else (if i < 195 then (if i < 190 then (if i < 187 then (if i < 186 then b 185 else b 186) else (if i < 188 then b 187 else (if i < 189 then b 188 else b 189))) else (if i < 192 then (if i < 191 then b 190 else b 191) else (if i < 193 then b 192 else (if i < 194 then b 193 else b 194)))) else (if i < 200 then (if i < 197 then (if i < 196 then b 195 else b 196) else (if i < 198 then decide (1 ≤ count197 b) else (if i < 199 then decide (2 ≤ count197 b) else decide (1 ≤ count199 b)))) else (if i < 203 then (if i < 201 then decide (2 ≤ count199 b) else (if i < 202 then decide (1 ≤ count201 b) else decide (2 ≤ count201 b))) else (if i < 204 then decide (1 ≤ count203 b) else (if i < 205 then decide (2 ≤ count203 b) else decide (1 ≤ count205 b))))))) else (if i < 226 then (if i < 216 then (if i < 211 then (if i < 208 then (if i < 207 then decide (2 ≤ count205 b) else decide (1 ≤ count207 b)) else (if i < 209 then decide (2 ≤ count207 b) else (if i < 210 then decide (1 ≤ count209 b) else decide (2 ≤ count209 b)))) else (if i < 213 then (if i < 212 then decide (1 ≤ count211 b) else decide (2 ≤ count211 b)) else (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))))) else (if i < 221 then (if i < 218 then (if i < 217 then decide (2 ≤ count215 b) else decide (1 ≤ count217 b)) else (if i < 219 then decide (2 ≤ count217 b) else (if i < 220 then decide (1 ≤ count219 b) else decide (2 ≤ count219 b)))) else (if i < 223 then (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b)) else (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b)))))) else (if i < 236 then (if i < 231 then (if i < 228 then (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b)) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b)))) else (if i < 233 then (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b)) else (if i < 234 then decide (1 ≤ count233 b) else (if i < 235 then decide (2 ≤ count233 b) else decide (1 ≤ count235 b))))) else (if i < 241 then (if i < 238 then (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b)) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))) else (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 245 then decide (2 ≤ count243 b) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)))))))) else (if i < 288 then (if i < 267 then (if i < 257 then (if i < 252 then (if i < 249 then (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)))) else (if i < 254 then (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)) else (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b))))) else (if i < 262 then (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))) else (if i < 264 then (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))))) else (if i < 277 then (if i < 272 then (if i < 269 then (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b)) else (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)))) else (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))))) else (if i < 282 then (if i < 279 then (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)) else (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)))) else (if i < 285 then (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))) else (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))))))) else (if i < 309 then (if i < 298 then (if i < 293 then (if i < 290 then (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)) else (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))) else (if i < 295 then (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)) else (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))))) else (if i < 303 then (if i < 300 then (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)) else (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b)))) else (if i < 306 then (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b))) else (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))))) else (if i < 319 then (if i < 314 then (if i < 311 then (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)) else (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)))) else (if i < 316 then (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))))) else (if i < 324 then (if i < 321 then (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)) else (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)))) else (if i < 327 then (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))) else (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)))))))))) else (if i < 495 then (if i < 412 then (if i < 371 then (if i < 350 then (if i < 340 then (if i < 335 then (if i < 332 then (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)) else (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b)))) else (if i < 337 then (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)) else (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))))) else (if i < 345 then (if i < 342 then (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)) else (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)))) else (if i < 347 then (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)) else (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))))) else (if i < 360 then (if i < 355 then (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)))) else (if i < 357 then (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))))) else (if i < 365 then (if i < 362 then (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)) else (if i < 363 then decide (2 ≤ count361 b) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b)))) else (if i < 368 then (if i < 366 then decide (1 ≤ count365 b) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))) else (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))))))) else (if i < 391 then (if i < 381 then (if i < 376 then (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)))) else (if i < 378 then (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)) else (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))))) else (if i < 386 then (if i < 383 then (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)) else (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)))) else (if i < 388 then (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)) else (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))))) else (if i < 401 then (if i < 396 then (if i < 393 then (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b)) else (if i < 394 then decide (3 ≤ count391 b) else (if i < 395 then decide (1 ≤ count394 b) else decide (2 ≤ count394 b)))) else (if i < 398 then (if i < 397 then decide (1 ≤ count396 b) else decide (2 ≤ count396 b)) else (if i < 399 then decide (3 ≤ count396 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))))) else (if i < 406 then (if i < 403 then (if i < 402 then decide (3 ≤ count399 b) else decide (4 ≤ count399 b)) else (if i < 404 then decide (5 ≤ count399 b) else (if i < 405 then decide (6 ≤ count399 b) else decide (1 ≤ count405 b)))) else (if i < 409 then (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b))) else (if i < 410 then decide (3 ≤ count407 b) else (if i < 411 then decide (1 ≤ count410 b) else decide (2 ≤ count410 b)))))))) else (if i < 453 then (if i < 432 then (if i < 422 then (if i < 417 then (if i < 414 then (if i < 413 then decide (1 ≤ count412 b) else decide (2 ≤ count412 b)) else (if i < 415 then decide (3 ≤ count412 b) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b)))) else (if i < 419 then (if i < 418 then decide (3 ≤ count415 b) else decide (4 ≤ count415 b)) else (if i < 420 then decide (5 ≤ count415 b) else (if i < 421 then decide (6 ≤ count415 b) else decide (1 ≤ count421 b))))) else (if i < 427 then (if i < 424 then (if i < 423 then decide (2 ≤ count421 b) else decide (3 ≤ count421 b)) else (if i < 425 then decide (4 ≤ count421 b) else (if i < 426 then decide (5 ≤ count421 b) else decide (6 ≤ count421 b)))) else (if i < 429 then (if i < 428 then decide (7 ≤ count421 b) else decide (8 ≤ count421 b)) else (if i < 430 then decide (9 ≤ count421 b) else (if i < 431 then decide (10 ≤ count421 b) else decide (11 ≤ count421 b)))))) else (if i < 442 then (if i < 437 then (if i < 434 then (if i < 433 then decide (12 ≤ count421 b) else decide (1 ≤ count433 b)) else (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))) else (if i < 439 then (if i < 438 then decide (3 ≤ count435 b) else decide (1 ≤ count438 b)) else (if i < 440 then decide (2 ≤ count438 b) else (if i < 441 then decide (1 ≤ count440 b) else decide (2 ≤ count440 b))))) else (if i < 447 then (if i < 444 then (if i < 443 then decide (3 ≤ count440 b) else decide (1 ≤ count443 b)) else (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (3 ≤ count443 b) else decide (4 ≤ count443 b)))) else (if i < 450 then (if i < 448 then decide (5 ≤ count443 b) else (if i < 449 then decide (6 ≤ count443 b) else decide (1 ≤ count449 b))) else (if i < 451 then decide (2 ≤ count449 b) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))))))) else (if i < 474 then (if i < 463 then (if i < 458 then (if i < 455 then (if i < 454 then decide (3 ≤ count451 b) else decide (1 ≤ count454 b)) else (if i < 456 then decide (2 ≤ count454 b) else (if i < 457 then decide (1 ≤ count456 b) else decide (2 ≤ count456 b)))) else (if i < 460 then (if i < 459 then decide (1 ≤ count458 b) else decide (2 ≤ count458 b)) else (if i < 461 then decide (3 ≤ count458 b) else (if i < 462 then decide (4 ≤ count458 b) else decide (1 ≤ count462 b))))) else (if i < 468 then (if i < 465 then (if i < 464 then decide (2 ≤ count462 b) else decide (3 ≤ count462 b)) else (if i < 466 then decide (4 ≤ count462 b) else (if i < 467 then decide (5 ≤ count462 b) else decide (6 ≤ count462 b)))) else (if i < 471 then (if i < 469 then decide (7 ≤ count462 b) else (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b))) else (if i < 472 then decide (3 ≤ count469 b) else (if i < 473 then decide (4 ≤ count469 b) else decide (5 ≤ count469 b)))))) else (if i < 484 then (if i < 479 then (if i < 476 then (if i < 475 then decide (6 ≤ count469 b) else decide (7 ≤ count469 b)) else (if i < 477 then decide (8 ≤ count469 b) else (if i < 478 then decide (9 ≤ count469 b) else decide (10 ≤ count469 b)))) else (if i < 481 then (if i < 480 then decide (11 ≤ count469 b) else decide (12 ≤ count469 b)) else (if i < 482 then decide (13 ≤ count469 b) else (if i < 483 then decide (1 ≤ count482 b) else decide (2 ≤ count482 b))))) else (if i < 489 then (if i < 486 then (if i < 485 then decide (3 ≤ count482 b) else decide (4 ≤ count482 b)) else (if i < 487 then decide (5 ≤ count482 b) else (if i < 488 then decide (6 ≤ count482 b) else decide (7 ≤ count482 b)))) else (if i < 492 then (if i < 490 then decide (8 ≤ count482 b) else (if i < 491 then decide (9 ≤ count482 b) else decide (10 ≤ count482 b))) else (if i < 493 then decide (11 ≤ count482 b) else (if i < 494 then decide (12 ≤ count482 b) else decide (13 ≤ count482 b))))))))) else (if i < 578 then (if i < 536 then (if i < 515 then (if i < 505 then (if i < 500 then (if i < 497 then (if i < 496 then decide (14 ≤ count482 b) else decide (15 ≤ count482 b)) else (if i < 498 then decide (16 ≤ count482 b) else (if i < 499 then decide (17 ≤ count482 b) else decide (18 ≤ count482 b)))) else (if i < 502 then (if i < 501 then decide (19 ≤ count482 b) else decide (20 ≤ count482 b)) else (if i < 503 then decide (21 ≤ count482 b) else (if i < 504 then decide (22 ≤ count482 b) else decide (23 ≤ count482 b))))) else (if i < 510 then (if i < 507 then (if i < 506 then decide (24 ≤ count482 b) else decide (25 ≤ count482 b)) else (if i < 508 then decide (1 ≤ count507 b) else (if i < 509 then decide (2 ≤ count507 b) else decide (1 ≤ count509 b)))) else (if i < 512 then (if i < 511 then decide (2 ≤ count509 b) else decide (3 ≤ count509 b)) else (if i < 513 then decide (1 ≤ count512 b) else (if i < 514 then decide (2 ≤ count512 b) else decide (1 ≤ count514 b)))))) else (if i < 525 then (if i < 520 then (if i < 517 then (if i < 516 then decide (2 ≤ count514 b) else decide (3 ≤ count514 b)) else (if i < 518 then decide (1 ≤ count517 b) else (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b)))) else (if i < 522 then (if i < 521 then decide (4 ≤ count517 b) else decide (5 ≤ count517 b)) else (if i < 523 then decide (6 ≤ count517 b) else (if i < 524 then decide (1 ≤ count523 b) else decide (2 ≤ count523 b))))) else (if i < 530 then (if i < 527 then (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b)) else (if i < 528 then decide (3 ≤ count525 b) else (if i < 529 then decide (1 ≤ count528 b) else decide (2 ≤ count528 b)))) else (if i < 533 then (if i < 531 then decide (1 ≤ count530 b) else (if i < 532 then decide (2 ≤ count530 b) else decide (1 ≤ count532 b))) else (if i < 534 then decide (2 ≤ count532 b) else (if i < 535 then decide (3 ≤ count532 b) else decide (4 ≤ count532 b))))))) else (if i < 557 then (if i < 546 then (if i < 541 then (if i < 538 then (if i < 537 then decide (1 ≤ count536 b) else decide (2 ≤ count536 b)) else (if i < 539 then decide (3 ≤ count536 b) else (if i < 540 then decide (4 ≤ count536 b) else decide (5 ≤ count536 b)))) else (if i < 543 then (if i < 542 then decide (6 ≤ count536 b) else decide (7 ≤ count536 b)) else (if i < 544 then decide (1 ≤ count543 b) else (if i < 545 then decide (2 ≤ count543 b) else decide (3 ≤ count543 b))))) else (if i < 551 then (if i < 548 then (if i < 547 then decide (4 ≤ count543 b) else decide (5 ≤ count543 b)) else (if i < 549 then decide (6 ≤ count543 b) else (if i < 550 then decide (7 ≤ count543 b) else decide (8 ≤ count543 b)))) else (if i < 554 then (if i < 552 then decide (9 ≤ count543 b) else (if i < 553 then decide (10 ≤ count543 b) else decide (11 ≤ count543 b))) else (if i < 555 then decide (12 ≤ count543 b) else (if i < 556 then decide (13 ≤ count543 b) else decide (1 ≤ count556 b)))))) else (if i < 567 then (if i < 562 then (if i < 559 then (if i < 558 then decide (2 ≤ count556 b) else decide (1 ≤ count558 b)) else (if i < 560 then decide (2 ≤ count558 b) else (if i < 561 then decide (3 ≤ count558 b) else decide (1 ≤ count561 b)))) else (if i < 564 then (if i < 563 then decide (2 ≤ count561 b) else decide (1 ≤ count563 b)) else (if i < 565 then decide (2 ≤ count563 b) else (if i < 566 then decide (3 ≤ count563 b) else decide (1 ≤ count566 b))))) else (if i < 572 then (if i < 569 then (if i < 568 then decide (2 ≤ count566 b) else decide (3 ≤ count566 b)) else (if i < 570 then decide (4 ≤ count566 b) else (if i < 571 then decide (5 ≤ count566 b) else decide (6 ≤ count566 b)))) else (if i < 575 then (if i < 573 then decide (1 ≤ count572 b) else (if i < 574 then decide (2 ≤ count572 b) else decide (1 ≤ count574 b))) else (if i < 576 then decide (2 ≤ count574 b) else (if i < 577 then decide (3 ≤ count574 b) else decide (1 ≤ count577 b)))))))) else (if i < 619 then (if i < 598 then (if i < 588 then (if i < 583 then (if i < 580 then (if i < 579 then decide (2 ≤ count577 b) else decide (1 ≤ count579 b)) else (if i < 581 then decide (2 ≤ count579 b) else (if i < 582 then decide (1 ≤ count581 b) else decide (2 ≤ count581 b)))) else (if i < 585 then (if i < 584 then decide (3 ≤ count581 b) else decide (4 ≤ count581 b)) else (if i < 586 then decide (1 ≤ count585 b) else (if i < 587 then decide (2 ≤ count585 b) else decide (3 ≤ count585 b))))) else (if i < 593 then (if i < 590 then (if i < 589 then decide (4 ≤ count585 b) else decide (5 ≤ count585 b)) else (if i < 591 then decide (6 ≤ count585 b) else (if i < 592 then decide (7 ≤ count585 b) else decide (1 ≤ count592 b)))) else (if i < 595 then (if i < 594 then decide (2 ≤ count592 b) else decide (3 ≤ count592 b)) else (if i < 596 then decide (4 ≤ count592 b) else (if i < 597 then decide (5 ≤ count592 b) else decide (6 ≤ count592 b)))))) else (if i < 608 then (if i < 603 then (if i < 600 then (if i < 599 then decide (7 ≤ count592 b) else decide (8 ≤ count592 b)) else (if i < 601 then decide (9 ≤ count592 b) else (if i < 602 then decide (10 ≤ count592 b) else decide (11 ≤ count592 b)))) else (if i < 605 then (if i < 604 then decide (12 ≤ count592 b) else decide (13 ≤ count592 b)) else (if i < 606 then decide (1 ≤ count605 b) else (if i < 607 then decide (2 ≤ count605 b) else decide (3 ≤ count605 b))))) else (if i < 613 then (if i < 610 then (if i < 609 then decide (4 ≤ count605 b) else decide (5 ≤ count605 b)) else (if i < 611 then decide (6 ≤ count605 b) else (if i < 612 then decide (7 ≤ count605 b) else decide (8 ≤ count605 b)))) else (if i < 616 then (if i < 614 then decide (9 ≤ count605 b) else (if i < 615 then decide (10 ≤ count605 b) else decide (11 ≤ count605 b))) else (if i < 617 then decide (12 ≤ count605 b) else (if i < 618 then decide (13 ≤ count605 b) else decide (14 ≤ count605 b))))))) else (if i < 640 then (if i < 629 then (if i < 624 then (if i < 621 then (if i < 620 then decide (15 ≤ count605 b) else decide (16 ≤ count605 b)) else (if i < 622 then decide (17 ≤ count605 b) else (if i < 623 then decide (18 ≤ count605 b) else decide (19 ≤ count605 b)))) else (if i < 626 then (if i < 625 then decide (20 ≤ count605 b) else decide (21 ≤ count605 b)) else (if i < 627 then decide (22 ≤ count605 b) else (if i < 628 then decide (23 ≤ count605 b) else decide (24 ≤ count605 b))))) else (if i < 634 then (if i < 631 then (if i < 630 then decide (25 ≤ count605 b) else decide (26 ≤ count605 b)) else (if i < 632 then decide (1 ≤ count631 b) else (if i < 633 then decide (2 ≤ count631 b) else decide (3 ≤ count631 b)))) else (if i < 637 then (if i < 635 then decide (4 ≤ count631 b) else (if i < 636 then decide (5 ≤ count631 b) else decide (6 ≤ count631 b))) else (if i < 638 then decide (7 ≤ count631 b) else (if i < 639 then decide (8 ≤ count631 b) else decide (9 ≤ count631 b)))))) else (if i < 650 then (if i < 645 then (if i < 642 then (if i < 641 then decide (10 ≤ count631 b) else decide (11 ≤ count631 b)) else (if i < 643 then decide (12 ≤ count631 b) else (if i < 644 then decide (13 ≤ count631 b) else decide (14 ≤ count631 b)))) else (if i < 647 then (if i < 646 then decide (15 ≤ count631 b) else decide (16 ≤ count631 b)) else (if i < 648 then decide (17 ≤ count631 b) else (if i < 649 then decide (18 ≤ count631 b) else decide (19 ≤ count631 b))))) else (if i < 655 then (if i < 652 then (if i < 651 then decide (20 ≤ count631 b) else decide (21 ≤ count631 b)) else (if i < 653 then decide (22 ≤ count631 b) else (if i < 654 then decide (23 ≤ count631 b) else decide (24 ≤ count631 b)))) else (if i < 658 then (if i < 656 then decide (25 ≤ count631 b) else (if i < 657 then decide (26 ≤ count631 b) else decide (27 ≤ count631 b))) else (if i < 659 then decide (28 ≤ count631 b) else (if i < 660 then decide (29 ≤ count631 b) else decide (30 ≤ count631 b))))))))))) else (if i < 992 then (if i < 826 then (if i < 743 then (if i < 702 then (if i < 681 then (if i < 671 then (if i < 666 then (if i < 663 then (if i < 662 then decide (31 ≤ count631 b) else decide (32 ≤ count631 b)) else (if i < 664 then decide (33 ≤ count631 b) else (if i < 665 then decide (34 ≤ count631 b) else decide (35 ≤ count631 b)))) else (if i < 668 then (if i < 667 then decide (36 ≤ count631 b) else decide (37 ≤ count631 b)) else (if i < 669 then decide (38 ≤ count631 b) else (if i < 670 then decide (39 ≤ count631 b) else decide (40 ≤ count631 b))))) else (if i < 676 then (if i < 673 then (if i < 672 then decide (41 ≤ count631 b) else decide (42 ≤ count631 b)) else (if i < 674 then decide (1 ≤ count673 b) else (if i < 675 then decide (2 ≤ count673 b) else decide (1 ≤ count675 b)))) else (if i < 678 then (if i < 677 then decide (2 ≤ count675 b) else decide (3 ≤ count675 b)) else (if i < 679 then decide (1 ≤ count678 b) else (if i < 680 then decide (2 ≤ count678 b) else decide (1 ≤ count680 b)))))) else (if i < 691 then (if i < 686 then (if i < 683 then (if i < 682 then decide (2 ≤ count680 b) else decide (3 ≤ count680 b)) else (if i < 684 then decide (1 ≤ count683 b) else (if i < 685 then decide (2 ≤ count683 b) else decide (3 ≤ count683 b)))) else (if i < 688 then (if i < 687 then decide (4 ≤ count683 b) else decide (5 ≤ count683 b)) else (if i < 689 then decide (6 ≤ count683 b) else (if i < 690 then decide (1 ≤ count689 b) else decide (2 ≤ count689 b))))) else (if i < 696 then (if i < 693 then (if i < 692 then decide (1 ≤ count691 b) else decide (2 ≤ count691 b)) else (if i < 694 then decide (3 ≤ count691 b) else (if i < 695 then decide (1 ≤ count694 b) else decide (2 ≤ count694 b)))) else (if i < 699 then (if i < 697 then decide (1 ≤ count696 b) else (if i < 698 then decide (2 ≤ count696 b) else decide (3 ≤ count696 b))) else (if i < 700 then decide (1 ≤ count699 b) else (if i < 701 then decide (2 ≤ count699 b) else decide (3 ≤ count699 b))))))) else (if i < 722 then (if i < 712 then (if i < 707 then (if i < 704 then (if i < 703 then decide (4 ≤ count699 b) else decide (5 ≤ count699 b)) else (if i < 705 then decide (6 ≤ count699 b) else (if i < 706 then decide (1 ≤ count705 b) else decide (2 ≤ count705 b)))) else (if i < 709 then (if i < 708 then decide (3 ≤ count705 b) else decide (4 ≤ count705 b)) else (if i < 710 then decide (5 ≤ count705 b) else (if i < 711 then decide (6 ≤ count705 b) else decide (7 ≤ count705 b))))) else (if i < 717 then (if i < 714 then (if i < 713 then decide (8 ≤ count705 b) else decide (9 ≤ count705 b)) else (if i < 715 then decide (10 ≤ count705 b) else (if i < 716 then decide (11 ≤ count705 b) else decide (1 ≤ count716 b)))) else (if i < 719 then (if i < 718 then decide (2 ≤ count716 b) else decide (1 ≤ count718 b)) else (if i < 720 then decide (2 ≤ count718 b) else (if i < 721 then decide (3 ≤ count718 b) else decide (1 ≤ count721 b)))))) else (if i < 732 then (if i < 727 then (if i < 724 then (if i < 723 then decide (2 ≤ count721 b) else decide (1 ≤ count723 b)) else (if i < 725 then decide (2 ≤ count723 b) else (if i < 726 then decide (3 ≤ count723 b) else decide (1 ≤ count726 b)))) else (if i < 729 then (if i < 728 then decide (2 ≤ count726 b) else decide (3 ≤ count726 b)) else (if i < 730 then decide (4 ≤ count726 b) else (if i < 731 then decide (5 ≤ count726 b) else decide (6 ≤ count726 b))))) else (if i < 737 then (if i < 734 then (if i < 733 then decide (1 ≤ count732 b) else decide (2 ≤ count732 b)) else (if i < 735 then decide (1 ≤ count734 b) else (if i < 736 then decide (2 ≤ count734 b) else decide (3 ≤ count734 b)))) else (if i < 740 then (if i < 738 then decide (1 ≤ count737 b) else (if i < 739 then decide (2 ≤ count737 b) else decide (1 ≤ count739 b))) else (if i < 741 then decide (2 ≤ count739 b) else (if i < 742 then decide (1 ≤ count741 b) else decide (2 ≤ count741 b)))))))) else (if i < 784 then (if i < 763 then (if i < 753 then (if i < 748 then (if i < 745 then (if i < 744 then decide (3 ≤ count741 b) else decide (4 ≤ count741 b)) else (if i < 746 then decide (1 ≤ count745 b) else (if i < 747 then decide (2 ≤ count745 b) else decide (3 ≤ count745 b)))) else (if i < 750 then (if i < 749 then decide (4 ≤ count745 b) else decide (5 ≤ count745 b)) else (if i < 751 then decide (6 ≤ count745 b) else (if i < 752 then decide (7 ≤ count745 b) else decide (1 ≤ count752 b))))) else (if i < 758 then (if i < 755 then (if i < 754 then decide (2 ≤ count752 b) else decide (3 ≤ count752 b)) else (if i < 756 then decide (4 ≤ count752 b) else (if i < 757 then decide (5 ≤ count752 b) else decide (6 ≤ count752 b)))) else (if i < 760 then (if i < 759 then decide (7 ≤ count752 b) else decide (8 ≤ count752 b)) else (if i < 761 then decide (9 ≤ count752 b) else (if i < 762 then decide (10 ≤ count752 b) else decide (11 ≤ count752 b)))))) else (if i < 773 then (if i < 768 then (if i < 765 then (if i < 764 then decide (1 ≤ count763 b) else decide (2 ≤ count763 b)) else (if i < 766 then decide (3 ≤ count763 b) else (if i < 767 then decide (4 ≤ count763 b) else decide (5 ≤ count763 b)))) else (if i < 770 then (if i < 769 then decide (6 ≤ count763 b) else decide (7 ≤ count763 b)) else (if i < 771 then decide (8 ≤ count763 b) else (if i < 772 then decide (9 ≤ count763 b) else decide (10 ≤ count763 b))))) else (if i < 778 then (if i < 775 then (if i < 774 then decide (11 ≤ count763 b) else decide (1 ≤ count774 b)) else (if i < 776 then decide (2 ≤ count774 b) else (if i < 777 then decide (1 ≤ count776 b) else decide (2 ≤ count776 b)))) else (if i < 781 then (if i < 779 then decide (3 ≤ count776 b) else (if i < 780 then decide (1 ≤ count779 b) else decide (2 ≤ count779 b))) else (if i < 782 then decide (1 ≤ count781 b) else (if i < 783 then decide (2 ≤ count781 b) else decide (3 ≤ count781 b))))))) else (if i < 805 then (if i < 794 then (if i < 789 then (if i < 786 then (if i < 785 then decide (1 ≤ count784 b) else decide (2 ≤ count784 b)) else (if i < 787 then decide (3 ≤ count784 b) else (if i < 788 then decide (4 ≤ count784 b) else decide (5 ≤ count784 b)))) else (if i < 791 then (if i < 790 then decide (6 ≤ count784 b) else decide (1 ≤ count790 b)) else (if i < 792 then decide (2 ≤ count790 b) else (if i < 793 then decide (1 ≤ count792 b) else decide (2 ≤ count792 b))))) else (if i < 799 then (if i < 796 then (if i < 795 then decide (3 ≤ count792 b) else decide (1 ≤ count795 b)) else (if i < 797 then decide (2 ≤ count795 b) else (if i < 798 then decide (1 ≤ count797 b) else decide (2 ≤ count797 b)))) else (if i < 802 then (if i < 800 then decide (1 ≤ count799 b) else (if i < 801 then decide (2 ≤ count799 b) else decide (3 ≤ count799 b))) else (if i < 803 then decide (4 ≤ count799 b) else (if i < 804 then decide (1 ≤ count803 b) else decide (2 ≤ count803 b)))))) else (if i < 815 then (if i < 810 then (if i < 807 then (if i < 806 then decide (3 ≤ count803 b) else decide (4 ≤ count803 b)) else (if i < 808 then decide (5 ≤ count803 b) else (if i < 809 then decide (6 ≤ count803 b) else decide (7 ≤ count803 b)))) else (if i < 812 then (if i < 811 then decide (1 ≤ count810 b) else decide (2 ≤ count810 b)) else (if i < 813 then decide (3 ≤ count810 b) else (if i < 814 then decide (4 ≤ count810 b) else decide (5 ≤ count810 b))))) else (if i < 820 then (if i < 817 then (if i < 816 then decide (6 ≤ count810 b) else decide (7 ≤ count810 b)) else (if i < 818 then decide (8 ≤ count810 b) else (if i < 819 then decide (9 ≤ count810 b) else decide (10 ≤ count810 b)))) else (if i < 823 then (if i < 821 then decide (11 ≤ count810 b) else (if i < 822 then decide (1 ≤ count821 b) else decide (2 ≤ count821 b))) else (if i < 824 then decide (1 ≤ count823 b) else (if i < 825 then decide (2 ≤ count823 b) else decide (3 ≤ count823 b))))))))) else (if i < 909 then (if i < 867 then (if i < 846 then (if i < 836 then (if i < 831 then (if i < 828 then (if i < 827 then decide (1 ≤ count826 b) else decide (2 ≤ count826 b)) else (if i < 829 then decide (1 ≤ count828 b) else (if i < 830 then decide (2 ≤ count828 b) else decide (3 ≤ count828 b)))) else (if i < 833 then (if i < 832 then decide (1 ≤ count831 b) else decide (2 ≤ count831 b)) else (if i < 834 then decide (3 ≤ count831 b) else (if i < 835 then decide (4 ≤ count831 b) else decide (5 ≤ count831 b))))) else (if i < 841 then (if i < 838 then (if i < 837 then decide (6 ≤ count831 b) else decide (1 ≤ count837 b)) else (if i < 839 then decide (2 ≤ count837 b) else (if i < 840 then decide (1 ≤ count839 b) else decide (2 ≤ count839 b)))) else (if i < 843 then (if i < 842 then decide (3 ≤ count839 b) else decide (1 ≤ count842 b)) else (if i < 844 then decide (2 ≤ count842 b) else (if i < 845 then decide (1 ≤ count844 b) else decide (2 ≤ count844 b)))))) else (if i < 856 then (if i < 851 then (if i < 848 then (if i < 847 then decide (1 ≤ count846 b) else decide (2 ≤ count846 b)) else (if i < 849 then decide (3 ≤ count846 b) else (if i < 850 then decide (4 ≤ count846 b) else decide (1 ≤ count850 b)))) else (if i < 853 then (if i < 852 then decide (2 ≤ count850 b) else decide (3 ≤ count850 b)) else (if i < 854 then decide (4 ≤ count850 b) else (if i < 855 then decide (5 ≤ count850 b) else decide (6 ≤ count850 b))))) else (if i < 861 then (if i < 858 then (if i < 857 then decide (7 ≤ count850 b) else decide (1 ≤ count857 b)) else (if i < 859 then decide (2 ≤ count857 b) else (if i < 860 then decide (3 ≤ count857 b) else decide (4 ≤ count857 b)))) else (if i < 864 then (if i < 862 then decide (5 ≤ count857 b) else (if i < 863 then decide (6 ≤ count857 b) else decide (7 ≤ count857 b))) else (if i < 865 then decide (8 ≤ count857 b) else (if i < 866 then decide (9 ≤ count857 b) else decide (10 ≤ count857 b))))))) else (if i < 888 then (if i < 877 then (if i < 872 then (if i < 869 then (if i < 868 then decide (11 ≤ count857 b) else decide (1 ≤ count868 b)) else (if i < 870 then decide (2 ≤ count868 b) else (if i < 871 then decide (3 ≤ count868 b) else decide (4 ≤ count868 b)))) else (if i < 874 then (if i < 873 then decide (5 ≤ count868 b) else decide (6 ≤ count868 b)) else (if i < 875 then decide (7 ≤ count868 b) else (if i < 876 then decide (8 ≤ count868 b) else decide (9 ≤ count868 b))))) else (if i < 882 then (if i < 879 then (if i < 878 then decide (10 ≤ count868 b) else decide (11 ≤ count868 b)) else (if i < 880 then decide (1 ≤ count879 b) else (if i < 881 then decide (2 ≤ count879 b) else decide (3 ≤ count879 b)))) else (if i < 885 then (if i < 883 then decide (4 ≤ count879 b) else (if i < 884 then decide (5 ≤ count879 b) else decide (6 ≤ count879 b))) else (if i < 886 then decide (7 ≤ count879 b) else (if i < 887 then decide (8 ≤ count879 b) else decide (9 ≤ count879 b)))))) else (if i < 898 then (if i < 893 then (if i < 890 then (if i < 889 then decide (10 ≤ count879 b) else decide (11 ≤ count879 b)) else (if i < 891 then decide (1 ≤ count890 b) else (if i < 892 then decide (2 ≤ count890 b) else decide (1 ≤ count892 b)))) else (if i < 895 then (if i < 894 then decide (2 ≤ count892 b) else decide (1 ≤ count894 b)) else (if i < 896 then decide (2 ≤ count894 b) else (if i < 897 then decide (3 ≤ count894 b) else decide (1 ≤ count897 b))))) else (if i < 903 then (if i < 900 then (if i < 899 then decide (2 ≤ count897 b) else decide (3 ≤ count897 b)) else (if i < 901 then decide (4 ≤ count897 b) else (if i < 902 then decide (5 ≤ count897 b) else decide (1 ≤ count902 b)))) else (if i < 906 then (if i < 904 then decide (2 ≤ count902 b) else (if i < 905 then decide (1 ≤ count904 b) else decide (2 ≤ count904 b))) else (if i < 907 then decide (3 ≤ count904 b) else (if i < 908 then decide (1 ≤ count907 b) else decide (2 ≤ count907 b)))))))) else (if i < 950 then (if i < 929 then (if i < 919 then (if i < 914 then (if i < 911 then (if i < 910 then decide (1 ≤ count909 b) else decide (2 ≤ count909 b)) else (if i < 912 then decide (3 ≤ count909 b) else (if i < 913 then decide (1 ≤ count912 b) else decide (2 ≤ count912 b)))) else (if i < 916 then (if i < 915 then decide (3 ≤ count912 b) else decide (4 ≤ count912 b)) else (if i < 917 then decide (5 ≤ count912 b) else (if i < 918 then decide (6 ≤ count912 b) else decide (1 ≤ count918 b))))) else (if i < 924 then (if i < 921 then (if i < 920 then decide (2 ≤ count918 b) else decide (3 ≤ count918 b)) else (if i < 922 then decide (4 ≤ count918 b) else (if i < 923 then decide (5 ≤ count918 b) else decide (6 ≤ count918 b)))) else (if i < 926 then (if i < 925 then decide (7 ≤ count918 b) else decide (8 ≤ count918 b)) else (if i < 927 then decide (9 ≤ count918 b) else (if i < 928 then decide (10 ≤ count918 b) else decide (11 ≤ count918 b)))))) else (if i < 939 then (if i < 934 then (if i < 931 then (if i < 930 then decide (1 ≤ count929 b) else decide (2 ≤ count929 b)) else (if i < 932 then decide (1 ≤ count931 b) else (if i < 933 then decide (2 ≤ count931 b) else decide (3 ≤ count931 b)))) else (if i < 936 then (if i < 935 then decide (1 ≤ count934 b) else decide (2 ≤ count934 b)) else (if i < 937 then decide (1 ≤ count936 b) else (if i < 938 then decide (2 ≤ count936 b) else decide (3 ≤ count936 b))))) else (if i < 944 then (if i < 941 then (if i < 940 then decide (1 ≤ count939 b) else decide (2 ≤ count939 b)) else (if i < 942 then decide (3 ≤ count939 b) else (if i < 943 then decide (4 ≤ count939 b) else decide (5 ≤ count939 b)))) else (if i < 947 then (if i < 945 then decide (6 ≤ count939 b) else (if i < 946 then decide (1 ≤ count945 b) else decide (2 ≤ count945 b))) else (if i < 948 then decide (1 ≤ count947 b) else (if i < 949 then decide (2 ≤ count947 b) else decide (3 ≤ count947 b))))))) else (if i < 971 then (if i < 960 then (if i < 955 then (if i < 952 then (if i < 951 then decide (1 ≤ count950 b) else decide (2 ≤ count950 b)) else (if i < 953 then decide (1 ≤ count952 b) else (if i < 954 then decide (2 ≤ count952 b) else decide (3 ≤ count952 b)))) else (if i < 957 then (if i < 956 then decide (1 ≤ count955 b) else decide (2 ≤ count955 b)) else (if i < 958 then decide (3 ≤ count955 b) else (if i < 959 then decide (4 ≤ count955 b) else decide (5 ≤ count955 b))))) else (if i < 965 then (if i < 962 then (if i < 961 then decide (6 ≤ count955 b) else decide (1 ≤ count961 b)) else (if i < 963 then decide (2 ≤ count961 b) else (if i < 964 then decide (3 ≤ count961 b) else decide (4 ≤ count961 b)))) else (if i < 968 then (if i < 966 then decide (5 ≤ count961 b) else (if i < 967 then decide (6 ≤ count961 b) else decide (7 ≤ count961 b))) else (if i < 969 then decide (8 ≤ count961 b) else (if i < 970 then decide (9 ≤ count961 b) else decide (10 ≤ count961 b)))))) else (if i < 981 then (if i < 976 then (if i < 973 then (if i < 972 then decide (11 ≤ count961 b) else decide (12 ≤ count961 b)) else (if i < 974 then decide (1 ≤ count973 b) else (if i < 975 then decide (2 ≤ count973 b) else decide (3 ≤ count973 b)))) else (if i < 978 then (if i < 977 then decide (4 ≤ count973 b) else decide (5 ≤ count973 b)) else (if i < 979 then decide (6 ≤ count973 b) else (if i < 980 then decide (7 ≤ count973 b) else decide (8 ≤ count973 b))))) else (if i < 986 then (if i < 983 then (if i < 982 then decide (9 ≤ count973 b) else decide (10 ≤ count973 b)) else (if i < 984 then decide (11 ≤ count973 b) else (if i < 985 then decide (12 ≤ count973 b) else decide (13 ≤ count973 b)))) else (if i < 989 then (if i < 987 then decide (14 ≤ count973 b) else (if i < 988 then decide (15 ≤ count973 b) else decide (16 ≤ count973 b))) else (if i < 990 then decide (17 ≤ count973 b) else (if i < 991 then decide (18 ≤ count973 b) else decide (19 ≤ count973 b)))))))))) else (if i < 1157 then (if i < 1074 then (if i < 1033 then (if i < 1012 then (if i < 1002 then (if i < 997 then (if i < 994 then (if i < 993 then decide (20 ≤ count973 b) else decide (21 ≤ count973 b)) else (if i < 995 then decide (22 ≤ count973 b) else (if i < 996 then decide (23 ≤ count973 b) else decide (1 ≤ count996 b)))) else (if i < 999 then (if i < 998 then decide (2 ≤ count996 b) else decide (1 ≤ count998 b)) else (if i < 1000 then decide (2 ≤ count998 b) else (if i < 1001 then decide (3 ≤ count998 b) else decide (1 ≤ count1001 b))))) else (if i < 1007 then (if i < 1004 then (if i < 1003 then decide (2 ≤ count1001 b) else decide (1 ≤ count1003 b)) else (if i < 1005 then decide (2 ≤ count1003 b) else (if i < 1006 then decide (3 ≤ count1003 b) else decide (1 ≤ count1006 b)))) else (if i < 1009 then (if i < 1008 then decide (2 ≤ count1006 b) else decide (3 ≤ count1006 b)) else (if i < 1010 then decide (4 ≤ count1006 b) else (if i < 1011 then decide (5 ≤ count1006 b) else decide (6 ≤ count1006 b)))))) else (if i < 1022 then (if i < 1017 then (if i < 1014 then (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b)) else (if i < 1015 then decide (1 ≤ count1014 b) else (if i < 1016 then decide (2 ≤ count1014 b) else decide (3 ≤ count1014 b)))) else (if i < 1019 then (if i < 1018 then decide (1 ≤ count1017 b) else decide (2 ≤ count1017 b)) else (if i < 1020 then decide (1 ≤ count1019 b) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (3 ≤ count1019 b))))) else (if i < 1027 then (if i < 1024 then (if i < 1023 then decide (1 ≤ count1022 b) else decide (2 ≤ count1022 b)) else (if i < 1025 then decide (3 ≤ count1022 b) else (if i < 1026 then decide (4 ≤ count1022 b) else decide (5 ≤ count1022 b)))) else (if i < 1030 then (if i < 1028 then decide (6 ≤ count1022 b) else (if i < 1029 then decide (1 ≤ count1028 b) else decide (2 ≤ count1028 b))) else (if i < 1031 then decide (3 ≤ count1028 b) else (if i < 1032 then decide (4 ≤ count1028 b) else decide (5 ≤ count1028 b))))))) else (if i < 1053 then (if i < 1043 then (if i < 1038 then (if i < 1035 then (if i < 1034 then decide (6 ≤ count1028 b) else decide (7 ≤ count1028 b)) else (if i < 1036 then decide (8 ≤ count1028 b) else (if i < 1037 then decide (9 ≤ count1028 b) else decide (10 ≤ count1028 b)))) else (if i < 1040 then (if i < 1039 then decide (11 ≤ count1028 b) else decide (12 ≤ count1028 b)) else (if i < 1041 then decide (1 ≤ count1040 b) else (if i < 1042 then decide (2 ≤ count1040 b) else decide (1 ≤ count1042 b))))) else (if i < 1048 then (if i < 1045 then (if i < 1044 then decide (2 ≤ count1042 b) else decide (3 ≤ count1042 b)) else (if i < 1046 then decide (1 ≤ count1045 b) else (if i < 1047 then decide (2 ≤ count1045 b) else decide (1 ≤ count1047 b)))) else (if i < 1050 then (if i < 1049 then decide (2 ≤ count1047 b) else decide (3 ≤ count1047 b)) else (if i < 1051 then decide (1 ≤ count1050 b) else (if i < 1052 then decide (2 ≤ count1050 b) else decide (3 ≤ count1050 b)))))) else (if i < 1063 then (if i < 1058 then (if i < 1055 then (if i < 1054 then decide (4 ≤ count1050 b) else decide (5 ≤ count1050 b)) else (if i < 1056 then decide (6 ≤ count1050 b) else (if i < 1057 then decide (1 ≤ count1056 b) else decide (2 ≤ count1056 b)))) else (if i < 1060 then (if i < 1059 then decide (1 ≤ count1058 b) else decide (2 ≤ count1058 b)) else (if i < 1061 then decide (3 ≤ count1058 b) else (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b))))) else (if i < 1068 then (if i < 1065 then (if i < 1064 then decide (1 ≤ count1063 b) else decide (2 ≤ count1063 b)) else (if i < 1066 then decide (3 ≤ count1063 b) else (if i < 1067 then decide (1 ≤ count1066 b) else decide (2 ≤ count1066 b)))) else (if i < 1071 then (if i < 1069 then decide (3 ≤ count1066 b) else (if i < 1070 then decide (4 ≤ count1066 b) else decide (5 ≤ count1066 b))) else (if i < 1072 then decide (6 ≤ count1066 b) else (if i < 1073 then decide (1 ≤ count1072 b) else decide (2 ≤ count1072 b)))))))) else (if i < 1115 then (if i < 1094 then (if i < 1084 then (if i < 1079 then (if i < 1076 then (if i < 1075 then decide (3 ≤ count1072 b) else decide (4 ≤ count1072 b)) else (if i < 1077 then decide (5 ≤ count1072 b) else (if i < 1078 then decide (6 ≤ count1072 b) else decide (7 ≤ count1072 b)))) else (if i < 1081 then (if i < 1080 then decide (8 ≤ count1072 b) else decide (9 ≤ count1072 b)) else (if i < 1082 then decide (10 ≤ count1072 b) else (if i < 1083 then decide (11 ≤ count1072 b) else decide (12 ≤ count1072 b))))) else (if i < 1089 then (if i < 1086 then (if i < 1085 then decide (1 ≤ count1084 b) else decide (2 ≤ count1084 b)) else (if i < 1087 then decide (3 ≤ count1084 b) else (if i < 1088 then decide (4 ≤ count1084 b) else decide (5 ≤ count1084 b)))) else (if i < 1091 then (if i < 1090 then decide (6 ≤ count1084 b) else decide (7 ≤ count1084 b)) else (if i < 1092 then decide (8 ≤ count1084 b) else (if i < 1093 then decide (9 ≤ count1084 b) else decide (10 ≤ count1084 b)))))) else (if i < 1104 then (if i < 1099 then (if i < 1096 then (if i < 1095 then decide (11 ≤ count1084 b) else decide (12 ≤ count1084 b)) else (if i < 1097 then decide (13 ≤ count1084 b) else (if i < 1098 then decide (14 ≤ count1084 b) else decide (15 ≤ count1084 b)))) else (if i < 1101 then (if i < 1100 then decide (16 ≤ count1084 b) else decide (17 ≤ count1084 b)) else (if i < 1102 then decide (18 ≤ count1084 b) else (if i < 1103 then decide (19 ≤ count1084 b) else decide (20 ≤ count1084 b))))) else (if i < 1109 then (if i < 1106 then (if i < 1105 then decide (21 ≤ count1084 b) else decide (22 ≤ count1084 b)) else (if i < 1107 then decide (23 ≤ count1084 b) else (if i < 1108 then decide (24 ≤ count1084 b) else decide (1 ≤ count1108 b)))) else (if i < 1112 then (if i < 1110 then decide (2 ≤ count1108 b) else (if i < 1111 then decide (3 ≤ count1108 b) else decide (4 ≤ count1108 b))) else (if i < 1113 then decide (5 ≤ count1108 b) else (if i < 1114 then decide (6 ≤ count1108 b) else decide (7 ≤ count1108 b))))))) else (if i < 1136 then (if i < 1125 then (if i < 1120 then (if i < 1117 then (if i < 1116 then decide (8 ≤ count1108 b) else decide (9 ≤ count1108 b)) else (if i < 1118 then decide (10 ≤ count1108 b) else (if i < 1119 then decide (11 ≤ count1108 b) else decide (12 ≤ count1108 b)))) else (if i < 1122 then (if i < 1121 then decide (13 ≤ count1108 b) else decide (14 ≤ count1108 b)) else (if i < 1123 then decide (15 ≤ count1108 b) else (if i < 1124 then decide (16 ≤ count1108 b) else decide (17 ≤ count1108 b))))) else (if i < 1130 then (if i < 1127 then (if i < 1126 then decide (18 ≤ count1108 b) else decide (19 ≤ count1108 b)) else (if i < 1128 then decide (20 ≤ count1108 b) else (if i < 1129 then decide (21 ≤ count1108 b) else decide (22 ≤ count1108 b)))) else (if i < 1133 then (if i < 1131 then decide (23 ≤ count1108 b) else (if i < 1132 then decide (24 ≤ count1108 b) else decide (25 ≤ count1108 b))) else (if i < 1134 then decide (26 ≤ count1108 b) else (if i < 1135 then decide (27 ≤ count1108 b) else decide (28 ≤ count1108 b)))))) else (if i < 1146 then (if i < 1141 then (if i < 1138 then (if i < 1137 then decide (29 ≤ count1108 b) else decide (30 ≤ count1108 b)) else (if i < 1139 then decide (31 ≤ count1108 b) else (if i < 1140 then decide (32 ≤ count1108 b) else decide (33 ≤ count1108 b)))) else (if i < 1143 then (if i < 1142 then decide (34 ≤ count1108 b) else decide (35 ≤ count1108 b)) else (if i < 1144 then decide (36 ≤ count1108 b) else (if i < 1145 then decide (37 ≤ count1108 b) else decide (38 ≤ count1108 b))))) else (if i < 1151 then (if i < 1148 then (if i < 1147 then decide (39 ≤ count1108 b) else decide (40 ≤ count1108 b)) else (if i < 1149 then decide (41 ≤ count1108 b) else (if i < 1150 then decide (42 ≤ count1108 b) else decide (1 ≤ count1150 b)))) else (if i < 1154 then (if i < 1152 then decide (2 ≤ count1150 b) else (if i < 1153 then decide (1 ≤ count1152 b) else decide (2 ≤ count1152 b))) else (if i < 1155 then decide (1 ≤ count1154 b) else (if i < 1156 then decide (2 ≤ count1154 b) else decide (3 ≤ count1154 b))))))))) else (if i < 1240 then (if i < 1198 then (if i < 1177 then (if i < 1167 then (if i < 1162 then (if i < 1159 then (if i < 1158 then decide (1 ≤ count1157 b) else decide (2 ≤ count1157 b)) else (if i < 1160 then decide (3 ≤ count1157 b) else (if i < 1161 then decide (4 ≤ count1157 b) else decide (5 ≤ count1157 b)))) else (if i < 1164 then (if i < 1163 then decide (1 ≤ count1162 b) else decide (2 ≤ count1162 b)) else (if i < 1165 then decide (1 ≤ count1164 b) else (if i < 1166 then decide (2 ≤ count1164 b) else decide (3 ≤ count1164 b))))) else (if i < 1172 then (if i < 1169 then (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b)) else (if i < 1170 then decide (1 ≤ count1169 b) else (if i < 1171 then decide (2 ≤ count1169 b) else decide (3 ≤ count1169 b)))) else (if i < 1174 then (if i < 1173 then decide (1 ≤ count1172 b) else decide (2 ≤ count1172 b)) else (if i < 1175 then decide (3 ≤ count1172 b) else (if i < 1176 then decide (4 ≤ count1172 b) else decide (5 ≤ count1172 b)))))) else (if i < 1187 then (if i < 1182 then (if i < 1179 then (if i < 1178 then decide (6 ≤ count1172 b) else decide (1 ≤ count1178 b)) else (if i < 1180 then decide (2 ≤ count1178 b) else (if i < 1181 then decide (3 ≤ count1178 b) else decide (4 ≤ count1178 b)))) else (if i < 1184 then (if i < 1183 then decide (5 ≤ count1178 b) else decide (6 ≤ count1178 b)) else (if i < 1185 then decide (7 ≤ count1178 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))))) else (if i < 1192 then (if i < 1189 then (if i < 1188 then decide (1 ≤ count1187 b) else decide (2 ≤ count1187 b)) else (if i < 1190 then decide (3 ≤ count1187 b) else (if i < 1191 then decide (1 ≤ count1190 b) else decide (2 ≤ count1190 b)))) else (if i < 1195 then (if i < 1193 then decide (1 ≤ count1192 b) else (if i < 1194 then decide (2 ≤ count1192 b) else decide (3 ≤ count1192 b))) else (if i < 1196 then decide (1 ≤ count1195 b) else (if i < 1197 then decide (2 ≤ count1195 b) else decide (3 ≤ count1195 b))))))) else (if i < 1219 then (if i < 1208 then (if i < 1203 then (if i < 1200 then (if i < 1199 then decide (4 ≤ count1195 b) else decide (5 ≤ count1195 b)) else (if i < 1201 then decide (6 ≤ count1195 b) else (if i < 1202 then decide (1 ≤ count1201 b) else decide (2 ≤ count1201 b)))) else (if i < 1205 then (if i < 1204 then decide (1 ≤ count1203 b) else decide (2 ≤ count1203 b)) else (if i < 1206 then decide (3 ≤ count1203 b) else (if i < 1207 then decide (1 ≤ count1206 b) else decide (2 ≤ count1206 b))))) else (if i < 1213 then (if i < 1210 then (if i < 1209 then decide (1 ≤ count1208 b) else decide (2 ≤ count1208 b)) else (if i < 1211 then decide (3 ≤ count1208 b) else (if i < 1212 then decide (1 ≤ count1211 b) else decide (2 ≤ count1211 b)))) else (if i < 1216 then (if i < 1214 then decide (3 ≤ count1211 b) else (if i < 1215 then decide (4 ≤ count1211 b) else decide (5 ≤ count1211 b))) else (if i < 1217 then decide (6 ≤ count1211 b) else (if i < 1218 then decide (1 ≤ count1217 b) else decide (2 ≤ count1217 b)))))) else (if i < 1229 then (if i < 1224 then (if i < 1221 then (if i < 1220 then decide (3 ≤ count1217 b) else decide (4 ≤ count1217 b)) else (if i < 1222 then decide (5 ≤ count1217 b) else (if i < 1223 then decide (6 ≤ count1217 b) else decide (7 ≤ count1217 b)))) else (if i < 1226 then (if i < 1225 then decide (1 ≤ count1224 b) else decide (2 ≤ count1224 b)) else (if i < 1227 then decide (3 ≤ count1224 b) else (if i < 1228 then decide (4 ≤ count1224 b) else decide (5 ≤ count1224 b))))) else (if i < 1234 then (if i < 1231 then (if i < 1230 then decide (6 ≤ count1224 b) else decide (7 ≤ count1224 b)) else (if i < 1232 then decide (1 ≤ count1231 b) else (if i < 1233 then decide (2 ≤ count1231 b) else decide (1 ≤ count1233 b)))) else (if i < 1237 then (if i < 1235 then decide (2 ≤ count1233 b) else (if i < 1236 then decide (3 ≤ count1233 b) else decide (1 ≤ count1236 b))) else (if i < 1238 then decide (2 ≤ count1236 b) else (if i < 1239 then decide (1 ≤ count1238 b) else decide (2 ≤ count1238 b)))))))) else (if i < 1281 then (if i < 1260 then (if i < 1250 then (if i < 1245 then (if i < 1242 then (if i < 1241 then decide (3 ≤ count1238 b) else decide (1 ≤ count1241 b)) else (if i < 1243 then decide (2 ≤ count1241 b) else (if i < 1244 then decide (3 ≤ count1241 b) else decide (4 ≤ count1241 b)))) else (if i < 1247 then (if i < 1246 then decide (5 ≤ count1241 b) else decide (6 ≤ count1241 b)) else (if i < 1248 then decide (1 ≤ count1247 b) else (if i < 1249 then decide (2 ≤ count1247 b) else decide (1 ≤ count1249 b))))) else (if i < 1255 then (if i < 1252 then (if i < 1251 then decide (2 ≤ count1249 b) else decide (3 ≤ count1249 b)) else (if i < 1253 then decide (1 ≤ count1252 b) else (if i < 1254 then decide (2 ≤ count1252 b) else decide (1 ≤ count1254 b)))) else (if i < 1257 then (if i < 1256 then decide (2 ≤ count1254 b) else decide (3 ≤ count1254 b)) else (if i < 1258 then decide (1 ≤ count1257 b) else (if i < 1259 then decide (2 ≤ count1257 b) else decide (3 ≤ count1257 b)))))) else (if i < 1270 then (if i < 1265 then (if i < 1262 then (if i < 1261 then decide (4 ≤ count1257 b) else decide (5 ≤ count1257 b)) else (if i < 1263 then decide (6 ≤ count1257 b) else (if i < 1264 then decide (1 ≤ count1263 b) else decide (2 ≤ count1263 b)))) else (if i < 1267 then (if i < 1266 then decide (3 ≤ count1263 b) else decide (4 ≤ count1263 b)) else (if i < 1268 then decide (5 ≤ count1263 b) else (if i < 1269 then decide (6 ≤ count1263 b) else decide (7 ≤ count1263 b))))) else (if i < 1275 then (if i < 1272 then (if i < 1271 then decide (1 ≤ count1270 b) else decide (2 ≤ count1270 b)) else (if i < 1273 then decide (1 ≤ count1272 b) else (if i < 1274 then decide (2 ≤ count1272 b) else decide (3 ≤ count1272 b)))) else (if i < 1278 then (if i < 1276 then decide (1 ≤ count1275 b) else (if i < 1277 then decide (2 ≤ count1275 b) else decide (1 ≤ count1277 b))) else (if i < 1279 then decide (2 ≤ count1277 b) else (if i < 1280 then decide (3 ≤ count1277 b) else decide (1 ≤ count1280 b))))))) else (if i < 1302 then (if i < 1291 then (if i < 1286 then (if i < 1283 then (if i < 1282 then decide (2 ≤ count1280 b) else decide (3 ≤ count1280 b)) else (if i < 1284 then decide (4 ≤ count1280 b) else (if i < 1285 then decide (5 ≤ count1280 b) else decide (6 ≤ count1280 b)))) else (if i < 1288 then (if i < 1287 then decide (1 ≤ count1286 b) else decide (2 ≤ count1286 b)) else (if i < 1289 then decide (1 ≤ count1288 b) else (if i < 1290 then decide (2 ≤ count1288 b) else decide (3 ≤ count1288 b))))) else (if i < 1296 then (if i < 1293 then (if i < 1292 then decide (1 ≤ count1291 b) else decide (2 ≤ count1291 b)) else (if i < 1294 then decide (1 ≤ count1293 b) else (if i < 1295 then decide (2 ≤ count1293 b) else decide (3 ≤ count1293 b)))) else (if i < 1299 then (if i < 1297 then decide (1 ≤ count1296 b) else (if i < 1298 then decide (2 ≤ count1296 b) else decide (3 ≤ count1296 b))) else (if i < 1300 then decide (4 ≤ count1296 b) else (if i < 1301 then decide (5 ≤ count1296 b) else decide (6 ≤ count1296 b)))))) else (if i < 1312 then (if i < 1307 then (if i < 1304 then (if i < 1303 then decide (1 ≤ count1302 b) else decide (2 ≤ count1302 b)) else (if i < 1305 then decide (3 ≤ count1302 b) else (if i < 1306 then decide (4 ≤ count1302 b) else decide (5 ≤ count1302 b)))) else (if i < 1309 then (if i < 1308 then decide (6 ≤ count1302 b) else decide (7 ≤ count1302 b)) else (if i < 1310 then decide (1 ≤ count1309 b) else (if i < 1311 then decide (2 ≤ count1309 b) else decide (3 ≤ count1309 b))))) else (if i < 1317 then (if i < 1314 then (if i < 1313 then decide (4 ≤ count1309 b) else decide (5 ≤ count1309 b)) else (if i < 1315 then decide (6 ≤ count1309 b) else (if i < 1316 then decide (7 ≤ count1309 b) else decide (1 ≤ count1316 b)))) else (if i < 1320 then (if i < 1318 then decide (2 ≤ count1316 b) else (if i < 1319 then decide (3 ≤ count1316 b) else decide (4 ≤ count1316 b))) else (if i < 1321 then decide (5 ≤ count1316 b) else (if i < 1322 then decide (6 ≤ count1316 b) else decide (7 ≤ count1316 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (135 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (136 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (137 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (138 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (140 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (148 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (149 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (151 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (154 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (155 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (159 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (193 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (199 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (200 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (201 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (205 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (214 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (218 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (220 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (222 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (296 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (327 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (342 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (346 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (348 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (350 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (390 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (392 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (393 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (397 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (406 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (410 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (412 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (414 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (422 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (424 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (428 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (430 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (486 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (487 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (488 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (502 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (506 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (508 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (510 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value1152 (q : Snake 81) : valuation q 1152 = decide (1 ≤ count1152 (baseVal q)) := rfl
theorem value1154 (q : Snake 81) : valuation q 1154 = decide (1 ≤ count1154 (baseVal q)) := rfl
theorem value1157 (q : Snake 81) : valuation q 1157 = decide (1 ≤ count1157 (baseVal q)) := rfl
theorem value1162 (q : Snake 81) : valuation q 1162 = decide (1 ≤ count1162 (baseVal q)) := rfl
theorem value1164 (q : Snake 81) : valuation q 1164 = decide (1 ≤ count1164 (baseVal q)) := rfl
theorem value1167 (q : Snake 81) : valuation q 1167 = decide (1 ≤ count1167 (baseVal q)) := rfl
theorem value1169 (q : Snake 81) : valuation q 1169 = decide (1 ≤ count1169 (baseVal q)) := rfl
theorem value1172 (q : Snake 81) : valuation q 1172 = decide (1 ≤ count1172 (baseVal q)) := rfl
theorem value1178 (q : Snake 81) : valuation q 1178 = decide (1 ≤ count1178 (baseVal q)) := rfl
theorem value1185 (q : Snake 81) : valuation q 1185 = decide (1 ≤ count1185 (baseVal q)) := rfl
theorem value1187 (q : Snake 81) : valuation q 1187 = decide (1 ≤ count1187 (baseVal q)) := rfl
theorem value1190 (q : Snake 81) : valuation q 1190 = decide (1 ≤ count1190 (baseVal q)) := rfl
theorem value1192 (q : Snake 81) : valuation q 1192 = decide (1 ≤ count1192 (baseVal q)) := rfl
theorem value1195 (q : Snake 81) : valuation q 1195 = decide (1 ≤ count1195 (baseVal q)) := rfl
theorem value1196 (q : Snake 81) : valuation q 1196 = decide (2 ≤ count1195 (baseVal q)) := rfl
theorem value1201 (q : Snake 81) : valuation q 1201 = decide (1 ≤ count1201 (baseVal q)) := rfl
theorem value1203 (q : Snake 81) : valuation q 1203 = decide (1 ≤ count1203 (baseVal q)) := rfl
theorem value1211 (q : Snake 81) : valuation q 1211 = decide (1 ≤ count1211 (baseVal q)) := rfl
theorem value1217 (q : Snake 81) : valuation q 1217 = decide (1 ≤ count1217 (baseVal q)) := rfl
theorem value1218 (q : Snake 81) : valuation q 1218 = decide (2 ≤ count1217 (baseVal q)) := rfl
theorem value1224 (q : Snake 81) : valuation q 1224 = decide (1 ≤ count1224 (baseVal q)) := rfl
theorem value1225 (q : Snake 81) : valuation q 1225 = decide (2 ≤ count1224 (baseVal q)) := rfl
theorem value1231 (q : Snake 81) : valuation q 1231 = decide (1 ≤ count1231 (baseVal q)) := rfl
theorem value1233 (q : Snake 81) : valuation q 1233 = decide (1 ≤ count1233 (baseVal q)) := rfl
theorem value1241 (q : Snake 81) : valuation q 1241 = decide (1 ≤ count1241 (baseVal q)) := rfl
theorem value1247 (q : Snake 81) : valuation q 1247 = decide (1 ≤ count1247 (baseVal q)) := rfl
theorem value1249 (q : Snake 81) : valuation q 1249 = decide (1 ≤ count1249 (baseVal q)) := rfl
theorem value1252 (q : Snake 81) : valuation q 1252 = decide (1 ≤ count1252 (baseVal q)) := rfl
theorem value1254 (q : Snake 81) : valuation q 1254 = decide (1 ≤ count1254 (baseVal q)) := rfl
theorem value1255 (q : Snake 81) : valuation q 1255 = decide (2 ≤ count1254 (baseVal q)) := rfl
theorem value1257 (q : Snake 81) : valuation q 1257 = decide (1 ≤ count1257 (baseVal q)) := rfl
theorem value1258 (q : Snake 81) : valuation q 1258 = decide (2 ≤ count1257 (baseVal q)) := rfl
theorem value1259 (q : Snake 81) : valuation q 1259 = decide (3 ≤ count1257 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (2 ≤ count1263 (baseVal q)) := rfl
theorem value1265 (q : Snake 81) : valuation q 1265 = decide (3 ≤ count1263 (baseVal q)) := rfl
theorem value1266 (q : Snake 81) : valuation q 1266 = decide (4 ≤ count1263 (baseVal q)) := rfl
theorem value1270 (q : Snake 81) : valuation q 1270 = decide (1 ≤ count1270 (baseVal q)) := rfl
theorem value1271 (q : Snake 81) : valuation q 1271 = decide (2 ≤ count1270 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (1 ≤ count1272 (baseVal q)) := rfl
theorem value1273 (q : Snake 81) : valuation q 1273 = decide (2 ≤ count1272 (baseVal q)) := rfl
theorem value1275 (q : Snake 81) : valuation q 1275 = decide (1 ≤ count1275 (baseVal q)) := rfl
theorem value1277 (q : Snake 81) : valuation q 1277 = decide (1 ≤ count1277 (baseVal q)) := rfl
theorem value1280 (q : Snake 81) : valuation q 1280 = decide (1 ≤ count1280 (baseVal q)) := rfl
theorem value1281 (q : Snake 81) : valuation q 1281 = decide (2 ≤ count1280 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (1 ≤ count1288 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (1 ≤ count1291 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (1 ≤ count1293 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (1 ≤ count1296 (baseVal q)) := rfl
theorem value1297 (q : Snake 81) : valuation q 1297 = decide (2 ≤ count1296 (baseVal q)) := rfl
theorem value1302 (q : Snake 81) : valuation q 1302 = decide (1 ≤ count1302 (baseVal q)) := rfl
theorem value1303 (q : Snake 81) : valuation q 1303 = decide (2 ≤ count1302 (baseVal q)) := rfl
theorem value1304 (q : Snake 81) : valuation q 1304 = decide (3 ≤ count1302 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (5 ≤ count1309 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (6 ≤ count1309 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (7 ≤ count1316 (baseVal q)) := rfl
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
theorem meaningNeg75 (b : Nat → Bool) : literal (valuationOf b) (-75) = decide (1 ≤ countLit b [-75]) := by
  change literal b (-75) = decide (1 ≤ countLit b [-75])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-75) <;> decide
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
theorem meaningNeg71 (b : Nat → Bool) : literal (valuationOf b) (-71) = decide (1 ≤ countLit b [-71]) := by
  change literal b (-71) = decide (1 ≤ countLit b [-71])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-71) <;> decide
theorem meaningNeg69 (b : Nat → Bool) : literal (valuationOf b) (-69) = decide (1 ≤ countLit b [-69]) := by
  change literal b (-69) = decide (1 ≤ countLit b [-69])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-69) <;> decide
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
theorem meaningNeg54 (b : Nat → Bool) : literal (valuationOf b) (-54) = decide (1 ≤ countLit b [-54]) := by
  change literal b (-54) = decide (1 ≤ countLit b [-54])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-54) <;> decide
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
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
theorem meaningNeg12 (b : Nat → Bool) : literal (valuationOf b) (-12) = decide (1 ≤ countLit b [-12]) := by
  change literal b (-12) = decide (1 ≤ countLit b [-12])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-12) <;> decide
theorem meaning1152 (b : Nat → Bool) : literal (valuationOf b) 1152 = decide (1 ≤ count1152 b) := rfl
theorem meaning1154 (b : Nat → Bool) : literal (valuationOf b) 1154 = decide (1 ≤ count1154 b) := rfl
theorem meaning1157 (b : Nat → Bool) : literal (valuationOf b) 1157 = decide (1 ≤ count1157 b) := rfl
theorem meaning1162 (b : Nat → Bool) : literal (valuationOf b) 1162 = decide (1 ≤ count1162 b) := rfl
theorem meaning1164 (b : Nat → Bool) : literal (valuationOf b) 1164 = decide (1 ≤ count1164 b) := rfl
theorem meaning1167 (b : Nat → Bool) : literal (valuationOf b) 1167 = decide (1 ≤ count1167 b) := rfl
theorem meaning1169 (b : Nat → Bool) : literal (valuationOf b) 1169 = decide (1 ≤ count1169 b) := rfl
theorem meaning1172 (b : Nat → Bool) : literal (valuationOf b) 1172 = decide (1 ≤ count1172 b) := rfl
theorem meaning1178 (b : Nat → Bool) : literal (valuationOf b) 1178 = decide (1 ≤ count1178 b) := rfl
theorem meaning1185 (b : Nat → Bool) : literal (valuationOf b) 1185 = decide (1 ≤ count1185 b) := rfl
theorem meaning1187 (b : Nat → Bool) : literal (valuationOf b) 1187 = decide (1 ≤ count1187 b) := rfl
theorem meaning1190 (b : Nat → Bool) : literal (valuationOf b) 1190 = decide (1 ≤ count1190 b) := rfl
theorem meaning1192 (b : Nat → Bool) : literal (valuationOf b) 1192 = decide (1 ≤ count1192 b) := rfl
theorem meaning1195 (b : Nat → Bool) : literal (valuationOf b) 1195 = decide (1 ≤ count1195 b) := rfl
theorem meaning1196 (b : Nat → Bool) : literal (valuationOf b) 1196 = decide (2 ≤ count1195 b) := rfl
theorem meaning1201 (b : Nat → Bool) : literal (valuationOf b) 1201 = decide (1 ≤ count1201 b) := rfl
theorem meaning1203 (b : Nat → Bool) : literal (valuationOf b) 1203 = decide (1 ≤ count1203 b) := rfl
theorem meaning1211 (b : Nat → Bool) : literal (valuationOf b) 1211 = decide (1 ≤ count1211 b) := rfl
theorem meaning1217 (b : Nat → Bool) : literal (valuationOf b) 1217 = decide (1 ≤ count1217 b) := rfl
theorem meaning1218 (b : Nat → Bool) : literal (valuationOf b) 1218 = decide (2 ≤ count1217 b) := rfl
theorem meaning1224 (b : Nat → Bool) : literal (valuationOf b) 1224 = decide (1 ≤ count1224 b) := rfl
theorem meaning1225 (b : Nat → Bool) : literal (valuationOf b) 1225 = decide (2 ≤ count1224 b) := rfl
theorem meaning1231 (b : Nat → Bool) : literal (valuationOf b) 1231 = decide (1 ≤ count1231 b) := rfl
theorem meaning1233 (b : Nat → Bool) : literal (valuationOf b) 1233 = decide (1 ≤ count1233 b) := rfl
theorem meaning1241 (b : Nat → Bool) : literal (valuationOf b) 1241 = decide (1 ≤ count1241 b) := rfl
theorem meaning1247 (b : Nat → Bool) : literal (valuationOf b) 1247 = decide (1 ≤ count1247 b) := rfl
theorem meaning1249 (b : Nat → Bool) : literal (valuationOf b) 1249 = decide (1 ≤ count1249 b) := rfl
theorem meaning1252 (b : Nat → Bool) : literal (valuationOf b) 1252 = decide (1 ≤ count1252 b) := rfl
theorem meaning1254 (b : Nat → Bool) : literal (valuationOf b) 1254 = decide (1 ≤ count1254 b) := rfl
theorem meaning1255 (b : Nat → Bool) : literal (valuationOf b) 1255 = decide (2 ≤ count1254 b) := rfl
theorem meaning1257 (b : Nat → Bool) : literal (valuationOf b) 1257 = decide (1 ≤ count1257 b) := rfl
theorem meaning1258 (b : Nat → Bool) : literal (valuationOf b) 1258 = decide (2 ≤ count1257 b) := rfl
theorem meaning1259 (b : Nat → Bool) : literal (valuationOf b) 1259 = decide (3 ≤ count1257 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (2 ≤ count1263 b) := rfl
theorem meaning1265 (b : Nat → Bool) : literal (valuationOf b) 1265 = decide (3 ≤ count1263 b) := rfl
theorem meaning1266 (b : Nat → Bool) : literal (valuationOf b) 1266 = decide (4 ≤ count1263 b) := rfl
theorem meaning1270 (b : Nat → Bool) : literal (valuationOf b) 1270 = decide (1 ≤ count1270 b) := rfl
theorem meaning1271 (b : Nat → Bool) : literal (valuationOf b) 1271 = decide (2 ≤ count1270 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (1 ≤ count1272 b) := rfl
theorem meaning1273 (b : Nat → Bool) : literal (valuationOf b) 1273 = decide (2 ≤ count1272 b) := rfl
theorem meaning1275 (b : Nat → Bool) : literal (valuationOf b) 1275 = decide (1 ≤ count1275 b) := rfl
theorem meaning1277 (b : Nat → Bool) : literal (valuationOf b) 1277 = decide (1 ≤ count1277 b) := rfl
theorem meaning1280 (b : Nat → Bool) : literal (valuationOf b) 1280 = decide (1 ≤ count1280 b) := rfl
theorem meaning1281 (b : Nat → Bool) : literal (valuationOf b) 1281 = decide (2 ≤ count1280 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (1 ≤ count1288 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (1 ≤ count1291 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (1 ≤ count1293 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (1 ≤ count1296 b) := rfl
theorem meaning1297 (b : Nat → Bool) : literal (valuationOf b) 1297 = decide (2 ≤ count1296 b) := rfl
theorem meaning1302 (b : Nat → Bool) : literal (valuationOf b) 1302 = decide (1 ≤ count1302 b) := rfl
theorem meaning1303 (b : Nat → Bool) : literal (valuationOf b) 1303 = decide (2 ≤ count1302 b) := rfl
theorem meaning1304 (b : Nat → Bool) : literal (valuationOf b) 1304 = decide (3 ≤ count1302 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (5 ≤ count1309 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (6 ≤ count1309 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (7 ≤ count1316 b) := rfl
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
end Snake9.Regrowth.E112118
