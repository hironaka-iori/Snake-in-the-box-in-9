import E112175Data
namespace Snake9.Regrowth.E112175
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 104 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 4 then decide (InPath q (6 : Vertex)) else (if i < 5 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (19 : Vertex)) else (if i < 8 then decide (InPath q (22 : Vertex)) else decide (InPath q (64 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (65 : Vertex)) else decide (InPath q (66 : Vertex))) else (if i < 12 then decide (InPath q (70 : Vertex)) else decide (InPath q (72 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (76 : Vertex)) else (if i < 15 then decide (InPath q (78 : Vertex)) else decide (InPath q (128 : Vertex)))) else (if i < 17 then decide (InPath q (130 : Vertex)) else (if i < 18 then decide (InPath q (132 : Vertex)) else decide (InPath q (134 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (135 : Vertex)) else (if i < 21 then decide (InPath q (136 : Vertex)) else decide (InPath q (137 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (138 : Vertex)) else decide (InPath q (140 : Vertex))) else (if i < 25 then decide (InPath q (142 : Vertex)) else decide (InPath q (148 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (149 : Vertex)) else (if i < 28 then decide (InPath q (151 : Vertex)) else decide (InPath q (153 : Vertex)))) else (if i < 30 then decide (InPath q (154 : Vertex)) else (if i < 31 then decide (InPath q (155 : Vertex)) else decide (InPath q (159 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (192 : Vertex)) else (if i < 34 then decide (InPath q (193 : Vertex)) else decide (InPath q (198 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex))) else (if i < 38 then decide (InPath q (201 : Vertex)) else decide (InPath q (205 : Vertex)))))) else (if i < 45 then (if i < 42 then (if i < 40 then decide (InPath q (207 : Vertex)) else (if i < 41 then decide (InPath q (209 : Vertex)) else decide (InPath q (210 : Vertex)))) else (if i < 43 then decide (InPath q (211 : Vertex)) else (if i < 44 then decide (InPath q (214 : Vertex)) else decide (InPath q (218 : Vertex))))) else (if i < 48 then (if i < 46 then decide (InPath q (220 : Vertex)) else (if i < 47 then decide (InPath q (221 : Vertex)) else decide (InPath q (222 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (288 : Vertex)) else decide (InPath q (289 : Vertex))) else (if i < 51 then decide (InPath q (296 : Vertex)) else decide (InPath q (305 : Vertex)))))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then decide (InPath q (306 : Vertex)) else (if i < 54 then decide (InPath q (307 : Vertex)) else decide (InPath q (310 : Vertex)))) else (if i < 56 then decide (InPath q (316 : Vertex)) else (if i < 57 then decide (InPath q (317 : Vertex)) else decide (InPath q (318 : Vertex))))) else (if i < 61 then (if i < 59 then decide (InPath q (320 : Vertex)) else (if i < 60 then decide (InPath q (321 : Vertex)) else decide (InPath q (326 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (327 : Vertex)) else decide (InPath q (328 : Vertex))) else (if i < 64 then decide (InPath q (329 : Vertex)) else decide (InPath q (333 : Vertex)))))) else (if i < 71 then (if i < 68 then (if i < 66 then decide (InPath q (335 : Vertex)) else (if i < 67 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex)))) else (if i < 69 then decide (InPath q (339 : Vertex)) else (if i < 70 then decide (InPath q (342 : Vertex)) else decide (InPath q (346 : Vertex))))) else (if i < 74 then (if i < 72 then decide (InPath q (348 : Vertex)) else (if i < 73 then decide (InPath q (349 : Vertex)) else decide (InPath q (350 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (390 : Vertex)) else decide (InPath q (392 : Vertex))) else (if i < 77 then decide (InPath q (393 : Vertex)) else decide (InPath q (397 : Vertex))))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then decide (InPath q (399 : Vertex)) else (if i < 80 then decide (InPath q (406 : Vertex)) else decide (InPath q (410 : Vertex)))) else (if i < 82 then decide (InPath q (412 : Vertex)) else (if i < 83 then decide (InPath q (413 : Vertex)) else decide (InPath q (414 : Vertex))))) else (if i < 87 then (if i < 85 then decide (InPath q (418 : Vertex)) else (if i < 86 then decide (InPath q (422 : Vertex)) else decide (InPath q (424 : Vertex)))) else (if i < 89 then (if i < 88 then decide (InPath q (428 : Vertex)) else decide (InPath q (430 : Vertex))) else (if i < 90 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex)))))) else (if i < 97 then (if i < 94 then (if i < 92 then decide (InPath q (486 : Vertex)) else (if i < 93 then decide (InPath q (487 : Vertex)) else decide (InPath q (488 : Vertex)))) else (if i < 95 then decide (InPath q (489 : Vertex)) else (if i < 96 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 100 then (if i < 98 then decide (InPath q (497 : Vertex)) else (if i < 99 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 103 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 156 then (if i < 130 then (if i < 117 then (if i < 110 then (if i < 107 then (if i < 105 then decide (InPath q (510 : Vertex)) else (if i < 106 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 108 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else (if i < 109 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex))))) else (if i < 113 then (if i < 111 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (64 : Vertex)))) else (if i < 115 then (if i < 114 then decide (BallClauseLogic.Endpoint q (65 : Vertex)) else decide (BallClauseLogic.Endpoint q (66 : Vertex))) else (if i < 116 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (72 : Vertex)))))) else (if i < 123 then (if i < 120 then (if i < 118 then decide (BallClauseLogic.Endpoint q (76 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (78 : Vertex)) else decide (BallClauseLogic.Endpoint q (128 : Vertex)))) else (if i < 121 then decide (BallClauseLogic.Endpoint q (130 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex))))) else (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (136 : Vertex)) else decide (BallClauseLogic.Endpoint q (137 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (140 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))))))) else (if i < 143 then (if i < 136 then (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (153 : Vertex)))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else (if i < 135 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex))))) else (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else decide (BallClauseLogic.Endpoint q (198 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (200 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex)))))) else (if i < 149 then (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else decide (BallClauseLogic.Endpoint q (210 : Vertex)))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex))))) else (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else decide (BallClauseLogic.Endpoint q (222 : Vertex)))) else (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else decide (BallClauseLogic.Endpoint q (289 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else decide (BallClauseLogic.Endpoint q (305 : Vertex)))))))) else (if i < 182 then (if i < 169 then (if i < 162 then (if i < 159 then (if i < 157 then decide (BallClauseLogic.Endpoint q (306 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (307 : Vertex)) else decide (BallClauseLogic.Endpoint q (310 : Vertex)))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (316 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex))))) else (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex)))) else (if i < 167 then (if i < 166 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (328 : Vertex))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else decide (BallClauseLogic.Endpoint q (333 : Vertex)))))) else (if i < 175 then (if i < 172 then (if i < 170 then decide (BallClauseLogic.Endpoint q (335 : Vertex)) else (if i < 171 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (338 : Vertex)))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (339 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (346 : Vertex))))) else (if i < 178 then (if i < 176 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (390 : Vertex)) else decide (BallClauseLogic.Endpoint q (392 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (393 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex))))))) else (if i < 195 then (if i < 188 then (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (399 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (410 : Vertex)))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex))))) else (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (422 : Vertex)) else decide (BallClauseLogic.Endpoint q (424 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else decide (BallClauseLogic.Endpoint q (430 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))))) else (if i < 202 then (if i < 198 then (if i < 196 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))) else (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 205 then (if i < 203 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else (if i < 204 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
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
def count315 (b : Nat → Bool) : Nat := countLit b [159, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169]
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
def count357 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
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
def count409 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count411 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count413 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count415 (b : Nat → Bool) : Nat := countLit b [1, 3, 4]
def count418 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count420 (b : Nat → Bool) : Nat := countLit b [5, 9, 10]
def count423 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10]
def count429 (b : Nat → Bool) : Nat := countLit b [14, 16]
def count431 (b : Nat → Bool) : Nat := countLit b [12, 14, 16]
def count434 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count436 (b : Nat → Bool) : Nat := countLit b [20, 24]
def count438 (b : Nat → Bool) : Nat := countLit b [17, 19, 20, 24]
def count442 (b : Nat → Bool) : Nat := countLit b [12, 14, 16, 17, 19, 20, 24]
def count449 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 12, 14, 16, 17, 19, 20, 24]
def count462 (b : Nat → Bool) : Nat := countLit b [28, 29]
def count464 (b : Nat → Bool) : Nat := countLit b [26, 28, 29]
def count467 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count469 (b : Nat → Bool) : Nat := countLit b [34, 37]
def count471 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37]
def count475 (b : Nat → Bool) : Nat := countLit b [26, 28, 29, 31, 32, 34, 37]
def count482 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count484 (b : Nat → Bool) : Nat := countLit b [39, 40, 41]
def count487 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count489 (b : Nat → Bool) : Nat := countLit b [48, 51]
def count491 (b : Nat → Bool) : Nat := countLit b [46, 47, 48, 51]
def count495 (b : Nat → Bool) : Nat := countLit b [39, 40, 41, 46, 47, 48, 51]
def count502 (b : Nat → Bool) : Nat := countLit b [26, 28, 29, 31, 32, 34, 37, 39, 40, 41, 46, 47, 48, 51]
def count516 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 12, 14, 16, 17, 19, 20, 24, 26, 28, 29, 31, 32, 34, 37, 39, 40, 41, 46, 47, 48, 51]
def count543 (b : Nat → Bool) : Nat := countLit b [56, 57]
def count545 (b : Nat → Bool) : Nat := countLit b [52, 56, 57]
def count548 (b : Nat → Bool) : Nat := countLit b [60, 63]
def count550 (b : Nat → Bool) : Nat := countLit b [58, 60, 63]
def count553 (b : Nat → Bool) : Nat := countLit b [52, 56, 57, 58, 60, 63]
def count559 (b : Nat → Bool) : Nat := countLit b [66, 67]
def count561 (b : Nat → Bool) : Nat := countLit b [65, 66, 67]
def count564 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count566 (b : Nat → Bool) : Nat := countLit b [74, 76]
def count568 (b : Nat → Bool) : Nat := countLit b [72, 73, 74, 76]
def count572 (b : Nat → Bool) : Nat := countLit b [65, 66, 67, 72, 73, 74, 76]
def count579 (b : Nat → Bool) : Nat := countLit b [52, 56, 57, 58, 60, 63, 65, 66, 67, 72, 73, 74, 76]
def count592 (b : Nat → Bool) : Nat := countLit b [82, 83]
def count594 (b : Nat → Bool) : Nat := countLit b [78, 82, 83]
def count597 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count599 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count601 (b : Nat → Bool) : Nat := countLit b [84, 86, 88, 89]
def count605 (b : Nat → Bool) : Nat := countLit b [78, 82, 83, 84, 86, 88, 89]
def count612 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count614 (b : Nat → Bool) : Nat := countLit b [91, 94, 96]
def count617 (b : Nat → Bool) : Nat := countLit b [97, 98]
def count619 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count621 (b : Nat → Bool) : Nat := countLit b [97, 98, 103, 104]
def count625 (b : Nat → Bool) : Nat := countLit b [91, 94, 96, 97, 98, 103, 104]
def count632 (b : Nat → Bool) : Nat := countLit b [78, 82, 83, 84, 86, 88, 89, 91, 94, 96, 97, 98, 103, 104]
def count646 (b : Nat → Bool) : Nat := countLit b [52, 56, 57, 58, 60, 63, 65, 66, 67, 72, 73, 74, 76, 78, 82, 83, 84, 86, 88, 89, 91, 94, 96, 97, 98, 103, 104]
def count673 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 12, 14, 16, 17, 19, 20, 24, 26, 28, 29, 31, 32, 34, 37, 39, 40, 41, 46, 47, 48, 51, 52, 56, 57, 58, 60, 63, 65, 66, 67, 72, 73, 74, 76, 78, 82, 83, 84, 86, 88, 89, 91, 94, 96, 97, 98, 103, 104]
def count715 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count717 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4]
def count720 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count722 (b : Nat → Bool) : Nat := countLit b [-5, -9, -10]
def count725 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10]
def count731 (b : Nat → Bool) : Nat := countLit b [-14, -16]
def count733 (b : Nat → Bool) : Nat := countLit b [-12, -14, -16]
def count736 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count738 (b : Nat → Bool) : Nat := countLit b [-20, -24]
def count740 (b : Nat → Bool) : Nat := countLit b [-17, -19, -20, -24]
def count744 (b : Nat → Bool) : Nat := countLit b [-12, -14, -16, -17, -19, -20, -24]
def count751 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]
def count764 (b : Nat → Bool) : Nat := countLit b [-28, -29]
def count766 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29]
def count769 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count771 (b : Nat → Bool) : Nat := countLit b [-34, -37]
def count773 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37]
def count777 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29, -31, -32, -34, -37]
def count784 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count786 (b : Nat → Bool) : Nat := countLit b [-39, -40, -41]
def count789 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count791 (b : Nat → Bool) : Nat := countLit b [-48, -51]
def count793 (b : Nat → Bool) : Nat := countLit b [-46, -47, -48, -51]
def count797 (b : Nat → Bool) : Nat := countLit b [-39, -40, -41, -46, -47, -48, -51]
def count804 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]
def count818 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]
def count832 (b : Nat → Bool) : Nat := countLit b [-56, -57]
def count834 (b : Nat → Bool) : Nat := countLit b [-52, -56, -57]
def count837 (b : Nat → Bool) : Nat := countLit b [-60, -63]
def count839 (b : Nat → Bool) : Nat := countLit b [-58, -60, -63]
def count842 (b : Nat → Bool) : Nat := countLit b [-52, -56, -57, -58, -60, -63]
def count848 (b : Nat → Bool) : Nat := countLit b [-66, -67]
def count850 (b : Nat → Bool) : Nat := countLit b [-65, -66, -67]
def count853 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count855 (b : Nat → Bool) : Nat := countLit b [-74, -76]
def count857 (b : Nat → Bool) : Nat := countLit b [-72, -73, -74, -76]
def count861 (b : Nat → Bool) : Nat := countLit b [-65, -66, -67, -72, -73, -74, -76]
def count868 (b : Nat → Bool) : Nat := countLit b [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76]
def count881 (b : Nat → Bool) : Nat := countLit b [-82, -83]
def count883 (b : Nat → Bool) : Nat := countLit b [-78, -82, -83]
def count886 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count888 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count890 (b : Nat → Bool) : Nat := countLit b [-84, -86, -88, -89]
def count894 (b : Nat → Bool) : Nat := countLit b [-78, -82, -83, -84, -86, -88, -89]
def count901 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count903 (b : Nat → Bool) : Nat := countLit b [-91, -94, -96]
def count906 (b : Nat → Bool) : Nat := countLit b [-97, -98]
def count908 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count910 (b : Nat → Bool) : Nat := countLit b [-97, -98, -103, -104]
def count914 (b : Nat → Bool) : Nat := countLit b [-91, -94, -96, -97, -98, -103, -104]
def count921 (b : Nat → Bool) : Nat := countLit b [-78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]
def count935 (b : Nat → Bool) : Nat := countLit b [-52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]
def count949 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24, -26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51, -52, -56, -57, -58, -60, -63, -65, -66, -67, -72, -73, -74, -76, -78, -82, -83, -84, -86, -88, -89, -91, -94, -96, -97, -98, -103, -104]
def count963 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count965 (b : Nat → Bool) : Nat := countLit b [2, 6, 7]
def count968 (b : Nat → Bool) : Nat := countLit b [11, 13]
def count970 (b : Nat → Bool) : Nat := countLit b [8, 11, 13]
def count973 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13]
def count979 (b : Nat → Bool) : Nat := countLit b [18, 21]
def count981 (b : Nat → Bool) : Nat := countLit b [15, 18, 21]
def count984 (b : Nat → Bool) : Nat := countLit b [23, 25]
def count986 (b : Nat → Bool) : Nat := countLit b [22, 23, 25]
def count989 (b : Nat → Bool) : Nat := countLit b [15, 18, 21, 22, 23, 25]
def count995 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13, 15, 18, 21, 22, 23, 25]
def count1007 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count1009 (b : Nat → Bool) : Nat := countLit b [27, 30, 33]
def count1012 (b : Nat → Bool) : Nat := countLit b [36, 38]
def count1014 (b : Nat → Bool) : Nat := countLit b [35, 36, 38]
def count1017 (b : Nat → Bool) : Nat := countLit b [27, 30, 33, 35, 36, 38]
def count1023 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count1025 (b : Nat → Bool) : Nat := countLit b [42, 43, 44]
def count1028 (b : Nat → Bool) : Nat := countLit b [45, 49]
def count1030 (b : Nat → Bool) : Nat := countLit b [50, 53]
def count1032 (b : Nat → Bool) : Nat := countLit b [45, 49, 50, 53]
def count1036 (b : Nat → Bool) : Nat := countLit b [42, 43, 44, 45, 49, 50, 53]
def count1043 (b : Nat → Bool) : Nat := countLit b [27, 30, 33, 35, 36, 38, 42, 43, 44, 45, 49, 50, 53]
def count1056 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13, 15, 18, 21, 22, 23, 25, 27, 30, 33, 35, 36, 38, 42, 43, 44, 45, 49, 50, 53]
def count1081 (b : Nat → Bool) : Nat := countLit b [55, 59]
def count1083 (b : Nat → Bool) : Nat := countLit b [54, 55, 59]
def count1086 (b : Nat → Bool) : Nat := countLit b [62, 64]
def count1088 (b : Nat → Bool) : Nat := countLit b [61, 62, 64]
def count1091 (b : Nat → Bool) : Nat := countLit b [54, 55, 59, 61, 62, 64]
def count1097 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count1099 (b : Nat → Bool) : Nat := countLit b [68, 69, 70]
def count1102 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count1104 (b : Nat → Bool) : Nat := countLit b [71, 75, 77]
def count1107 (b : Nat → Bool) : Nat := countLit b [68, 69, 70, 71, 75, 77]
def count1113 (b : Nat → Bool) : Nat := countLit b [54, 55, 59, 61, 62, 64, 68, 69, 70, 71, 75, 77]
def count1125 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count1127 (b : Nat → Bool) : Nat := countLit b [79, 80, 81]
def count1130 (b : Nat → Bool) : Nat := countLit b [87, 90]
def count1132 (b : Nat → Bool) : Nat := countLit b [85, 87, 90]
def count1135 (b : Nat → Bool) : Nat := countLit b [79, 80, 81, 85, 87, 90]
def count1141 (b : Nat → Bool) : Nat := countLit b [93, 95]
def count1143 (b : Nat → Bool) : Nat := countLit b [92, 93, 95]
def count1146 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count1148 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count1150 (b : Nat → Bool) : Nat := countLit b [99, 100, 101, 102]
def count1154 (b : Nat → Bool) : Nat := countLit b [92, 93, 95, 99, 100, 101, 102]
def count1161 (b : Nat → Bool) : Nat := countLit b [79, 80, 81, 85, 87, 90, 92, 93, 95, 99, 100, 101, 102]
def count1174 (b : Nat → Bool) : Nat := countLit b [54, 55, 59, 61, 62, 64, 68, 69, 70, 71, 75, 77, 79, 80, 81, 85, 87, 90, 92, 93, 95, 99, 100, 101, 102]
def count1199 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13, 15, 18, 21, 22, 23, 25, 27, 30, 33, 35, 36, 38, 42, 43, 44, 45, 49, 50, 53, 54, 55, 59, 61, 62, 64, 68, 69, 70, 71, 75, 77, 79, 80, 81, 85, 87, 90, 92, 93, 95, 99, 100, 101, 102]
def count1241 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count1243 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7]
def count1246 (b : Nat → Bool) : Nat := countLit b [-11, -13]
def count1248 (b : Nat → Bool) : Nat := countLit b [-8, -11, -13]
def count1251 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13]
def count1257 (b : Nat → Bool) : Nat := countLit b [-18, -21]
def count1259 (b : Nat → Bool) : Nat := countLit b [-15, -18, -21]
def count1262 (b : Nat → Bool) : Nat := countLit b [-23, -25]
def count1264 (b : Nat → Bool) : Nat := countLit b [-22, -23, -25]
def count1267 (b : Nat → Bool) : Nat := countLit b [-15, -18, -21, -22, -23, -25]
def count1273 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25]
def count1283 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count1285 (b : Nat → Bool) : Nat := countLit b [-27, -30, -33]
def count1288 (b : Nat → Bool) : Nat := countLit b [-36, -38]
def count1290 (b : Nat → Bool) : Nat := countLit b [-35, -36, -38]
def count1293 (b : Nat → Bool) : Nat := countLit b [-27, -30, -33, -35, -36, -38]
def count1299 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count1301 (b : Nat → Bool) : Nat := countLit b [-42, -43, -44]
def count1304 (b : Nat → Bool) : Nat := countLit b [-45, -49]
def count1306 (b : Nat → Bool) : Nat := countLit b [-50, -53]
def count1308 (b : Nat → Bool) : Nat := countLit b [-45, -49, -50, -53]
def count1312 (b : Nat → Bool) : Nat := countLit b [-42, -43, -44, -45, -49, -50, -53]
def count1319 (b : Nat → Bool) : Nat := countLit b [-27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]
def count1329 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53]
def count1339 (b : Nat → Bool) : Nat := countLit b [-55, -59]
def count1341 (b : Nat → Bool) : Nat := countLit b [-54, -55, -59]
def count1344 (b : Nat → Bool) : Nat := countLit b [-62, -64]
def count1346 (b : Nat → Bool) : Nat := countLit b [-61, -62, -64]
def count1349 (b : Nat → Bool) : Nat := countLit b [-54, -55, -59, -61, -62, -64]
def count1355 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count1357 (b : Nat → Bool) : Nat := countLit b [-68, -69, -70]
def count1360 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count1362 (b : Nat → Bool) : Nat := countLit b [-71, -75, -77]
def count1365 (b : Nat → Bool) : Nat := countLit b [-68, -69, -70, -71, -75, -77]
def count1371 (b : Nat → Bool) : Nat := countLit b [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]
def count1381 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1383 (b : Nat → Bool) : Nat := countLit b [-79, -80, -81]
def count1386 (b : Nat → Bool) : Nat := countLit b [-87, -90]
def count1388 (b : Nat → Bool) : Nat := countLit b [-85, -87, -90]
def count1391 (b : Nat → Bool) : Nat := countLit b [-79, -80, -81, -85, -87, -90]
def count1397 (b : Nat → Bool) : Nat := countLit b [-93, -95]
def count1399 (b : Nat → Bool) : Nat := countLit b [-92, -93, -95]
def count1402 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1404 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count1406 (b : Nat → Bool) : Nat := countLit b [-99, -100, -101, -102]
def count1410 (b : Nat → Bool) : Nat := countLit b [-92, -93, -95, -99, -100, -101, -102]
def count1417 (b : Nat → Bool) : Nat := countLit b [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]
def count1427 (b : Nat → Bool) : Nat := countLit b [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]
def count1437 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13, -15, -18, -21, -22, -23, -25, -27, -30, -33, -35, -36, -38, -42, -43, -44, -45, -49, -50, -53, -54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77, -79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 723 then (if i < 361 then (if i < 180 then (if i < 90 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 16 then (if i < 13 then (if i < 12 then b 11 else b 12) else (if i < 14 then b 13 else (if i < 15 then b 14 else b 15))) else (if i < 19 then (if i < 17 then b 16 else (if i < 18 then b 17 else b 18)) else (if i < 20 then b 19 else (if i < 21 then b 20 else b 21))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else (if i < 26 then b 25 else b 26))) else (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)))) else (if i < 39 then (if i < 36 then (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)) else (if i < 37 then b 36 else (if i < 38 then b 37 else b 38))) else (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)))))) else (if i < 67 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else (if i < 49 then b 48 else b 49))) else (if i < 53 then (if i < 51 then b 50 else (if i < 52 then b 51 else b 52)) else (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)))) else (if i < 61 then (if i < 58 then (if i < 57 then b 56 else b 57) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60))) else (if i < 64 then (if i < 62 then b 61 else (if i < 63 then b 62 else b 63)) else (if i < 65 then b 64 else (if i < 66 then b 65 else b 66))))) else (if i < 78 then (if i < 72 then (if i < 69 then (if i < 68 then b 67 else b 68) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))) else (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)))) else (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))))))) else (if i < 135 then (if i < 112 then (if i < 101 then (if i < 95 then (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))) else (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)))) else (if i < 106 then (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else (if i < 105 then b 104 else b 105))) else (if i < 109 then (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111))))) else (if i < 123 then (if i < 117 then (if i < 114 then (if i < 113 then b 112 else b 113) else (if i < 115 then b 114 else (if i < 116 then b 115 else b 116))) else (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)))) else (if i < 129 then (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 127 then b 126 else (if i < 128 then b 127 else b 128))) else (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)))))) else (if i < 157 then (if i < 146 then (if i < 140 then (if i < 137 then (if i < 136 then b 135 else b 136) else (if i < 138 then b 137 else (if i < 139 then b 138 else b 139))) else (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)))) else (if i < 151 then (if i < 148 then (if i < 147 then b 146 else b 147) else (if i < 149 then b 148 else (if i < 150 then b 149 else b 150))) else (if i < 154 then (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)) else (if i < 155 then b 154 else (if i < 156 then b 155 else b 156))))) else (if i < 168 then (if i < 162 then (if i < 159 then (if i < 158 then b 157 else b 158) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)))) else (if i < 174 then (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 172 then b 171 else (if i < 173 then b 172 else b 173))) else (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)))))))) else (if i < 270 then (if i < 225 then (if i < 202 then (if i < 191 then (if i < 185 then (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else (if i < 184 then b 183 else b 184))) else (if i < 188 then (if i < 186 then b 185 else (if i < 187 then b 186 else b 187)) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)))) else (if i < 196 then (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else (if i < 195 then b 194 else b 195))) else (if i < 199 then (if i < 197 then b 196 else (if i < 198 then b 197 else b 198)) else (if i < 200 then b 199 else (if i < 201 then b 200 else b 201))))) else (if i < 213 then (if i < 207 then (if i < 204 then (if i < 203 then b 202 else b 203) else (if i < 205 then b 204 else (if i < 206 then b 205 else b 206))) else (if i < 210 then (if i < 208 then b 207 else (if i < 209 then b 208 else decide (1 ≤ count209 b))) else (if i < 211 then decide (2 ≤ count209 b) else (if i < 212 then decide (1 ≤ count211 b) else decide (2 ≤ count211 b))))) else (if i < 219 then (if i < 216 then (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))) else (if i < 217 then decide (2 ≤ count215 b) else (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b)))) else (if i < 222 then (if i < 220 then decide (1 ≤ count219 b) else (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b))) else (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b))))))) else (if i < 247 then (if i < 236 then (if i < 230 then (if i < 227 then (if i < 226 then decide (1 ≤ count225 b) else decide (2 ≤ count225 b)) else (if i < 228 then decide (1 ≤ count227 b) else (if i < 229 then decide (2 ≤ count227 b) else decide (1 ≤ count229 b)))) else (if i < 233 then (if i < 231 then decide (2 ≤ count229 b) else (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b))) else (if i < 234 then decide (1 ≤ count233 b) else (if i < 235 then decide (2 ≤ count233 b) else decide (1 ≤ count235 b))))) else (if i < 241 then (if i < 238 then (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b)) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))) else (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 245 then decide (2 ≤ count243 b) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)))))) else (if i < 258 then (if i < 252 then (if i < 249 then (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)))) else (if i < 255 then (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))) else (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))))) else (if i < 264 then (if i < 261 then (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)))) else (if i < 267 then (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))) else (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)))))))) else (if i < 315 then (if i < 292 then (if i < 281 then (if i < 275 then (if i < 272 then (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b)) else (if i < 273 then decide (2 ≤ count271 b) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b)))) else (if i < 278 then (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b))) else (if i < 279 then decide (2 ≤ count277 b) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b))))) else (if i < 286 then (if i < 283 then (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)) else (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)))) else (if i < 289 then (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))) else (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)))))) else (if i < 303 then (if i < 297 then (if i < 294 then (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b)) else (if i < 295 then decide (2 ≤ count293 b) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b)))) else (if i < 300 then (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))) else (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b))))) else (if i < 309 then (if i < 306 then (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b))) else (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))) else (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))))))) else (if i < 338 then (if i < 326 then (if i < 320 then (if i < 317 then (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b)) else (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))) else (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))))) else (if i < 332 then (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 335 then (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)))))) else (if i < 349 then (if i < 343 then (if i < 340 then (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)) else (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))) else (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 347 then decide (2 ≤ count345 b) else (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b))))) else (if i < 355 then (if i < 352 then (if i < 350 then decide (1 ≤ count349 b) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b))) else (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)))) else (if i < 358 then (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b))) else (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))))))))) else (if i < 542 then (if i < 451 then (if i < 406 then (if i < 383 then (if i < 372 then (if i < 366 then (if i < 363 then (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))) else (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b))))) else (if i < 377 then (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)))) else (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))))) else (if i < 394 then (if i < 388 then (if i < 385 then (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)))) else (if i < 391 then (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b))) else (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))))) else (if i < 400 then (if i < 397 then (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))) else (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))) else (if i < 403 then (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))) else (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))))))) else (if i < 428 then (if i < 417 then (if i < 411 then (if i < 408 then (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b)) else (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)))) else (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 415 then decide (2 ≤ count413 b) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b))))) else (if i < 422 then (if i < 419 then (if i < 418 then decide (3 ≤ count415 b) else decide (1 ≤ count418 b)) else (if i < 420 then decide (2 ≤ count418 b) else (if i < 421 then decide (1 ≤ count420 b) else decide (2 ≤ count420 b)))) else (if i < 425 then (if i < 423 then decide (3 ≤ count420 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 426 then decide (3 ≤ count423 b) else (if i < 427 then decide (4 ≤ count423 b) else decide (5 ≤ count423 b)))))) else (if i < 439 then (if i < 433 then (if i < 430 then (if i < 429 then decide (6 ≤ count423 b) else decide (1 ≤ count429 b)) else (if i < 431 then decide (2 ≤ count429 b) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)))) else (if i < 436 then (if i < 434 then decide (3 ≤ count431 b) else (if i < 435 then decide (1 ≤ count434 b) else decide (2 ≤ count434 b))) else (if i < 437 then decide (1 ≤ count436 b) else (if i < 438 then decide (2 ≤ count436 b) else decide (1 ≤ count438 b))))) else (if i < 445 then (if i < 442 then (if i < 440 then decide (2 ≤ count438 b) else (if i < 441 then decide (3 ≤ count438 b) else decide (4 ≤ count438 b))) else (if i < 443 then decide (1 ≤ count442 b) else (if i < 444 then decide (2 ≤ count442 b) else decide (3 ≤ count442 b)))) else (if i < 448 then (if i < 446 then decide (4 ≤ count442 b) else (if i < 447 then decide (5 ≤ count442 b) else decide (6 ≤ count442 b))) else (if i < 449 then decide (7 ≤ count442 b) else (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)))))))) else (if i < 496 then (if i < 473 then (if i < 462 then (if i < 456 then (if i < 453 then (if i < 452 then decide (3 ≤ count449 b) else decide (4 ≤ count449 b)) else (if i < 454 then decide (5 ≤ count449 b) else (if i < 455 then decide (6 ≤ count449 b) else decide (7 ≤ count449 b)))) else (if i < 459 then (if i < 457 then decide (8 ≤ count449 b) else (if i < 458 then decide (9 ≤ count449 b) else decide (10 ≤ count449 b))) else (if i < 460 then decide (11 ≤ count449 b) else (if i < 461 then decide (12 ≤ count449 b) else decide (13 ≤ count449 b))))) else (if i < 467 then (if i < 464 then (if i < 463 then decide (1 ≤ count462 b) else decide (2 ≤ count462 b)) else (if i < 465 then decide (1 ≤ count464 b) else (if i < 466 then decide (2 ≤ count464 b) else decide (3 ≤ count464 b)))) else (if i < 470 then (if i < 468 then decide (1 ≤ count467 b) else (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b))) else (if i < 471 then decide (2 ≤ count469 b) else (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b)))))) else (if i < 484 then (if i < 478 then (if i < 475 then (if i < 474 then decide (3 ≤ count471 b) else decide (4 ≤ count471 b)) else (if i < 476 then decide (1 ≤ count475 b) else (if i < 477 then decide (2 ≤ count475 b) else decide (3 ≤ count475 b)))) else (if i < 481 then (if i < 479 then decide (4 ≤ count475 b) else (if i < 480 then decide (5 ≤ count475 b) else decide (6 ≤ count475 b))) else (if i < 482 then decide (7 ≤ count475 b) else (if i < 483 then decide (1 ≤ count482 b) else decide (2 ≤ count482 b))))) else (if i < 490 then (if i < 487 then (if i < 485 then decide (1 ≤ count484 b) else (if i < 486 then decide (2 ≤ count484 b) else decide (3 ≤ count484 b))) else (if i < 488 then decide (1 ≤ count487 b) else (if i < 489 then decide (2 ≤ count487 b) else decide (1 ≤ count489 b)))) else (if i < 493 then (if i < 491 then decide (2 ≤ count489 b) else (if i < 492 then decide (1 ≤ count491 b) else decide (2 ≤ count491 b))) else (if i < 494 then decide (3 ≤ count491 b) else (if i < 495 then decide (4 ≤ count491 b) else decide (1 ≤ count495 b))))))) else (if i < 519 then (if i < 507 then (if i < 501 then (if i < 498 then (if i < 497 then decide (2 ≤ count495 b) else decide (3 ≤ count495 b)) else (if i < 499 then decide (4 ≤ count495 b) else (if i < 500 then decide (5 ≤ count495 b) else decide (6 ≤ count495 b)))) else (if i < 504 then (if i < 502 then decide (7 ≤ count495 b) else (if i < 503 then decide (1 ≤ count502 b) else decide (2 ≤ count502 b))) else (if i < 505 then decide (3 ≤ count502 b) else (if i < 506 then decide (4 ≤ count502 b) else decide (5 ≤ count502 b))))) else (if i < 513 then (if i < 510 then (if i < 508 then decide (6 ≤ count502 b) else (if i < 509 then decide (7 ≤ count502 b) else decide (8 ≤ count502 b))) else (if i < 511 then decide (9 ≤ count502 b) else (if i < 512 then decide (10 ≤ count502 b) else decide (11 ≤ count502 b)))) else (if i < 516 then (if i < 514 then decide (12 ≤ count502 b) else (if i < 515 then decide (13 ≤ count502 b) else decide (14 ≤ count502 b))) else (if i < 517 then decide (1 ≤ count516 b) else (if i < 518 then decide (2 ≤ count516 b) else decide (3 ≤ count516 b)))))) else (if i < 530 then (if i < 524 then (if i < 521 then (if i < 520 then decide (4 ≤ count516 b) else decide (5 ≤ count516 b)) else (if i < 522 then decide (6 ≤ count516 b) else (if i < 523 then decide (7 ≤ count516 b) else decide (8 ≤ count516 b)))) else (if i < 527 then (if i < 525 then decide (9 ≤ count516 b) else (if i < 526 then decide (10 ≤ count516 b) else decide (11 ≤ count516 b))) else (if i < 528 then decide (12 ≤ count516 b) else (if i < 529 then decide (13 ≤ count516 b) else decide (14 ≤ count516 b))))) else (if i < 536 then (if i < 533 then (if i < 531 then decide (15 ≤ count516 b) else (if i < 532 then decide (16 ≤ count516 b) else decide (17 ≤ count516 b))) else (if i < 534 then decide (18 ≤ count516 b) else (if i < 535 then decide (19 ≤ count516 b) else decide (20 ≤ count516 b)))) else (if i < 539 then (if i < 537 then decide (21 ≤ count516 b) else (if i < 538 then decide (22 ≤ count516 b) else decide (23 ≤ count516 b))) else (if i < 540 then decide (24 ≤ count516 b) else (if i < 541 then decide (25 ≤ count516 b) else decide (26 ≤ count516 b))))))))) else (if i < 632 then (if i < 587 then (if i < 564 then (if i < 553 then (if i < 547 then (if i < 544 then (if i < 543 then decide (27 ≤ count516 b) else decide (1 ≤ count543 b)) else (if i < 545 then decide (2 ≤ count543 b) else (if i < 546 then decide (1 ≤ count545 b) else decide (2 ≤ count545 b)))) else (if i < 550 then (if i < 548 then decide (3 ≤ count545 b) else (if i < 549 then decide (1 ≤ count548 b) else decide (2 ≤ count548 b))) else (if i < 551 then decide (1 ≤ count550 b) else (if i < 552 then decide (2 ≤ count550 b) else decide (3 ≤ count550 b))))) else (if i < 558 then (if i < 555 then (if i < 554 then decide (1 ≤ count553 b) else decide (2 ≤ count553 b)) else (if i < 556 then decide (3 ≤ count553 b) else (if i < 557 then decide (4 ≤ count553 b) else decide (5 ≤ count553 b)))) else (if i < 561 then (if i < 559 then decide (6 ≤ count553 b) else (if i < 560 then decide (1 ≤ count559 b) else decide (2 ≤ count559 b))) else (if i < 562 then decide (1 ≤ count561 b) else (if i < 563 then decide (2 ≤ count561 b) else decide (3 ≤ count561 b)))))) else (if i < 575 then (if i < 569 then (if i < 566 then (if i < 565 then decide (1 ≤ count564 b) else decide (2 ≤ count564 b)) else (if i < 567 then decide (1 ≤ count566 b) else (if i < 568 then decide (2 ≤ count566 b) else decide (1 ≤ count568 b)))) else (if i < 572 then (if i < 570 then decide (2 ≤ count568 b) else (if i < 571 then decide (3 ≤ count568 b) else decide (4 ≤ count568 b))) else (if i < 573 then decide (1 ≤ count572 b) else (if i < 574 then decide (2 ≤ count572 b) else decide (3 ≤ count572 b))))) else (if i < 581 then (if i < 578 then (if i < 576 then decide (4 ≤ count572 b) else (if i < 577 then decide (5 ≤ count572 b) else decide (6 ≤ count572 b))) else (if i < 579 then decide (7 ≤ count572 b) else (if i < 580 then decide (1 ≤ count579 b) else decide (2 ≤ count579 b)))) else (if i < 584 then (if i < 582 then decide (3 ≤ count579 b) else (if i < 583 then decide (4 ≤ count579 b) else decide (5 ≤ count579 b))) else (if i < 585 then decide (6 ≤ count579 b) else (if i < 586 then decide (7 ≤ count579 b) else decide (8 ≤ count579 b))))))) else (if i < 609 then (if i < 598 then (if i < 592 then (if i < 589 then (if i < 588 then decide (9 ≤ count579 b) else decide (10 ≤ count579 b)) else (if i < 590 then decide (11 ≤ count579 b) else (if i < 591 then decide (12 ≤ count579 b) else decide (13 ≤ count579 b)))) else (if i < 595 then (if i < 593 then decide (1 ≤ count592 b) else (if i < 594 then decide (2 ≤ count592 b) else decide (1 ≤ count594 b))) else (if i < 596 then decide (2 ≤ count594 b) else (if i < 597 then decide (3 ≤ count594 b) else decide (1 ≤ count597 b))))) else (if i < 603 then (if i < 600 then (if i < 599 then decide (2 ≤ count597 b) else decide (1 ≤ count599 b)) else (if i < 601 then decide (2 ≤ count599 b) else (if i < 602 then decide (1 ≤ count601 b) else decide (2 ≤ count601 b)))) else (if i < 606 then (if i < 604 then decide (3 ≤ count601 b) else (if i < 605 then decide (4 ≤ count601 b) else decide (1 ≤ count605 b))) else (if i < 607 then decide (2 ≤ count605 b) else (if i < 608 then decide (3 ≤ count605 b) else decide (4 ≤ count605 b)))))) else (if i < 620 then (if i < 614 then (if i < 611 then (if i < 610 then decide (5 ≤ count605 b) else decide (6 ≤ count605 b)) else (if i < 612 then decide (7 ≤ count605 b) else (if i < 613 then decide (1 ≤ count612 b) else decide (2 ≤ count612 b)))) else (if i < 617 then (if i < 615 then decide (1 ≤ count614 b) else (if i < 616 then decide (2 ≤ count614 b) else decide (3 ≤ count614 b))) else (if i < 618 then decide (1 ≤ count617 b) else (if i < 619 then decide (2 ≤ count617 b) else decide (1 ≤ count619 b))))) else (if i < 626 then (if i < 623 then (if i < 621 then decide (2 ≤ count619 b) else (if i < 622 then decide (1 ≤ count621 b) else decide (2 ≤ count621 b))) else (if i < 624 then decide (3 ≤ count621 b) else (if i < 625 then decide (4 ≤ count621 b) else decide (1 ≤ count625 b)))) else (if i < 629 then (if i < 627 then decide (2 ≤ count625 b) else (if i < 628 then decide (3 ≤ count625 b) else decide (4 ≤ count625 b))) else (if i < 630 then decide (5 ≤ count625 b) else (if i < 631 then decide (6 ≤ count625 b) else decide (7 ≤ count625 b)))))))) else (if i < 677 then (if i < 654 then (if i < 643 then (if i < 637 then (if i < 634 then (if i < 633 then decide (1 ≤ count632 b) else decide (2 ≤ count632 b)) else (if i < 635 then decide (3 ≤ count632 b) else (if i < 636 then decide (4 ≤ count632 b) else decide (5 ≤ count632 b)))) else (if i < 640 then (if i < 638 then decide (6 ≤ count632 b) else (if i < 639 then decide (7 ≤ count632 b) else decide (8 ≤ count632 b))) else (if i < 641 then decide (9 ≤ count632 b) else (if i < 642 then decide (10 ≤ count632 b) else decide (11 ≤ count632 b))))) else (if i < 648 then (if i < 645 then (if i < 644 then decide (12 ≤ count632 b) else decide (13 ≤ count632 b)) else (if i < 646 then decide (14 ≤ count632 b) else (if i < 647 then decide (1 ≤ count646 b) else decide (2 ≤ count646 b)))) else (if i < 651 then (if i < 649 then decide (3 ≤ count646 b) else (if i < 650 then decide (4 ≤ count646 b) else decide (5 ≤ count646 b))) else (if i < 652 then decide (6 ≤ count646 b) else (if i < 653 then decide (7 ≤ count646 b) else decide (8 ≤ count646 b)))))) else (if i < 665 then (if i < 659 then (if i < 656 then (if i < 655 then decide (9 ≤ count646 b) else decide (10 ≤ count646 b)) else (if i < 657 then decide (11 ≤ count646 b) else (if i < 658 then decide (12 ≤ count646 b) else decide (13 ≤ count646 b)))) else (if i < 662 then (if i < 660 then decide (14 ≤ count646 b) else (if i < 661 then decide (15 ≤ count646 b) else decide (16 ≤ count646 b))) else (if i < 663 then decide (17 ≤ count646 b) else (if i < 664 then decide (18 ≤ count646 b) else decide (19 ≤ count646 b))))) else (if i < 671 then (if i < 668 then (if i < 666 then decide (20 ≤ count646 b) else (if i < 667 then decide (21 ≤ count646 b) else decide (22 ≤ count646 b))) else (if i < 669 then decide (23 ≤ count646 b) else (if i < 670 then decide (24 ≤ count646 b) else decide (25 ≤ count646 b)))) else (if i < 674 then (if i < 672 then decide (26 ≤ count646 b) else (if i < 673 then decide (27 ≤ count646 b) else decide (1 ≤ count673 b))) else (if i < 675 then decide (2 ≤ count673 b) else (if i < 676 then decide (3 ≤ count673 b) else decide (4 ≤ count673 b))))))) else (if i < 700 then (if i < 688 then (if i < 682 then (if i < 679 then (if i < 678 then decide (5 ≤ count673 b) else decide (6 ≤ count673 b)) else (if i < 680 then decide (7 ≤ count673 b) else (if i < 681 then decide (8 ≤ count673 b) else decide (9 ≤ count673 b)))) else (if i < 685 then (if i < 683 then decide (10 ≤ count673 b) else (if i < 684 then decide (11 ≤ count673 b) else decide (12 ≤ count673 b))) else (if i < 686 then decide (13 ≤ count673 b) else (if i < 687 then decide (14 ≤ count673 b) else decide (15 ≤ count673 b))))) else (if i < 694 then (if i < 691 then (if i < 689 then decide (16 ≤ count673 b) else (if i < 690 then decide (17 ≤ count673 b) else decide (18 ≤ count673 b))) else (if i < 692 then decide (19 ≤ count673 b) else (if i < 693 then decide (20 ≤ count673 b) else decide (21 ≤ count673 b)))) else (if i < 697 then (if i < 695 then decide (22 ≤ count673 b) else (if i < 696 then decide (23 ≤ count673 b) else decide (24 ≤ count673 b))) else (if i < 698 then decide (25 ≤ count673 b) else (if i < 699 then decide (26 ≤ count673 b) else decide (27 ≤ count673 b)))))) else (if i < 711 then (if i < 705 then (if i < 702 then (if i < 701 then decide (28 ≤ count673 b) else decide (29 ≤ count673 b)) else (if i < 703 then decide (30 ≤ count673 b) else (if i < 704 then decide (31 ≤ count673 b) else decide (32 ≤ count673 b)))) else (if i < 708 then (if i < 706 then decide (33 ≤ count673 b) else (if i < 707 then decide (34 ≤ count673 b) else decide (35 ≤ count673 b))) else (if i < 709 then decide (36 ≤ count673 b) else (if i < 710 then decide (37 ≤ count673 b) else decide (38 ≤ count673 b))))) else (if i < 717 then (if i < 714 then (if i < 712 then decide (39 ≤ count673 b) else (if i < 713 then decide (40 ≤ count673 b) else decide (41 ≤ count673 b))) else (if i < 715 then decide (42 ≤ count673 b) else (if i < 716 then decide (1 ≤ count715 b) else decide (2 ≤ count715 b)))) else (if i < 720 then (if i < 718 then decide (1 ≤ count717 b) else (if i < 719 then decide (2 ≤ count717 b) else decide (3 ≤ count717 b))) else (if i < 721 then decide (1 ≤ count720 b) else (if i < 722 then decide (2 ≤ count720 b) else decide (1 ≤ count722 b))))))))))) else (if i < 1085 then (if i < 904 then (if i < 813 then (if i < 768 then (if i < 745 then (if i < 734 then (if i < 728 then (if i < 725 then (if i < 724 then decide (2 ≤ count722 b) else decide (3 ≤ count722 b)) else (if i < 726 then decide (1 ≤ count725 b) else (if i < 727 then decide (2 ≤ count725 b) else decide (3 ≤ count725 b)))) else (if i < 731 then (if i < 729 then decide (4 ≤ count725 b) else (if i < 730 then decide (5 ≤ count725 b) else decide (6 ≤ count725 b))) else (if i < 732 then decide (1 ≤ count731 b) else (if i < 733 then decide (2 ≤ count731 b) else decide (1 ≤ count733 b))))) else (if i < 739 then (if i < 736 then (if i < 735 then decide (2 ≤ count733 b) else decide (3 ≤ count733 b)) else (if i < 737 then decide (1 ≤ count736 b) else (if i < 738 then decide (2 ≤ count736 b) else decide (1 ≤ count738 b)))) else (if i < 742 then (if i < 740 then decide (2 ≤ count738 b) else (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b))) else (if i < 743 then decide (3 ≤ count740 b) else (if i < 744 then decide (4 ≤ count740 b) else decide (1 ≤ count744 b)))))) else (if i < 756 then (if i < 750 then (if i < 747 then (if i < 746 then decide (2 ≤ count744 b) else decide (3 ≤ count744 b)) else (if i < 748 then decide (4 ≤ count744 b) else (if i < 749 then decide (5 ≤ count744 b) else decide (6 ≤ count744 b)))) else (if i < 753 then (if i < 751 then decide (7 ≤ count744 b) else (if i < 752 then decide (1 ≤ count751 b) else decide (2 ≤ count751 b))) else (if i < 754 then decide (3 ≤ count751 b) else (if i < 755 then decide (4 ≤ count751 b) else decide (5 ≤ count751 b))))) else (if i < 762 then (if i < 759 then (if i < 757 then decide (6 ≤ count751 b) else (if i < 758 then decide (7 ≤ count751 b) else decide (8 ≤ count751 b))) else (if i < 760 then decide (9 ≤ count751 b) else (if i < 761 then decide (10 ≤ count751 b) else decide (11 ≤ count751 b)))) else (if i < 765 then (if i < 763 then decide (12 ≤ count751 b) else (if i < 764 then decide (13 ≤ count751 b) else decide (1 ≤ count764 b))) else (if i < 766 then decide (2 ≤ count764 b) else (if i < 767 then decide (1 ≤ count766 b) else decide (2 ≤ count766 b))))))) else (if i < 790 then (if i < 779 then (if i < 773 then (if i < 770 then (if i < 769 then decide (3 ≤ count766 b) else decide (1 ≤ count769 b)) else (if i < 771 then decide (2 ≤ count769 b) else (if i < 772 then decide (1 ≤ count771 b) else decide (2 ≤ count771 b)))) else (if i < 776 then (if i < 774 then decide (1 ≤ count773 b) else (if i < 775 then decide (2 ≤ count773 b) else decide (3 ≤ count773 b))) else (if i < 777 then decide (4 ≤ count773 b) else (if i < 778 then decide (1 ≤ count777 b) else decide (2 ≤ count777 b))))) else (if i < 784 then (if i < 781 then (if i < 780 then decide (3 ≤ count777 b) else decide (4 ≤ count777 b)) else (if i < 782 then decide (5 ≤ count777 b) else (if i < 783 then decide (6 ≤ count777 b) else decide (7 ≤ count777 b)))) else (if i < 787 then (if i < 785 then decide (1 ≤ count784 b) else (if i < 786 then decide (2 ≤ count784 b) else decide (1 ≤ count786 b))) else (if i < 788 then decide (2 ≤ count786 b) else (if i < 789 then decide (3 ≤ count786 b) else decide (1 ≤ count789 b)))))) else (if i < 801 then (if i < 795 then (if i < 792 then (if i < 791 then decide (2 ≤ count789 b) else decide (1 ≤ count791 b)) else (if i < 793 then decide (2 ≤ count791 b) else (if i < 794 then decide (1 ≤ count793 b) else decide (2 ≤ count793 b)))) else (if i < 798 then (if i < 796 then decide (3 ≤ count793 b) else (if i < 797 then decide (4 ≤ count793 b) else decide (1 ≤ count797 b))) else (if i < 799 then decide (2 ≤ count797 b) else (if i < 800 then decide (3 ≤ count797 b) else decide (4 ≤ count797 b))))) else (if i < 807 then (if i < 804 then (if i < 802 then decide (5 ≤ count797 b) else (if i < 803 then decide (6 ≤ count797 b) else decide (7 ≤ count797 b))) else (if i < 805 then decide (1 ≤ count804 b) else (if i < 806 then decide (2 ≤ count804 b) else decide (3 ≤ count804 b)))) else (if i < 810 then (if i < 808 then decide (4 ≤ count804 b) else (if i < 809 then decide (5 ≤ count804 b) else decide (6 ≤ count804 b))) else (if i < 811 then decide (7 ≤ count804 b) else (if i < 812 then decide (8 ≤ count804 b) else decide (9 ≤ count804 b)))))))) else (if i < 858 then (if i < 835 then (if i < 824 then (if i < 818 then (if i < 815 then (if i < 814 then decide (10 ≤ count804 b) else decide (11 ≤ count804 b)) else (if i < 816 then decide (12 ≤ count804 b) else (if i < 817 then decide (13 ≤ count804 b) else decide (14 ≤ count804 b)))) else (if i < 821 then (if i < 819 then decide (1 ≤ count818 b) else (if i < 820 then decide (2 ≤ count818 b) else decide (3 ≤ count818 b))) else (if i < 822 then decide (4 ≤ count818 b) else (if i < 823 then decide (5 ≤ count818 b) else decide (6 ≤ count818 b))))) else (if i < 829 then (if i < 826 then (if i < 825 then decide (7 ≤ count818 b) else decide (8 ≤ count818 b)) else (if i < 827 then decide (9 ≤ count818 b) else (if i < 828 then decide (10 ≤ count818 b) else decide (11 ≤ count818 b)))) else (if i < 832 then (if i < 830 then decide (12 ≤ count818 b) else (if i < 831 then decide (13 ≤ count818 b) else decide (14 ≤ count818 b))) else (if i < 833 then decide (1 ≤ count832 b) else (if i < 834 then decide (2 ≤ count832 b) else decide (1 ≤ count834 b)))))) else (if i < 846 then (if i < 840 then (if i < 837 then (if i < 836 then decide (2 ≤ count834 b) else decide (3 ≤ count834 b)) else (if i < 838 then decide (1 ≤ count837 b) else (if i < 839 then decide (2 ≤ count837 b) else decide (1 ≤ count839 b)))) else (if i < 843 then (if i < 841 then decide (2 ≤ count839 b) else (if i < 842 then decide (3 ≤ count839 b) else decide (1 ≤ count842 b))) else (if i < 844 then decide (2 ≤ count842 b) else (if i < 845 then decide (3 ≤ count842 b) else decide (4 ≤ count842 b))))) else (if i < 852 then (if i < 849 then (if i < 847 then decide (5 ≤ count842 b) else (if i < 848 then decide (6 ≤ count842 b) else decide (1 ≤ count848 b))) else (if i < 850 then decide (2 ≤ count848 b) else (if i < 851 then decide (1 ≤ count850 b) else decide (2 ≤ count850 b)))) else (if i < 855 then (if i < 853 then decide (3 ≤ count850 b) else (if i < 854 then decide (1 ≤ count853 b) else decide (2 ≤ count853 b))) else (if i < 856 then decide (1 ≤ count855 b) else (if i < 857 then decide (2 ≤ count855 b) else decide (1 ≤ count857 b))))))) else (if i < 881 then (if i < 869 then (if i < 863 then (if i < 860 then (if i < 859 then decide (2 ≤ count857 b) else decide (3 ≤ count857 b)) else (if i < 861 then decide (4 ≤ count857 b) else (if i < 862 then decide (1 ≤ count861 b) else decide (2 ≤ count861 b)))) else (if i < 866 then (if i < 864 then decide (3 ≤ count861 b) else (if i < 865 then decide (4 ≤ count861 b) else decide (5 ≤ count861 b))) else (if i < 867 then decide (6 ≤ count861 b) else (if i < 868 then decide (7 ≤ count861 b) else decide (1 ≤ count868 b))))) else (if i < 875 then (if i < 872 then (if i < 870 then decide (2 ≤ count868 b) else (if i < 871 then decide (3 ≤ count868 b) else decide (4 ≤ count868 b))) else (if i < 873 then decide (5 ≤ count868 b) else (if i < 874 then decide (6 ≤ count868 b) else decide (7 ≤ count868 b)))) else (if i < 878 then (if i < 876 then decide (8 ≤ count868 b) else (if i < 877 then decide (9 ≤ count868 b) else decide (10 ≤ count868 b))) else (if i < 879 then decide (11 ≤ count868 b) else (if i < 880 then decide (12 ≤ count868 b) else decide (13 ≤ count868 b)))))) else (if i < 892 then (if i < 886 then (if i < 883 then (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b)) else (if i < 884 then decide (1 ≤ count883 b) else (if i < 885 then decide (2 ≤ count883 b) else decide (3 ≤ count883 b)))) else (if i < 889 then (if i < 887 then decide (1 ≤ count886 b) else (if i < 888 then decide (2 ≤ count886 b) else decide (1 ≤ count888 b))) else (if i < 890 then decide (2 ≤ count888 b) else (if i < 891 then decide (1 ≤ count890 b) else decide (2 ≤ count890 b))))) else (if i < 898 then (if i < 895 then (if i < 893 then decide (3 ≤ count890 b) else (if i < 894 then decide (4 ≤ count890 b) else decide (1 ≤ count894 b))) else (if i < 896 then decide (2 ≤ count894 b) else (if i < 897 then decide (3 ≤ count894 b) else decide (4 ≤ count894 b)))) else (if i < 901 then (if i < 899 then decide (5 ≤ count894 b) else (if i < 900 then decide (6 ≤ count894 b) else decide (7 ≤ count894 b))) else (if i < 902 then decide (1 ≤ count901 b) else (if i < 903 then decide (2 ≤ count901 b) else decide (1 ≤ count903 b))))))))) else (if i < 994 then (if i < 949 then (if i < 926 then (if i < 915 then (if i < 909 then (if i < 906 then (if i < 905 then decide (2 ≤ count903 b) else decide (3 ≤ count903 b)) else (if i < 907 then decide (1 ≤ count906 b) else (if i < 908 then decide (2 ≤ count906 b) else decide (1 ≤ count908 b)))) else (if i < 912 then (if i < 910 then decide (2 ≤ count908 b) else (if i < 911 then decide (1 ≤ count910 b) else decide (2 ≤ count910 b))) else (if i < 913 then decide (3 ≤ count910 b) else (if i < 914 then decide (4 ≤ count910 b) else decide (1 ≤ count914 b))))) else (if i < 920 then (if i < 917 then (if i < 916 then decide (2 ≤ count914 b) else decide (3 ≤ count914 b)) else (if i < 918 then decide (4 ≤ count914 b) else (if i < 919 then decide (5 ≤ count914 b) else decide (6 ≤ count914 b)))) else (if i < 923 then (if i < 921 then decide (7 ≤ count914 b) else (if i < 922 then decide (1 ≤ count921 b) else decide (2 ≤ count921 b))) else (if i < 924 then decide (3 ≤ count921 b) else (if i < 925 then decide (4 ≤ count921 b) else decide (5 ≤ count921 b)))))) else (if i < 937 then (if i < 931 then (if i < 928 then (if i < 927 then decide (6 ≤ count921 b) else decide (7 ≤ count921 b)) else (if i < 929 then decide (8 ≤ count921 b) else (if i < 930 then decide (9 ≤ count921 b) else decide (10 ≤ count921 b)))) else (if i < 934 then (if i < 932 then decide (11 ≤ count921 b) else (if i < 933 then decide (12 ≤ count921 b) else decide (13 ≤ count921 b))) else (if i < 935 then decide (14 ≤ count921 b) else (if i < 936 then decide (1 ≤ count935 b) else decide (2 ≤ count935 b))))) else (if i < 943 then (if i < 940 then (if i < 938 then decide (3 ≤ count935 b) else (if i < 939 then decide (4 ≤ count935 b) else decide (5 ≤ count935 b))) else (if i < 941 then decide (6 ≤ count935 b) else (if i < 942 then decide (7 ≤ count935 b) else decide (8 ≤ count935 b)))) else (if i < 946 then (if i < 944 then decide (9 ≤ count935 b) else (if i < 945 then decide (10 ≤ count935 b) else decide (11 ≤ count935 b))) else (if i < 947 then decide (12 ≤ count935 b) else (if i < 948 then decide (13 ≤ count935 b) else decide (14 ≤ count935 b))))))) else (if i < 971 then (if i < 960 then (if i < 954 then (if i < 951 then (if i < 950 then decide (1 ≤ count949 b) else decide (2 ≤ count949 b)) else (if i < 952 then decide (3 ≤ count949 b) else (if i < 953 then decide (4 ≤ count949 b) else decide (5 ≤ count949 b)))) else (if i < 957 then (if i < 955 then decide (6 ≤ count949 b) else (if i < 956 then decide (7 ≤ count949 b) else decide (8 ≤ count949 b))) else (if i < 958 then decide (9 ≤ count949 b) else (if i < 959 then decide (10 ≤ count949 b) else decide (11 ≤ count949 b))))) else (if i < 965 then (if i < 962 then (if i < 961 then decide (12 ≤ count949 b) else decide (13 ≤ count949 b)) else (if i < 963 then decide (14 ≤ count949 b) else (if i < 964 then decide (1 ≤ count963 b) else decide (2 ≤ count963 b)))) else (if i < 968 then (if i < 966 then decide (1 ≤ count965 b) else (if i < 967 then decide (2 ≤ count965 b) else decide (3 ≤ count965 b))) else (if i < 969 then decide (1 ≤ count968 b) else (if i < 970 then decide (2 ≤ count968 b) else decide (1 ≤ count970 b)))))) else (if i < 982 then (if i < 976 then (if i < 973 then (if i < 972 then decide (2 ≤ count970 b) else decide (3 ≤ count970 b)) else (if i < 974 then decide (1 ≤ count973 b) else (if i < 975 then decide (2 ≤ count973 b) else decide (3 ≤ count973 b)))) else (if i < 979 then (if i < 977 then decide (4 ≤ count973 b) else (if i < 978 then decide (5 ≤ count973 b) else decide (6 ≤ count973 b))) else (if i < 980 then decide (1 ≤ count979 b) else (if i < 981 then decide (2 ≤ count979 b) else decide (1 ≤ count981 b))))) else (if i < 988 then (if i < 985 then (if i < 983 then decide (2 ≤ count981 b) else (if i < 984 then decide (3 ≤ count981 b) else decide (1 ≤ count984 b))) else (if i < 986 then decide (2 ≤ count984 b) else (if i < 987 then decide (1 ≤ count986 b) else decide (2 ≤ count986 b)))) else (if i < 991 then (if i < 989 then decide (3 ≤ count986 b) else (if i < 990 then decide (1 ≤ count989 b) else decide (2 ≤ count989 b))) else (if i < 992 then decide (3 ≤ count989 b) else (if i < 993 then decide (4 ≤ count989 b) else decide (5 ≤ count989 b)))))))) else (if i < 1039 then (if i < 1016 then (if i < 1005 then (if i < 999 then (if i < 996 then (if i < 995 then decide (6 ≤ count989 b) else decide (1 ≤ count995 b)) else (if i < 997 then decide (2 ≤ count995 b) else (if i < 998 then decide (3 ≤ count995 b) else decide (4 ≤ count995 b)))) else (if i < 1002 then (if i < 1000 then decide (5 ≤ count995 b) else (if i < 1001 then decide (6 ≤ count995 b) else decide (7 ≤ count995 b))) else (if i < 1003 then decide (8 ≤ count995 b) else (if i < 1004 then decide (9 ≤ count995 b) else decide (10 ≤ count995 b))))) else (if i < 1010 then (if i < 1007 then (if i < 1006 then decide (11 ≤ count995 b) else decide (12 ≤ count995 b)) else (if i < 1008 then decide (1 ≤ count1007 b) else (if i < 1009 then decide (2 ≤ count1007 b) else decide (1 ≤ count1009 b)))) else (if i < 1013 then (if i < 1011 then decide (2 ≤ count1009 b) else (if i < 1012 then decide (3 ≤ count1009 b) else decide (1 ≤ count1012 b))) else (if i < 1014 then decide (2 ≤ count1012 b) else (if i < 1015 then decide (1 ≤ count1014 b) else decide (2 ≤ count1014 b)))))) else (if i < 1027 then (if i < 1021 then (if i < 1018 then (if i < 1017 then decide (3 ≤ count1014 b) else decide (1 ≤ count1017 b)) else (if i < 1019 then decide (2 ≤ count1017 b) else (if i < 1020 then decide (3 ≤ count1017 b) else decide (4 ≤ count1017 b)))) else (if i < 1024 then (if i < 1022 then decide (5 ≤ count1017 b) else (if i < 1023 then decide (6 ≤ count1017 b) else decide (1 ≤ count1023 b))) else (if i < 1025 then decide (2 ≤ count1023 b) else (if i < 1026 then decide (1 ≤ count1025 b) else decide (2 ≤ count1025 b))))) else (if i < 1033 then (if i < 1030 then (if i < 1028 then decide (3 ≤ count1025 b) else (if i < 1029 then decide (1 ≤ count1028 b) else decide (2 ≤ count1028 b))) else (if i < 1031 then decide (1 ≤ count1030 b) else (if i < 1032 then decide (2 ≤ count1030 b) else decide (1 ≤ count1032 b)))) else (if i < 1036 then (if i < 1034 then decide (2 ≤ count1032 b) else (if i < 1035 then decide (3 ≤ count1032 b) else decide (4 ≤ count1032 b))) else (if i < 1037 then decide (1 ≤ count1036 b) else (if i < 1038 then decide (2 ≤ count1036 b) else decide (3 ≤ count1036 b))))))) else (if i < 1062 then (if i < 1050 then (if i < 1044 then (if i < 1041 then (if i < 1040 then decide (4 ≤ count1036 b) else decide (5 ≤ count1036 b)) else (if i < 1042 then decide (6 ≤ count1036 b) else (if i < 1043 then decide (7 ≤ count1036 b) else decide (1 ≤ count1043 b)))) else (if i < 1047 then (if i < 1045 then decide (2 ≤ count1043 b) else (if i < 1046 then decide (3 ≤ count1043 b) else decide (4 ≤ count1043 b))) else (if i < 1048 then decide (5 ≤ count1043 b) else (if i < 1049 then decide (6 ≤ count1043 b) else decide (7 ≤ count1043 b))))) else (if i < 1056 then (if i < 1053 then (if i < 1051 then decide (8 ≤ count1043 b) else (if i < 1052 then decide (9 ≤ count1043 b) else decide (10 ≤ count1043 b))) else (if i < 1054 then decide (11 ≤ count1043 b) else (if i < 1055 then decide (12 ≤ count1043 b) else decide (13 ≤ count1043 b)))) else (if i < 1059 then (if i < 1057 then decide (1 ≤ count1056 b) else (if i < 1058 then decide (2 ≤ count1056 b) else decide (3 ≤ count1056 b))) else (if i < 1060 then decide (4 ≤ count1056 b) else (if i < 1061 then decide (5 ≤ count1056 b) else decide (6 ≤ count1056 b)))))) else (if i < 1073 then (if i < 1067 then (if i < 1064 then (if i < 1063 then decide (7 ≤ count1056 b) else decide (8 ≤ count1056 b)) else (if i < 1065 then decide (9 ≤ count1056 b) else (if i < 1066 then decide (10 ≤ count1056 b) else decide (11 ≤ count1056 b)))) else (if i < 1070 then (if i < 1068 then decide (12 ≤ count1056 b) else (if i < 1069 then decide (13 ≤ count1056 b) else decide (14 ≤ count1056 b))) else (if i < 1071 then decide (15 ≤ count1056 b) else (if i < 1072 then decide (16 ≤ count1056 b) else decide (17 ≤ count1056 b))))) else (if i < 1079 then (if i < 1076 then (if i < 1074 then decide (18 ≤ count1056 b) else (if i < 1075 then decide (19 ≤ count1056 b) else decide (20 ≤ count1056 b))) else (if i < 1077 then decide (21 ≤ count1056 b) else (if i < 1078 then decide (22 ≤ count1056 b) else decide (23 ≤ count1056 b)))) else (if i < 1082 then (if i < 1080 then decide (24 ≤ count1056 b) else (if i < 1081 then decide (25 ≤ count1056 b) else decide (1 ≤ count1081 b))) else (if i < 1083 then decide (2 ≤ count1081 b) else (if i < 1084 then decide (1 ≤ count1083 b) else decide (2 ≤ count1083 b)))))))))) else (if i < 1266 then (if i < 1175 then (if i < 1130 then (if i < 1107 then (if i < 1096 then (if i < 1090 then (if i < 1087 then (if i < 1086 then decide (3 ≤ count1083 b) else decide (1 ≤ count1086 b)) else (if i < 1088 then decide (2 ≤ count1086 b) else (if i < 1089 then decide (1 ≤ count1088 b) else decide (2 ≤ count1088 b)))) else (if i < 1093 then (if i < 1091 then decide (3 ≤ count1088 b) else (if i < 1092 then decide (1 ≤ count1091 b) else decide (2 ≤ count1091 b))) else (if i < 1094 then decide (3 ≤ count1091 b) else (if i < 1095 then decide (4 ≤ count1091 b) else decide (5 ≤ count1091 b))))) else (if i < 1101 then (if i < 1098 then (if i < 1097 then decide (6 ≤ count1091 b) else decide (1 ≤ count1097 b)) else (if i < 1099 then decide (2 ≤ count1097 b) else (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b)))) else (if i < 1104 then (if i < 1102 then decide (3 ≤ count1099 b) else (if i < 1103 then decide (1 ≤ count1102 b) else decide (2 ≤ count1102 b))) else (if i < 1105 then decide (1 ≤ count1104 b) else (if i < 1106 then decide (2 ≤ count1104 b) else decide (3 ≤ count1104 b)))))) else (if i < 1118 then (if i < 1112 then (if i < 1109 then (if i < 1108 then decide (1 ≤ count1107 b) else decide (2 ≤ count1107 b)) else (if i < 1110 then decide (3 ≤ count1107 b) else (if i < 1111 then decide (4 ≤ count1107 b) else decide (5 ≤ count1107 b)))) else (if i < 1115 then (if i < 1113 then decide (6 ≤ count1107 b) else (if i < 1114 then decide (1 ≤ count1113 b) else decide (2 ≤ count1113 b))) else (if i < 1116 then decide (3 ≤ count1113 b) else (if i < 1117 then decide (4 ≤ count1113 b) else decide (5 ≤ count1113 b))))) else (if i < 1124 then (if i < 1121 then (if i < 1119 then decide (6 ≤ count1113 b) else (if i < 1120 then decide (7 ≤ count1113 b) else decide (8 ≤ count1113 b))) else (if i < 1122 then decide (9 ≤ count1113 b) else (if i < 1123 then decide (10 ≤ count1113 b) else decide (11 ≤ count1113 b)))) else (if i < 1127 then (if i < 1125 then decide (12 ≤ count1113 b) else (if i < 1126 then decide (1 ≤ count1125 b) else decide (2 ≤ count1125 b))) else (if i < 1128 then decide (1 ≤ count1127 b) else (if i < 1129 then decide (2 ≤ count1127 b) else decide (3 ≤ count1127 b))))))) else (if i < 1152 then (if i < 1141 then (if i < 1135 then (if i < 1132 then (if i < 1131 then decide (1 ≤ count1130 b) else decide (2 ≤ count1130 b)) else (if i < 1133 then decide (1 ≤ count1132 b) else (if i < 1134 then decide (2 ≤ count1132 b) else decide (3 ≤ count1132 b)))) else (if i < 1138 then (if i < 1136 then decide (1 ≤ count1135 b) else (if i < 1137 then decide (2 ≤ count1135 b) else decide (3 ≤ count1135 b))) else (if i < 1139 then decide (4 ≤ count1135 b) else (if i < 1140 then decide (5 ≤ count1135 b) else decide (6 ≤ count1135 b))))) else (if i < 1146 then (if i < 1143 then (if i < 1142 then decide (1 ≤ count1141 b) else decide (2 ≤ count1141 b)) else (if i < 1144 then decide (1 ≤ count1143 b) else (if i < 1145 then decide (2 ≤ count1143 b) else decide (3 ≤ count1143 b)))) else (if i < 1149 then (if i < 1147 then decide (1 ≤ count1146 b) else (if i < 1148 then decide (2 ≤ count1146 b) else decide (1 ≤ count1148 b))) else (if i < 1150 then decide (2 ≤ count1148 b) else (if i < 1151 then decide (1 ≤ count1150 b) else decide (2 ≤ count1150 b)))))) else (if i < 1163 then (if i < 1157 then (if i < 1154 then (if i < 1153 then decide (3 ≤ count1150 b) else decide (4 ≤ count1150 b)) else (if i < 1155 then decide (1 ≤ count1154 b) else (if i < 1156 then decide (2 ≤ count1154 b) else decide (3 ≤ count1154 b)))) else (if i < 1160 then (if i < 1158 then decide (4 ≤ count1154 b) else (if i < 1159 then decide (5 ≤ count1154 b) else decide (6 ≤ count1154 b))) else (if i < 1161 then decide (7 ≤ count1154 b) else (if i < 1162 then decide (1 ≤ count1161 b) else decide (2 ≤ count1161 b))))) else (if i < 1169 then (if i < 1166 then (if i < 1164 then decide (3 ≤ count1161 b) else (if i < 1165 then decide (4 ≤ count1161 b) else decide (5 ≤ count1161 b))) else (if i < 1167 then decide (6 ≤ count1161 b) else (if i < 1168 then decide (7 ≤ count1161 b) else decide (8 ≤ count1161 b)))) else (if i < 1172 then (if i < 1170 then decide (9 ≤ count1161 b) else (if i < 1171 then decide (10 ≤ count1161 b) else decide (11 ≤ count1161 b))) else (if i < 1173 then decide (12 ≤ count1161 b) else (if i < 1174 then decide (13 ≤ count1161 b) else decide (1 ≤ count1174 b)))))))) else (if i < 1220 then (if i < 1197 then (if i < 1186 then (if i < 1180 then (if i < 1177 then (if i < 1176 then decide (2 ≤ count1174 b) else decide (3 ≤ count1174 b)) else (if i < 1178 then decide (4 ≤ count1174 b) else (if i < 1179 then decide (5 ≤ count1174 b) else decide (6 ≤ count1174 b)))) else (if i < 1183 then (if i < 1181 then decide (7 ≤ count1174 b) else (if i < 1182 then decide (8 ≤ count1174 b) else decide (9 ≤ count1174 b))) else (if i < 1184 then decide (10 ≤ count1174 b) else (if i < 1185 then decide (11 ≤ count1174 b) else decide (12 ≤ count1174 b))))) else (if i < 1191 then (if i < 1188 then (if i < 1187 then decide (13 ≤ count1174 b) else decide (14 ≤ count1174 b)) else (if i < 1189 then decide (15 ≤ count1174 b) else (if i < 1190 then decide (16 ≤ count1174 b) else decide (17 ≤ count1174 b)))) else (if i < 1194 then (if i < 1192 then decide (18 ≤ count1174 b) else (if i < 1193 then decide (19 ≤ count1174 b) else decide (20 ≤ count1174 b))) else (if i < 1195 then decide (21 ≤ count1174 b) else (if i < 1196 then decide (22 ≤ count1174 b) else decide (23 ≤ count1174 b)))))) else (if i < 1208 then (if i < 1202 then (if i < 1199 then (if i < 1198 then decide (24 ≤ count1174 b) else decide (25 ≤ count1174 b)) else (if i < 1200 then decide (1 ≤ count1199 b) else (if i < 1201 then decide (2 ≤ count1199 b) else decide (3 ≤ count1199 b)))) else (if i < 1205 then (if i < 1203 then decide (4 ≤ count1199 b) else (if i < 1204 then decide (5 ≤ count1199 b) else decide (6 ≤ count1199 b))) else (if i < 1206 then decide (7 ≤ count1199 b) else (if i < 1207 then decide (8 ≤ count1199 b) else decide (9 ≤ count1199 b))))) else (if i < 1214 then (if i < 1211 then (if i < 1209 then decide (10 ≤ count1199 b) else (if i < 1210 then decide (11 ≤ count1199 b) else decide (12 ≤ count1199 b))) else (if i < 1212 then decide (13 ≤ count1199 b) else (if i < 1213 then decide (14 ≤ count1199 b) else decide (15 ≤ count1199 b)))) else (if i < 1217 then (if i < 1215 then decide (16 ≤ count1199 b) else (if i < 1216 then decide (17 ≤ count1199 b) else decide (18 ≤ count1199 b))) else (if i < 1218 then decide (19 ≤ count1199 b) else (if i < 1219 then decide (20 ≤ count1199 b) else decide (21 ≤ count1199 b))))))) else (if i < 1243 then (if i < 1231 then (if i < 1225 then (if i < 1222 then (if i < 1221 then decide (22 ≤ count1199 b) else decide (23 ≤ count1199 b)) else (if i < 1223 then decide (24 ≤ count1199 b) else (if i < 1224 then decide (25 ≤ count1199 b) else decide (26 ≤ count1199 b)))) else (if i < 1228 then (if i < 1226 then decide (27 ≤ count1199 b) else (if i < 1227 then decide (28 ≤ count1199 b) else decide (29 ≤ count1199 b))) else (if i < 1229 then decide (30 ≤ count1199 b) else (if i < 1230 then decide (31 ≤ count1199 b) else decide (32 ≤ count1199 b))))) else (if i < 1237 then (if i < 1234 then (if i < 1232 then decide (33 ≤ count1199 b) else (if i < 1233 then decide (34 ≤ count1199 b) else decide (35 ≤ count1199 b))) else (if i < 1235 then decide (36 ≤ count1199 b) else (if i < 1236 then decide (37 ≤ count1199 b) else decide (38 ≤ count1199 b)))) else (if i < 1240 then (if i < 1238 then decide (39 ≤ count1199 b) else (if i < 1239 then decide (40 ≤ count1199 b) else decide (41 ≤ count1199 b))) else (if i < 1241 then decide (42 ≤ count1199 b) else (if i < 1242 then decide (1 ≤ count1241 b) else decide (2 ≤ count1241 b)))))) else (if i < 1254 then (if i < 1248 then (if i < 1245 then (if i < 1244 then decide (1 ≤ count1243 b) else decide (2 ≤ count1243 b)) else (if i < 1246 then decide (3 ≤ count1243 b) else (if i < 1247 then decide (1 ≤ count1246 b) else decide (2 ≤ count1246 b)))) else (if i < 1251 then (if i < 1249 then decide (1 ≤ count1248 b) else (if i < 1250 then decide (2 ≤ count1248 b) else decide (3 ≤ count1248 b))) else (if i < 1252 then decide (1 ≤ count1251 b) else (if i < 1253 then decide (2 ≤ count1251 b) else decide (3 ≤ count1251 b))))) else (if i < 1260 then (if i < 1257 then (if i < 1255 then decide (4 ≤ count1251 b) else (if i < 1256 then decide (5 ≤ count1251 b) else decide (6 ≤ count1251 b))) else (if i < 1258 then decide (1 ≤ count1257 b) else (if i < 1259 then decide (2 ≤ count1257 b) else decide (1 ≤ count1259 b)))) else (if i < 1263 then (if i < 1261 then decide (2 ≤ count1259 b) else (if i < 1262 then decide (3 ≤ count1259 b) else decide (1 ≤ count1262 b))) else (if i < 1264 then decide (2 ≤ count1262 b) else (if i < 1265 then decide (1 ≤ count1264 b) else decide (2 ≤ count1264 b))))))))) else (if i < 1356 then (if i < 1311 then (if i < 1288 then (if i < 1277 then (if i < 1271 then (if i < 1268 then (if i < 1267 then decide (3 ≤ count1264 b) else decide (1 ≤ count1267 b)) else (if i < 1269 then decide (2 ≤ count1267 b) else (if i < 1270 then decide (3 ≤ count1267 b) else decide (4 ≤ count1267 b)))) else (if i < 1274 then (if i < 1272 then decide (5 ≤ count1267 b) else (if i < 1273 then decide (6 ≤ count1267 b) else decide (1 ≤ count1273 b))) else (if i < 1275 then decide (2 ≤ count1273 b) else (if i < 1276 then decide (3 ≤ count1273 b) else decide (4 ≤ count1273 b))))) else (if i < 1282 then (if i < 1279 then (if i < 1278 then decide (5 ≤ count1273 b) else decide (6 ≤ count1273 b)) else (if i < 1280 then decide (7 ≤ count1273 b) else (if i < 1281 then decide (8 ≤ count1273 b) else decide (9 ≤ count1273 b)))) else (if i < 1285 then (if i < 1283 then decide (10 ≤ count1273 b) else (if i < 1284 then decide (1 ≤ count1283 b) else decide (2 ≤ count1283 b))) else (if i < 1286 then decide (1 ≤ count1285 b) else (if i < 1287 then decide (2 ≤ count1285 b) else decide (3 ≤ count1285 b)))))) else (if i < 1299 then (if i < 1293 then (if i < 1290 then (if i < 1289 then decide (1 ≤ count1288 b) else decide (2 ≤ count1288 b)) else (if i < 1291 then decide (1 ≤ count1290 b) else (if i < 1292 then decide (2 ≤ count1290 b) else decide (3 ≤ count1290 b)))) else (if i < 1296 then (if i < 1294 then decide (1 ≤ count1293 b) else (if i < 1295 then decide (2 ≤ count1293 b) else decide (3 ≤ count1293 b))) else (if i < 1297 then decide (4 ≤ count1293 b) else (if i < 1298 then decide (5 ≤ count1293 b) else decide (6 ≤ count1293 b))))) else (if i < 1305 then (if i < 1302 then (if i < 1300 then decide (1 ≤ count1299 b) else (if i < 1301 then decide (2 ≤ count1299 b) else decide (1 ≤ count1301 b))) else (if i < 1303 then decide (2 ≤ count1301 b) else (if i < 1304 then decide (3 ≤ count1301 b) else decide (1 ≤ count1304 b)))) else (if i < 1308 then (if i < 1306 then decide (2 ≤ count1304 b) else (if i < 1307 then decide (1 ≤ count1306 b) else decide (2 ≤ count1306 b))) else (if i < 1309 then decide (1 ≤ count1308 b) else (if i < 1310 then decide (2 ≤ count1308 b) else decide (3 ≤ count1308 b))))))) else (if i < 1333 then (if i < 1322 then (if i < 1316 then (if i < 1313 then (if i < 1312 then decide (4 ≤ count1308 b) else decide (1 ≤ count1312 b)) else (if i < 1314 then decide (2 ≤ count1312 b) else (if i < 1315 then decide (3 ≤ count1312 b) else decide (4 ≤ count1312 b)))) else (if i < 1319 then (if i < 1317 then decide (5 ≤ count1312 b) else (if i < 1318 then decide (6 ≤ count1312 b) else decide (7 ≤ count1312 b))) else (if i < 1320 then decide (1 ≤ count1319 b) else (if i < 1321 then decide (2 ≤ count1319 b) else decide (3 ≤ count1319 b))))) else (if i < 1327 then (if i < 1324 then (if i < 1323 then decide (4 ≤ count1319 b) else decide (5 ≤ count1319 b)) else (if i < 1325 then decide (6 ≤ count1319 b) else (if i < 1326 then decide (7 ≤ count1319 b) else decide (8 ≤ count1319 b)))) else (if i < 1330 then (if i < 1328 then decide (9 ≤ count1319 b) else (if i < 1329 then decide (10 ≤ count1319 b) else decide (1 ≤ count1329 b))) else (if i < 1331 then decide (2 ≤ count1329 b) else (if i < 1332 then decide (3 ≤ count1329 b) else decide (4 ≤ count1329 b)))))) else (if i < 1344 then (if i < 1338 then (if i < 1335 then (if i < 1334 then decide (5 ≤ count1329 b) else decide (6 ≤ count1329 b)) else (if i < 1336 then decide (7 ≤ count1329 b) else (if i < 1337 then decide (8 ≤ count1329 b) else decide (9 ≤ count1329 b)))) else (if i < 1341 then (if i < 1339 then decide (10 ≤ count1329 b) else (if i < 1340 then decide (1 ≤ count1339 b) else decide (2 ≤ count1339 b))) else (if i < 1342 then decide (1 ≤ count1341 b) else (if i < 1343 then decide (2 ≤ count1341 b) else decide (3 ≤ count1341 b))))) else (if i < 1350 then (if i < 1347 then (if i < 1345 then decide (1 ≤ count1344 b) else (if i < 1346 then decide (2 ≤ count1344 b) else decide (1 ≤ count1346 b))) else (if i < 1348 then decide (2 ≤ count1346 b) else (if i < 1349 then decide (3 ≤ count1346 b) else decide (1 ≤ count1349 b)))) else (if i < 1353 then (if i < 1351 then decide (2 ≤ count1349 b) else (if i < 1352 then decide (3 ≤ count1349 b) else decide (4 ≤ count1349 b))) else (if i < 1354 then decide (5 ≤ count1349 b) else (if i < 1355 then decide (6 ≤ count1349 b) else decide (1 ≤ count1355 b)))))))) else (if i < 1401 then (if i < 1378 then (if i < 1367 then (if i < 1361 then (if i < 1358 then (if i < 1357 then decide (2 ≤ count1355 b) else decide (1 ≤ count1357 b)) else (if i < 1359 then decide (2 ≤ count1357 b) else (if i < 1360 then decide (3 ≤ count1357 b) else decide (1 ≤ count1360 b)))) else (if i < 1364 then (if i < 1362 then decide (2 ≤ count1360 b) else (if i < 1363 then decide (1 ≤ count1362 b) else decide (2 ≤ count1362 b))) else (if i < 1365 then decide (3 ≤ count1362 b) else (if i < 1366 then decide (1 ≤ count1365 b) else decide (2 ≤ count1365 b))))) else (if i < 1372 then (if i < 1369 then (if i < 1368 then decide (3 ≤ count1365 b) else decide (4 ≤ count1365 b)) else (if i < 1370 then decide (5 ≤ count1365 b) else (if i < 1371 then decide (6 ≤ count1365 b) else decide (1 ≤ count1371 b)))) else (if i < 1375 then (if i < 1373 then decide (2 ≤ count1371 b) else (if i < 1374 then decide (3 ≤ count1371 b) else decide (4 ≤ count1371 b))) else (if i < 1376 then decide (5 ≤ count1371 b) else (if i < 1377 then decide (6 ≤ count1371 b) else decide (7 ≤ count1371 b)))))) else (if i < 1389 then (if i < 1383 then (if i < 1380 then (if i < 1379 then decide (8 ≤ count1371 b) else decide (9 ≤ count1371 b)) else (if i < 1381 then decide (10 ≤ count1371 b) else (if i < 1382 then decide (1 ≤ count1381 b) else decide (2 ≤ count1381 b)))) else (if i < 1386 then (if i < 1384 then decide (1 ≤ count1383 b) else (if i < 1385 then decide (2 ≤ count1383 b) else decide (3 ≤ count1383 b))) else (if i < 1387 then decide (1 ≤ count1386 b) else (if i < 1388 then decide (2 ≤ count1386 b) else decide (1 ≤ count1388 b))))) else (if i < 1395 then (if i < 1392 then (if i < 1390 then decide (2 ≤ count1388 b) else (if i < 1391 then decide (3 ≤ count1388 b) else decide (1 ≤ count1391 b))) else (if i < 1393 then decide (2 ≤ count1391 b) else (if i < 1394 then decide (3 ≤ count1391 b) else decide (4 ≤ count1391 b)))) else (if i < 1398 then (if i < 1396 then decide (5 ≤ count1391 b) else (if i < 1397 then decide (6 ≤ count1391 b) else decide (1 ≤ count1397 b))) else (if i < 1399 then decide (2 ≤ count1397 b) else (if i < 1400 then decide (1 ≤ count1399 b) else decide (2 ≤ count1399 b))))))) else (if i < 1424 then (if i < 1412 then (if i < 1406 then (if i < 1403 then (if i < 1402 then decide (3 ≤ count1399 b) else decide (1 ≤ count1402 b)) else (if i < 1404 then decide (2 ≤ count1402 b) else (if i < 1405 then decide (1 ≤ count1404 b) else decide (2 ≤ count1404 b)))) else (if i < 1409 then (if i < 1407 then decide (1 ≤ count1406 b) else (if i < 1408 then decide (2 ≤ count1406 b) else decide (3 ≤ count1406 b))) else (if i < 1410 then decide (4 ≤ count1406 b) else (if i < 1411 then decide (1 ≤ count1410 b) else decide (2 ≤ count1410 b))))) else (if i < 1418 then (if i < 1415 then (if i < 1413 then decide (3 ≤ count1410 b) else (if i < 1414 then decide (4 ≤ count1410 b) else decide (5 ≤ count1410 b))) else (if i < 1416 then decide (6 ≤ count1410 b) else (if i < 1417 then decide (7 ≤ count1410 b) else decide (1 ≤ count1417 b)))) else (if i < 1421 then (if i < 1419 then decide (2 ≤ count1417 b) else (if i < 1420 then decide (3 ≤ count1417 b) else decide (4 ≤ count1417 b))) else (if i < 1422 then decide (5 ≤ count1417 b) else (if i < 1423 then decide (6 ≤ count1417 b) else decide (7 ≤ count1417 b)))))) else (if i < 1435 then (if i < 1429 then (if i < 1426 then (if i < 1425 then decide (8 ≤ count1417 b) else decide (9 ≤ count1417 b)) else (if i < 1427 then decide (10 ≤ count1417 b) else (if i < 1428 then decide (1 ≤ count1427 b) else decide (2 ≤ count1427 b)))) else (if i < 1432 then (if i < 1430 then decide (3 ≤ count1427 b) else (if i < 1431 then decide (4 ≤ count1427 b) else decide (5 ≤ count1427 b))) else (if i < 1433 then decide (6 ≤ count1427 b) else (if i < 1434 then decide (7 ≤ count1427 b) else decide (8 ≤ count1427 b))))) else (if i < 1441 then (if i < 1438 then (if i < 1436 then decide (9 ≤ count1427 b) else (if i < 1437 then decide (10 ≤ count1427 b) else decide (1 ≤ count1437 b))) else (if i < 1439 then decide (2 ≤ count1437 b) else (if i < 1440 then decide (3 ≤ count1437 b) else decide (4 ≤ count1437 b)))) else (if i < 1444 then (if i < 1442 then decide (5 ≤ count1437 b) else (if i < 1443 then decide (6 ≤ count1437 b) else decide (7 ≤ count1437 b))) else (if i < 1445 then decide (8 ≤ count1437 b) else (if i < 1446 then decide (9 ≤ count1437 b) else decide (10 ≤ count1437 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (17 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (18 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (19 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (22 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (64 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (65 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (66 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (70 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (72 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (76 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (78 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (128 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (130 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (132 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (134 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (135 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (136 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (137 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (138 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (140 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (142 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (148 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (149 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (151 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (153 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (154 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (155 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (159 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (192 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (193 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (198 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (199 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (200 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (201 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (205 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (207 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (209 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (210 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (211 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (214 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (218 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (220 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (221 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (222 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (288 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (289 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (296 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (305 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (306 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (307 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (310 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (316 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (317 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (318 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (320 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (321 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (326 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (327 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (328 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (329 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (333 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (335 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (337 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (338 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (339 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (342 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (346 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (348 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (349 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (350 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (390 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (392 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (393 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (397 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (399 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (406 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (410 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (412 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (413 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (414 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (418 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (422 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (424 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (428 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (430 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (480 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (481 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (486 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (487 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (488 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (489 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (493 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (495 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (497 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (498 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (499 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (502 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (506 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (508 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (509 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (510 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (72 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (128 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (153 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (209 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (210 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (306 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (316 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (318 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (326 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (390 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (392 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (422 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (489 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (1 ≤ count209 (baseVal q)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (1 ≤ count211 (baseVal q)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (1 ≤ count213 (baseVal q)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (1 ≤ count217 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (2 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value250 (q : Snake 81) : valuation q 250 = decide (2 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (2 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value276 (q : Snake 81) : valuation q 276 = decide (2 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value278 (q : Snake 81) : valuation q 278 = decide (2 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value288 (q : Snake 81) : valuation q 288 = decide (2 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value332 (q : Snake 81) : valuation q 332 = decide (2 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value352 (q : Snake 81) : valuation q 352 = decide (2 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value382 (q : Snake 81) : valuation q 382 = decide (2 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value408 (q : Snake 81) : valuation q 408 = decide (2 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value715 (q : Snake 81) : valuation q 715 = decide (1 ≤ count715 (baseVal q)) := rfl
theorem value717 (q : Snake 81) : valuation q 717 = decide (1 ≤ count717 (baseVal q)) := rfl
theorem value718 (q : Snake 81) : valuation q 718 = decide (2 ≤ count717 (baseVal q)) := rfl
theorem value720 (q : Snake 81) : valuation q 720 = decide (1 ≤ count720 (baseVal q)) := rfl
theorem value722 (q : Snake 81) : valuation q 722 = decide (1 ≤ count722 (baseVal q)) := rfl
theorem value725 (q : Snake 81) : valuation q 725 = decide (1 ≤ count725 (baseVal q)) := rfl
theorem value726 (q : Snake 81) : valuation q 726 = decide (2 ≤ count725 (baseVal q)) := rfl
theorem value727 (q : Snake 81) : valuation q 727 = decide (3 ≤ count725 (baseVal q)) := rfl
theorem value731 (q : Snake 81) : valuation q 731 = decide (1 ≤ count731 (baseVal q)) := rfl
theorem value732 (q : Snake 81) : valuation q 732 = decide (2 ≤ count731 (baseVal q)) := rfl
theorem value733 (q : Snake 81) : valuation q 733 = decide (1 ≤ count733 (baseVal q)) := rfl
theorem value734 (q : Snake 81) : valuation q 734 = decide (2 ≤ count733 (baseVal q)) := rfl
theorem value735 (q : Snake 81) : valuation q 735 = decide (3 ≤ count733 (baseVal q)) := rfl
theorem value736 (q : Snake 81) : valuation q 736 = decide (1 ≤ count736 (baseVal q)) := rfl
theorem value737 (q : Snake 81) : valuation q 737 = decide (2 ≤ count736 (baseVal q)) := rfl
theorem value738 (q : Snake 81) : valuation q 738 = decide (1 ≤ count738 (baseVal q)) := rfl
theorem value739 (q : Snake 81) : valuation q 739 = decide (2 ≤ count738 (baseVal q)) := rfl
theorem value742 (q : Snake 81) : valuation q 742 = decide (3 ≤ count740 (baseVal q)) := rfl
theorem value743 (q : Snake 81) : valuation q 743 = decide (4 ≤ count740 (baseVal q)) := rfl
theorem value748 (q : Snake 81) : valuation q 748 = decide (5 ≤ count744 (baseVal q)) := rfl
theorem value749 (q : Snake 81) : valuation q 749 = decide (6 ≤ count744 (baseVal q)) := rfl
theorem value757 (q : Snake 81) : valuation q 757 = decide (7 ≤ count751 (baseVal q)) := rfl
theorem value758 (q : Snake 81) : valuation q 758 = decide (8 ≤ count751 (baseVal q)) := rfl
theorem value764 (q : Snake 81) : valuation q 764 = decide (1 ≤ count764 (baseVal q)) := rfl
theorem value766 (q : Snake 81) : valuation q 766 = decide (1 ≤ count766 (baseVal q)) := rfl
theorem value767 (q : Snake 81) : valuation q 767 = decide (2 ≤ count766 (baseVal q)) := rfl
theorem value769 (q : Snake 81) : valuation q 769 = decide (1 ≤ count769 (baseVal q)) := rfl
theorem value771 (q : Snake 81) : valuation q 771 = decide (1 ≤ count771 (baseVal q)) := rfl
theorem value773 (q : Snake 81) : valuation q 773 = decide (1 ≤ count773 (baseVal q)) := rfl
theorem value774 (q : Snake 81) : valuation q 774 = decide (2 ≤ count773 (baseVal q)) := rfl
theorem value777 (q : Snake 81) : valuation q 777 = decide (1 ≤ count777 (baseVal q)) := rfl
theorem value778 (q : Snake 81) : valuation q 778 = decide (2 ≤ count777 (baseVal q)) := rfl
theorem value779 (q : Snake 81) : valuation q 779 = decide (3 ≤ count777 (baseVal q)) := rfl
theorem value784 (q : Snake 81) : valuation q 784 = decide (1 ≤ count784 (baseVal q)) := rfl
theorem value786 (q : Snake 81) : valuation q 786 = decide (1 ≤ count786 (baseVal q)) := rfl
theorem value789 (q : Snake 81) : valuation q 789 = decide (1 ≤ count789 (baseVal q)) := rfl
theorem value793 (q : Snake 81) : valuation q 793 = decide (1 ≤ count793 (baseVal q)) := rfl
theorem value798 (q : Snake 81) : valuation q 798 = decide (2 ≤ count797 (baseVal q)) := rfl
theorem value806 (q : Snake 81) : valuation q 806 = decide (3 ≤ count804 (baseVal q)) := rfl
theorem value807 (q : Snake 81) : valuation q 807 = decide (4 ≤ count804 (baseVal q)) := rfl
theorem value808 (q : Snake 81) : valuation q 808 = decide (5 ≤ count804 (baseVal q)) := rfl
theorem value827 (q : Snake 81) : valuation q 827 = decide (10 ≤ count818 (baseVal q)) := rfl
theorem value828 (q : Snake 81) : valuation q 828 = decide (11 ≤ count818 (baseVal q)) := rfl
theorem value829 (q : Snake 81) : valuation q 829 = decide (12 ≤ count818 (baseVal q)) := rfl
theorem value839 (q : Snake 81) : valuation q 839 = decide (1 ≤ count839 (baseVal q)) := rfl
theorem value842 (q : Snake 81) : valuation q 842 = decide (1 ≤ count842 (baseVal q)) := rfl
theorem value855 (q : Snake 81) : valuation q 855 = decide (1 ≤ count855 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (1 ≤ count857 (baseVal q)) := rfl
theorem value861 (q : Snake 81) : valuation q 861 = decide (1 ≤ count861 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (1 ≤ count868 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (2 ≤ count868 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (1 ≤ count883 (baseVal q)) := rfl
theorem value886 (q : Snake 81) : valuation q 886 = decide (1 ≤ count886 (baseVal q)) := rfl
theorem value890 (q : Snake 81) : valuation q 890 = decide (1 ≤ count890 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (2 ≤ count894 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (2 ≤ count921 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (2 ≤ count935 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (3 ≤ count935 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (4 ≤ count935 (baseVal q)) := rfl
theorem value962 (q : Snake 81) : valuation q 962 = decide (14 ≤ count949 (baseVal q)) := rfl
theorem value1241 (q : Snake 81) : valuation q 1241 = decide (1 ≤ count1241 (baseVal q)) := rfl
theorem value1242 (q : Snake 81) : valuation q 1242 = decide (2 ≤ count1241 (baseVal q)) := rfl
theorem value1243 (q : Snake 81) : valuation q 1243 = decide (1 ≤ count1243 (baseVal q)) := rfl
theorem value1244 (q : Snake 81) : valuation q 1244 = decide (2 ≤ count1243 (baseVal q)) := rfl
theorem value1245 (q : Snake 81) : valuation q 1245 = decide (3 ≤ count1243 (baseVal q)) := rfl
theorem value1246 (q : Snake 81) : valuation q 1246 = decide (1 ≤ count1246 (baseVal q)) := rfl
theorem value1247 (q : Snake 81) : valuation q 1247 = decide (2 ≤ count1246 (baseVal q)) := rfl
theorem value1248 (q : Snake 81) : valuation q 1248 = decide (1 ≤ count1248 (baseVal q)) := rfl
theorem value1249 (q : Snake 81) : valuation q 1249 = decide (2 ≤ count1248 (baseVal q)) := rfl
theorem value1250 (q : Snake 81) : valuation q 1250 = decide (3 ≤ count1248 (baseVal q)) := rfl
theorem value1251 (q : Snake 81) : valuation q 1251 = decide (1 ≤ count1251 (baseVal q)) := rfl
theorem value1252 (q : Snake 81) : valuation q 1252 = decide (2 ≤ count1251 (baseVal q)) := rfl
theorem value1253 (q : Snake 81) : valuation q 1253 = decide (3 ≤ count1251 (baseVal q)) := rfl
theorem value1254 (q : Snake 81) : valuation q 1254 = decide (4 ≤ count1251 (baseVal q)) := rfl
theorem value1255 (q : Snake 81) : valuation q 1255 = decide (5 ≤ count1251 (baseVal q)) := rfl
theorem value1257 (q : Snake 81) : valuation q 1257 = decide (1 ≤ count1257 (baseVal q)) := rfl
theorem value1258 (q : Snake 81) : valuation q 1258 = decide (2 ≤ count1257 (baseVal q)) := rfl
theorem value1259 (q : Snake 81) : valuation q 1259 = decide (1 ≤ count1259 (baseVal q)) := rfl
theorem value1260 (q : Snake 81) : valuation q 1260 = decide (2 ≤ count1259 (baseVal q)) := rfl
theorem value1261 (q : Snake 81) : valuation q 1261 = decide (3 ≤ count1259 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (1 ≤ count1262 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (2 ≤ count1262 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (1 ≤ count1264 (baseVal q)) := rfl
theorem value1265 (q : Snake 81) : valuation q 1265 = decide (2 ≤ count1264 (baseVal q)) := rfl
theorem value1266 (q : Snake 81) : valuation q 1266 = decide (3 ≤ count1264 (baseVal q)) := rfl
theorem value1267 (q : Snake 81) : valuation q 1267 = decide (1 ≤ count1267 (baseVal q)) := rfl
theorem value1268 (q : Snake 81) : valuation q 1268 = decide (2 ≤ count1267 (baseVal q)) := rfl
theorem value1269 (q : Snake 81) : valuation q 1269 = decide (3 ≤ count1267 (baseVal q)) := rfl
theorem value1273 (q : Snake 81) : valuation q 1273 = decide (1 ≤ count1273 (baseVal q)) := rfl
theorem value1274 (q : Snake 81) : valuation q 1274 = decide (2 ≤ count1273 (baseVal q)) := rfl
theorem value1275 (q : Snake 81) : valuation q 1275 = decide (3 ≤ count1273 (baseVal q)) := rfl
theorem value1276 (q : Snake 81) : valuation q 1276 = decide (4 ≤ count1273 (baseVal q)) := rfl
theorem value1277 (q : Snake 81) : valuation q 1277 = decide (5 ≤ count1273 (baseVal q)) := rfl
theorem value1278 (q : Snake 81) : valuation q 1278 = decide (6 ≤ count1273 (baseVal q)) := rfl
theorem value1283 (q : Snake 81) : valuation q 1283 = decide (1 ≤ count1283 (baseVal q)) := rfl
theorem value1284 (q : Snake 81) : valuation q 1284 = decide (2 ≤ count1283 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (1 ≤ count1285 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (2 ≤ count1285 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (1 ≤ count1288 (baseVal q)) := rfl
theorem value1289 (q : Snake 81) : valuation q 1289 = decide (2 ≤ count1288 (baseVal q)) := rfl
theorem value1290 (q : Snake 81) : valuation q 1290 = decide (1 ≤ count1290 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (2 ≤ count1290 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (1 ≤ count1293 (baseVal q)) := rfl
theorem value1294 (q : Snake 81) : valuation q 1294 = decide (2 ≤ count1293 (baseVal q)) := rfl
theorem value1299 (q : Snake 81) : valuation q 1299 = decide (1 ≤ count1299 (baseVal q)) := rfl
theorem value1300 (q : Snake 81) : valuation q 1300 = decide (2 ≤ count1299 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (1 ≤ count1301 (baseVal q)) := rfl
theorem value1302 (q : Snake 81) : valuation q 1302 = decide (2 ≤ count1301 (baseVal q)) := rfl
theorem value1304 (q : Snake 81) : valuation q 1304 = decide (1 ≤ count1304 (baseVal q)) := rfl
theorem value1305 (q : Snake 81) : valuation q 1305 = decide (2 ≤ count1304 (baseVal q)) := rfl
theorem value1306 (q : Snake 81) : valuation q 1306 = decide (1 ≤ count1306 (baseVal q)) := rfl
theorem value1308 (q : Snake 81) : valuation q 1308 = decide (1 ≤ count1308 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (2 ≤ count1308 (baseVal q)) := rfl
theorem value1310 (q : Snake 81) : valuation q 1310 = decide (3 ≤ count1308 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (1 ≤ count1312 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (2 ≤ count1312 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (3 ≤ count1312 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (1 ≤ count1319 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (2 ≤ count1319 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (3 ≤ count1319 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (4 ≤ count1319 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (2 ≤ count1329 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (3 ≤ count1329 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (4 ≤ count1329 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (5 ≤ count1329 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (6 ≤ count1329 (baseVal q)) := rfl
theorem value1335 (q : Snake 81) : valuation q 1335 = decide (7 ≤ count1329 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (1 ≤ count1339 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (1 ≤ count1341 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (1 ≤ count1344 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (1 ≤ count1346 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (2 ≤ count1346 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (2 ≤ count1349 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (3 ≤ count1349 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (1 ≤ count1355 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (2 ≤ count1355 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (1 ≤ count1357 (baseVal q)) := rfl
theorem value1358 (q : Snake 81) : valuation q 1358 = decide (2 ≤ count1357 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (1 ≤ count1360 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (2 ≤ count1360 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (1 ≤ count1362 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (2 ≤ count1362 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (1 ≤ count1365 (baseVal q)) := rfl
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (2 ≤ count1365 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (3 ≤ count1365 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (1 ≤ count1371 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (2 ≤ count1371 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (3 ≤ count1371 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (4 ≤ count1371 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (1 ≤ count1381 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (2 ≤ count1381 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (1 ≤ count1383 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (2 ≤ count1383 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (3 ≤ count1383 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (1 ≤ count1386 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (2 ≤ count1386 (baseVal q)) := rfl
theorem value1388 (q : Snake 81) : valuation q 1388 = decide (1 ≤ count1388 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (2 ≤ count1388 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (1 ≤ count1391 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (2 ≤ count1391 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (3 ≤ count1391 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (4 ≤ count1391 (baseVal q)) := rfl
theorem value1397 (q : Snake 81) : valuation q 1397 = decide (1 ≤ count1397 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (1 ≤ count1399 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (2 ≤ count1399 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (1 ≤ count1402 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (2 ≤ count1402 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (1 ≤ count1404 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (2 ≤ count1404 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (1 ≤ count1406 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (2 ≤ count1406 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (1 ≤ count1410 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (2 ≤ count1410 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (3 ≤ count1410 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (1 ≤ count1417 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (2 ≤ count1417 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (3 ≤ count1417 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (4 ≤ count1417 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (5 ≤ count1417 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (3 ≤ count1427 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (4 ≤ count1427 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (5 ≤ count1427 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (6 ≤ count1427 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (7 ≤ count1427 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (8 ≤ count1427 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (10 ≤ count1437 (baseVal q)) := rfl
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
theorem meaningNeg90 (b : Nat → Bool) : literal (valuationOf b) (-90) = decide (1 ≤ countLit b [-90]) := by
  change literal b (-90) = decide (1 ≤ countLit b [-90])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-90) <;> decide
theorem meaningNeg87 (b : Nat → Bool) : literal (valuationOf b) (-87) = decide (1 ≤ countLit b [-87]) := by
  change literal b (-87) = decide (1 ≤ countLit b [-87])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-87) <;> decide
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
theorem meaningNeg32 (b : Nat → Bool) : literal (valuationOf b) (-32) = decide (1 ≤ countLit b [-32]) := by
  change literal b (-32) = decide (1 ≤ countLit b [-32])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-32) <;> decide
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
theorem meaningNeg12 (b : Nat → Bool) : literal (valuationOf b) (-12) = decide (1 ≤ countLit b [-12]) := by
  change literal b (-12) = decide (1 ≤ countLit b [-12])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-12) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning106 (b : Nat → Bool) : literal (valuationOf b) (106) = decide (1 ≤ countLit b [106]) := by
  change literal b (106) = decide (1 ≤ countLit b [106])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (106) <;> decide
theorem meaning110 (b : Nat → Bool) : literal (valuationOf b) (110) = decide (1 ≤ countLit b [110]) := by
  change literal b (110) = decide (1 ≤ countLit b [110])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (110) <;> decide
theorem meaning111 (b : Nat → Bool) : literal (valuationOf b) (111) = decide (1 ≤ countLit b [111]) := by
  change literal b (111) = decide (1 ≤ countLit b [111])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (111) <;> decide
theorem meaning117 (b : Nat → Bool) : literal (valuationOf b) (117) = decide (1 ≤ countLit b [117]) := by
  change literal b (117) = decide (1 ≤ countLit b [117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (117) <;> decide
theorem meaning119 (b : Nat → Bool) : literal (valuationOf b) (119) = decide (1 ≤ countLit b [119]) := by
  change literal b (119) = decide (1 ≤ countLit b [119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (119) <;> decide
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
theorem meaning126 (b : Nat → Bool) : literal (valuationOf b) (126) = decide (1 ≤ countLit b [126]) := by
  change literal b (126) = decide (1 ≤ countLit b [126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (126) <;> decide
theorem meaning127 (b : Nat → Bool) : literal (valuationOf b) (127) = decide (1 ≤ countLit b [127]) := by
  change literal b (127) = decide (1 ≤ countLit b [127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (127) <;> decide
theorem meaning129 (b : Nat → Bool) : literal (valuationOf b) (129) = decide (1 ≤ countLit b [129]) := by
  change literal b (129) = decide (1 ≤ countLit b [129])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (129) <;> decide
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
theorem meaning137 (b : Nat → Bool) : literal (valuationOf b) (137) = decide (1 ≤ countLit b [137]) := by
  change literal b (137) = decide (1 ≤ countLit b [137])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (137) <;> decide
theorem meaning139 (b : Nat → Bool) : literal (valuationOf b) (139) = decide (1 ≤ countLit b [139]) := by
  change literal b (139) = decide (1 ≤ countLit b [139])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (139) <;> decide
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
theorem meaning148 (b : Nat → Bool) : literal (valuationOf b) (148) = decide (1 ≤ countLit b [148]) := by
  change literal b (148) = decide (1 ≤ countLit b [148])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (148) <;> decide
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
theorem meaning157 (b : Nat → Bool) : literal (valuationOf b) (157) = decide (1 ≤ countLit b [157]) := by
  change literal b (157) = decide (1 ≤ countLit b [157])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (157) <;> decide
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
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
theorem meaning165 (b : Nat → Bool) : literal (valuationOf b) (165) = decide (1 ≤ countLit b [165]) := by
  change literal b (165) = decide (1 ≤ countLit b [165])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (165) <;> decide
theorem meaning166 (b : Nat → Bool) : literal (valuationOf b) (166) = decide (1 ≤ countLit b [166]) := by
  change literal b (166) = decide (1 ≤ countLit b [166])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (166) <;> decide
theorem meaning168 (b : Nat → Bool) : literal (valuationOf b) (168) = decide (1 ≤ countLit b [168]) := by
  change literal b (168) = decide (1 ≤ countLit b [168])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (168) <;> decide
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
theorem meaning175 (b : Nat → Bool) : literal (valuationOf b) (175) = decide (1 ≤ countLit b [175]) := by
  change literal b (175) = decide (1 ≤ countLit b [175])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (175) <;> decide
theorem meaning179 (b : Nat → Bool) : literal (valuationOf b) (179) = decide (1 ≤ countLit b [179]) := by
  change literal b (179) = decide (1 ≤ countLit b [179])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (179) <;> decide
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
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
theorem meaning189 (b : Nat → Bool) : literal (valuationOf b) (189) = decide (1 ≤ countLit b [189]) := by
  change literal b (189) = decide (1 ≤ countLit b [189])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (189) <;> decide
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
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) 209 = decide (1 ≤ count209 b) := rfl
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) 211 = decide (1 ≤ count211 b) := rfl
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) 213 = decide (1 ≤ count213 b) := rfl
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) 215 = decide (1 ≤ count215 b) := rfl
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) 217 = decide (1 ≤ count217 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) 230 = decide (2 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning250 (b : Nat → Bool) : literal (valuationOf b) 250 = decide (2 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) 252 = decide (2 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning276 (b : Nat → Bool) : literal (valuationOf b) 276 = decide (2 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning278 (b : Nat → Bool) : literal (valuationOf b) 278 = decide (2 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning288 (b : Nat → Bool) : literal (valuationOf b) 288 = decide (2 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning332 (b : Nat → Bool) : literal (valuationOf b) 332 = decide (2 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning338 (b : Nat → Bool) : literal (valuationOf b) 338 = decide (2 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning352 (b : Nat → Bool) : literal (valuationOf b) 352 = decide (2 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning356 (b : Nat → Bool) : literal (valuationOf b) 356 = decide (2 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning382 (b : Nat → Bool) : literal (valuationOf b) 382 = decide (2 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning408 (b : Nat → Bool) : literal (valuationOf b) 408 = decide (2 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning715 (b : Nat → Bool) : literal (valuationOf b) 715 = decide (1 ≤ count715 b) := rfl
theorem meaning717 (b : Nat → Bool) : literal (valuationOf b) 717 = decide (1 ≤ count717 b) := rfl
theorem meaning718 (b : Nat → Bool) : literal (valuationOf b) 718 = decide (2 ≤ count717 b) := rfl
theorem meaning720 (b : Nat → Bool) : literal (valuationOf b) 720 = decide (1 ≤ count720 b) := rfl
theorem meaning722 (b : Nat → Bool) : literal (valuationOf b) 722 = decide (1 ≤ count722 b) := rfl
theorem meaning725 (b : Nat → Bool) : literal (valuationOf b) 725 = decide (1 ≤ count725 b) := rfl
theorem meaning726 (b : Nat → Bool) : literal (valuationOf b) 726 = decide (2 ≤ count725 b) := rfl
theorem meaning727 (b : Nat → Bool) : literal (valuationOf b) 727 = decide (3 ≤ count725 b) := rfl
theorem meaning731 (b : Nat → Bool) : literal (valuationOf b) 731 = decide (1 ≤ count731 b) := rfl
theorem meaning732 (b : Nat → Bool) : literal (valuationOf b) 732 = decide (2 ≤ count731 b) := rfl
theorem meaning733 (b : Nat → Bool) : literal (valuationOf b) 733 = decide (1 ≤ count733 b) := rfl
theorem meaning734 (b : Nat → Bool) : literal (valuationOf b) 734 = decide (2 ≤ count733 b) := rfl
theorem meaning735 (b : Nat → Bool) : literal (valuationOf b) 735 = decide (3 ≤ count733 b) := rfl
theorem meaning736 (b : Nat → Bool) : literal (valuationOf b) 736 = decide (1 ≤ count736 b) := rfl
theorem meaning737 (b : Nat → Bool) : literal (valuationOf b) 737 = decide (2 ≤ count736 b) := rfl
theorem meaning738 (b : Nat → Bool) : literal (valuationOf b) 738 = decide (1 ≤ count738 b) := rfl
theorem meaning739 (b : Nat → Bool) : literal (valuationOf b) 739 = decide (2 ≤ count738 b) := rfl
theorem meaning742 (b : Nat → Bool) : literal (valuationOf b) 742 = decide (3 ≤ count740 b) := rfl
theorem meaning743 (b : Nat → Bool) : literal (valuationOf b) 743 = decide (4 ≤ count740 b) := rfl
theorem meaning748 (b : Nat → Bool) : literal (valuationOf b) 748 = decide (5 ≤ count744 b) := rfl
theorem meaning749 (b : Nat → Bool) : literal (valuationOf b) 749 = decide (6 ≤ count744 b) := rfl
theorem meaning757 (b : Nat → Bool) : literal (valuationOf b) 757 = decide (7 ≤ count751 b) := rfl
theorem meaning758 (b : Nat → Bool) : literal (valuationOf b) 758 = decide (8 ≤ count751 b) := rfl
theorem meaning764 (b : Nat → Bool) : literal (valuationOf b) 764 = decide (1 ≤ count764 b) := rfl
theorem meaning766 (b : Nat → Bool) : literal (valuationOf b) 766 = decide (1 ≤ count766 b) := rfl
theorem meaning767 (b : Nat → Bool) : literal (valuationOf b) 767 = decide (2 ≤ count766 b) := rfl
theorem meaning769 (b : Nat → Bool) : literal (valuationOf b) 769 = decide (1 ≤ count769 b) := rfl
theorem meaning771 (b : Nat → Bool) : literal (valuationOf b) 771 = decide (1 ≤ count771 b) := rfl
theorem meaning773 (b : Nat → Bool) : literal (valuationOf b) 773 = decide (1 ≤ count773 b) := rfl
theorem meaning774 (b : Nat → Bool) : literal (valuationOf b) 774 = decide (2 ≤ count773 b) := rfl
theorem meaning777 (b : Nat → Bool) : literal (valuationOf b) 777 = decide (1 ≤ count777 b) := rfl
theorem meaning778 (b : Nat → Bool) : literal (valuationOf b) 778 = decide (2 ≤ count777 b) := rfl
theorem meaning779 (b : Nat → Bool) : literal (valuationOf b) 779 = decide (3 ≤ count777 b) := rfl
theorem meaning784 (b : Nat → Bool) : literal (valuationOf b) 784 = decide (1 ≤ count784 b) := rfl
theorem meaning786 (b : Nat → Bool) : literal (valuationOf b) 786 = decide (1 ≤ count786 b) := rfl
theorem meaning789 (b : Nat → Bool) : literal (valuationOf b) 789 = decide (1 ≤ count789 b) := rfl
theorem meaning793 (b : Nat → Bool) : literal (valuationOf b) 793 = decide (1 ≤ count793 b) := rfl
theorem meaning798 (b : Nat → Bool) : literal (valuationOf b) 798 = decide (2 ≤ count797 b) := rfl
theorem meaning806 (b : Nat → Bool) : literal (valuationOf b) 806 = decide (3 ≤ count804 b) := rfl
theorem meaning807 (b : Nat → Bool) : literal (valuationOf b) 807 = decide (4 ≤ count804 b) := rfl
theorem meaning808 (b : Nat → Bool) : literal (valuationOf b) 808 = decide (5 ≤ count804 b) := rfl
theorem meaning827 (b : Nat → Bool) : literal (valuationOf b) 827 = decide (10 ≤ count818 b) := rfl
theorem meaning828 (b : Nat → Bool) : literal (valuationOf b) 828 = decide (11 ≤ count818 b) := rfl
theorem meaning829 (b : Nat → Bool) : literal (valuationOf b) 829 = decide (12 ≤ count818 b) := rfl
theorem meaning839 (b : Nat → Bool) : literal (valuationOf b) 839 = decide (1 ≤ count839 b) := rfl
theorem meaning842 (b : Nat → Bool) : literal (valuationOf b) 842 = decide (1 ≤ count842 b) := rfl
theorem meaning855 (b : Nat → Bool) : literal (valuationOf b) 855 = decide (1 ≤ count855 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (1 ≤ count857 b) := rfl
theorem meaning861 (b : Nat → Bool) : literal (valuationOf b) 861 = decide (1 ≤ count861 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (1 ≤ count868 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (2 ≤ count868 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (1 ≤ count883 b) := rfl
theorem meaning886 (b : Nat → Bool) : literal (valuationOf b) 886 = decide (1 ≤ count886 b) := rfl
theorem meaning890 (b : Nat → Bool) : literal (valuationOf b) 890 = decide (1 ≤ count890 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (2 ≤ count894 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (2 ≤ count921 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (2 ≤ count935 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (3 ≤ count935 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (4 ≤ count935 b) := rfl
theorem meaning962 (b : Nat → Bool) : literal (valuationOf b) 962 = decide (14 ≤ count949 b) := rfl
theorem meaning1241 (b : Nat → Bool) : literal (valuationOf b) 1241 = decide (1 ≤ count1241 b) := rfl
theorem meaning1242 (b : Nat → Bool) : literal (valuationOf b) 1242 = decide (2 ≤ count1241 b) := rfl
theorem meaning1243 (b : Nat → Bool) : literal (valuationOf b) 1243 = decide (1 ≤ count1243 b) := rfl
theorem meaning1244 (b : Nat → Bool) : literal (valuationOf b) 1244 = decide (2 ≤ count1243 b) := rfl
theorem meaning1245 (b : Nat → Bool) : literal (valuationOf b) 1245 = decide (3 ≤ count1243 b) := rfl
theorem meaning1246 (b : Nat → Bool) : literal (valuationOf b) 1246 = decide (1 ≤ count1246 b) := rfl
theorem meaning1247 (b : Nat → Bool) : literal (valuationOf b) 1247 = decide (2 ≤ count1246 b) := rfl
theorem meaning1248 (b : Nat → Bool) : literal (valuationOf b) 1248 = decide (1 ≤ count1248 b) := rfl
theorem meaning1249 (b : Nat → Bool) : literal (valuationOf b) 1249 = decide (2 ≤ count1248 b) := rfl
theorem meaning1250 (b : Nat → Bool) : literal (valuationOf b) 1250 = decide (3 ≤ count1248 b) := rfl
theorem meaning1251 (b : Nat → Bool) : literal (valuationOf b) 1251 = decide (1 ≤ count1251 b) := rfl
theorem meaning1252 (b : Nat → Bool) : literal (valuationOf b) 1252 = decide (2 ≤ count1251 b) := rfl
theorem meaning1253 (b : Nat → Bool) : literal (valuationOf b) 1253 = decide (3 ≤ count1251 b) := rfl
theorem meaning1254 (b : Nat → Bool) : literal (valuationOf b) 1254 = decide (4 ≤ count1251 b) := rfl
theorem meaning1255 (b : Nat → Bool) : literal (valuationOf b) 1255 = decide (5 ≤ count1251 b) := rfl
theorem meaning1257 (b : Nat → Bool) : literal (valuationOf b) 1257 = decide (1 ≤ count1257 b) := rfl
theorem meaning1258 (b : Nat → Bool) : literal (valuationOf b) 1258 = decide (2 ≤ count1257 b) := rfl
theorem meaning1259 (b : Nat → Bool) : literal (valuationOf b) 1259 = decide (1 ≤ count1259 b) := rfl
theorem meaning1260 (b : Nat → Bool) : literal (valuationOf b) 1260 = decide (2 ≤ count1259 b) := rfl
theorem meaning1261 (b : Nat → Bool) : literal (valuationOf b) 1261 = decide (3 ≤ count1259 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (1 ≤ count1262 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (2 ≤ count1262 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (1 ≤ count1264 b) := rfl
theorem meaning1265 (b : Nat → Bool) : literal (valuationOf b) 1265 = decide (2 ≤ count1264 b) := rfl
theorem meaning1266 (b : Nat → Bool) : literal (valuationOf b) 1266 = decide (3 ≤ count1264 b) := rfl
theorem meaning1267 (b : Nat → Bool) : literal (valuationOf b) 1267 = decide (1 ≤ count1267 b) := rfl
theorem meaning1268 (b : Nat → Bool) : literal (valuationOf b) 1268 = decide (2 ≤ count1267 b) := rfl
theorem meaning1269 (b : Nat → Bool) : literal (valuationOf b) 1269 = decide (3 ≤ count1267 b) := rfl
theorem meaning1273 (b : Nat → Bool) : literal (valuationOf b) 1273 = decide (1 ≤ count1273 b) := rfl
theorem meaning1274 (b : Nat → Bool) : literal (valuationOf b) 1274 = decide (2 ≤ count1273 b) := rfl
theorem meaning1275 (b : Nat → Bool) : literal (valuationOf b) 1275 = decide (3 ≤ count1273 b) := rfl
theorem meaning1276 (b : Nat → Bool) : literal (valuationOf b) 1276 = decide (4 ≤ count1273 b) := rfl
theorem meaning1277 (b : Nat → Bool) : literal (valuationOf b) 1277 = decide (5 ≤ count1273 b) := rfl
theorem meaning1278 (b : Nat → Bool) : literal (valuationOf b) 1278 = decide (6 ≤ count1273 b) := rfl
theorem meaning1283 (b : Nat → Bool) : literal (valuationOf b) 1283 = decide (1 ≤ count1283 b) := rfl
theorem meaning1284 (b : Nat → Bool) : literal (valuationOf b) 1284 = decide (2 ≤ count1283 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (1 ≤ count1285 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (2 ≤ count1285 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (1 ≤ count1288 b) := rfl
theorem meaning1289 (b : Nat → Bool) : literal (valuationOf b) 1289 = decide (2 ≤ count1288 b) := rfl
theorem meaning1290 (b : Nat → Bool) : literal (valuationOf b) 1290 = decide (1 ≤ count1290 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (2 ≤ count1290 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (1 ≤ count1293 b) := rfl
theorem meaning1294 (b : Nat → Bool) : literal (valuationOf b) 1294 = decide (2 ≤ count1293 b) := rfl
theorem meaning1299 (b : Nat → Bool) : literal (valuationOf b) 1299 = decide (1 ≤ count1299 b) := rfl
theorem meaning1300 (b : Nat → Bool) : literal (valuationOf b) 1300 = decide (2 ≤ count1299 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (1 ≤ count1301 b) := rfl
theorem meaning1302 (b : Nat → Bool) : literal (valuationOf b) 1302 = decide (2 ≤ count1301 b) := rfl
theorem meaning1304 (b : Nat → Bool) : literal (valuationOf b) 1304 = decide (1 ≤ count1304 b) := rfl
theorem meaning1305 (b : Nat → Bool) : literal (valuationOf b) 1305 = decide (2 ≤ count1304 b) := rfl
theorem meaning1306 (b : Nat → Bool) : literal (valuationOf b) 1306 = decide (1 ≤ count1306 b) := rfl
theorem meaning1308 (b : Nat → Bool) : literal (valuationOf b) 1308 = decide (1 ≤ count1308 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (2 ≤ count1308 b) := rfl
theorem meaning1310 (b : Nat → Bool) : literal (valuationOf b) 1310 = decide (3 ≤ count1308 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (1 ≤ count1312 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (2 ≤ count1312 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (3 ≤ count1312 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (1 ≤ count1319 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (2 ≤ count1319 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (3 ≤ count1319 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (4 ≤ count1319 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (2 ≤ count1329 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (3 ≤ count1329 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (4 ≤ count1329 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (5 ≤ count1329 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (6 ≤ count1329 b) := rfl
theorem meaning1335 (b : Nat → Bool) : literal (valuationOf b) 1335 = decide (7 ≤ count1329 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (1 ≤ count1339 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (1 ≤ count1341 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (1 ≤ count1344 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (1 ≤ count1346 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (2 ≤ count1346 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (2 ≤ count1349 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (3 ≤ count1349 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (1 ≤ count1355 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (2 ≤ count1355 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (1 ≤ count1357 b) := rfl
theorem meaning1358 (b : Nat → Bool) : literal (valuationOf b) 1358 = decide (2 ≤ count1357 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (1 ≤ count1360 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (2 ≤ count1360 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (1 ≤ count1362 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (2 ≤ count1362 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (1 ≤ count1365 b) := rfl
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (2 ≤ count1365 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (3 ≤ count1365 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (1 ≤ count1371 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (2 ≤ count1371 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (3 ≤ count1371 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (4 ≤ count1371 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (1 ≤ count1381 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (2 ≤ count1381 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (1 ≤ count1383 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (2 ≤ count1383 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (3 ≤ count1383 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (1 ≤ count1386 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (2 ≤ count1386 b) := rfl
theorem meaning1388 (b : Nat → Bool) : literal (valuationOf b) 1388 = decide (1 ≤ count1388 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (2 ≤ count1388 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (1 ≤ count1391 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (2 ≤ count1391 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (3 ≤ count1391 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (4 ≤ count1391 b) := rfl
theorem meaning1397 (b : Nat → Bool) : literal (valuationOf b) 1397 = decide (1 ≤ count1397 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (1 ≤ count1399 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (2 ≤ count1399 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (1 ≤ count1402 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (2 ≤ count1402 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (1 ≤ count1404 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (2 ≤ count1404 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (1 ≤ count1406 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (2 ≤ count1406 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (1 ≤ count1410 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (2 ≤ count1410 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (3 ≤ count1410 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (1 ≤ count1417 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (2 ≤ count1417 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (3 ≤ count1417 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (4 ≤ count1417 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (5 ≤ count1417 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (3 ≤ count1427 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (4 ≤ count1427 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (5 ≤ count1427 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (6 ≤ count1427 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (7 ≤ count1427 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (8 ≤ count1427 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (10 ≤ count1437 b) := rfl
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
end Snake9.Regrowth.E112175
