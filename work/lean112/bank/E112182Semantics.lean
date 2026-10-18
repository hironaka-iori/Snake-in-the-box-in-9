import E112182Data
namespace Snake9.Regrowth.E112182
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 102 then (if i < 51 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (34 : Vertex)) else decide (InPath q (36 : Vertex)))) else (if i < 4 then decide (InPath q (39 : Vertex)) else (if i < 5 then decide (InPath q (40 : Vertex)) else decide (InPath q (41 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (42 : Vertex)) else (if i < 8 then decide (InPath q (44 : Vertex)) else decide (InPath q (46 : Vertex)))) else (if i < 10 then decide (InPath q (52 : Vertex)) else (if i < 11 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex)))))) else (if i < 18 then (if i < 15 then (if i < 13 then decide (InPath q (57 : Vertex)) else (if i < 14 then decide (InPath q (58 : Vertex)) else decide (InPath q (59 : Vertex)))) else (if i < 16 then decide (InPath q (63 : Vertex)) else (if i < 17 then decide (InPath q (96 : Vertex)) else decide (InPath q (97 : Vertex))))) else (if i < 21 then (if i < 19 then decide (InPath q (102 : Vertex)) else (if i < 20 then decide (InPath q (103 : Vertex)) else decide (InPath q (104 : Vertex)))) else (if i < 23 then (if i < 22 then decide (InPath q (105 : Vertex)) else decide (InPath q (109 : Vertex))) else (if i < 24 then decide (InPath q (111 : Vertex)) else decide (InPath q (113 : Vertex))))))) else (if i < 38 then (if i < 31 then (if i < 28 then (if i < 26 then decide (InPath q (114 : Vertex)) else (if i < 27 then decide (InPath q (115 : Vertex)) else decide (InPath q (118 : Vertex)))) else (if i < 29 then decide (InPath q (122 : Vertex)) else (if i < 30 then decide (InPath q (124 : Vertex)) else decide (InPath q (125 : Vertex))))) else (if i < 34 then (if i < 32 then decide (InPath q (126 : Vertex)) else (if i < 33 then decide (InPath q (130 : Vertex)) else decide (InPath q (132 : Vertex)))) else (if i < 36 then (if i < 35 then decide (InPath q (135 : Vertex)) else decide (InPath q (136 : Vertex))) else (if i < 37 then decide (InPath q (137 : Vertex)) else decide (InPath q (138 : Vertex)))))) else (if i < 44 then (if i < 41 then (if i < 39 then decide (InPath q (140 : Vertex)) else (if i < 40 then decide (InPath q (142 : Vertex)) else decide (InPath q (148 : Vertex)))) else (if i < 42 then decide (InPath q (149 : Vertex)) else (if i < 43 then decide (InPath q (151 : Vertex)) else decide (InPath q (153 : Vertex))))) else (if i < 47 then (if i < 45 then decide (InPath q (154 : Vertex)) else (if i < 46 then decide (InPath q (155 : Vertex)) else decide (InPath q (159 : Vertex)))) else (if i < 49 then (if i < 48 then decide (InPath q (198 : Vertex)) else decide (InPath q (200 : Vertex))) else (if i < 50 then decide (InPath q (201 : Vertex)) else decide (InPath q (205 : Vertex)))))))) else (if i < 76 then (if i < 63 then (if i < 57 then (if i < 54 then (if i < 52 then decide (InPath q (207 : Vertex)) else (if i < 53 then decide (InPath q (214 : Vertex)) else decide (InPath q (218 : Vertex)))) else (if i < 55 then decide (InPath q (220 : Vertex)) else (if i < 56 then decide (InPath q (221 : Vertex)) else decide (InPath q (222 : Vertex))))) else (if i < 60 then (if i < 58 then decide (InPath q (226 : Vertex)) else (if i < 59 then decide (InPath q (230 : Vertex)) else decide (InPath q (232 : Vertex)))) else (if i < 61 then decide (InPath q (236 : Vertex)) else (if i < 62 then decide (InPath q (238 : Vertex)) else decide (InPath q (264 : Vertex)))))) else (if i < 69 then (if i < 66 then (if i < 64 then decide (InPath q (268 : Vertex)) else (if i < 65 then decide (InPath q (296 : Vertex)) else decide (InPath q (297 : Vertex)))) else (if i < 67 then decide (InPath q (301 : Vertex)) else (if i < 68 then decide (InPath q (303 : Vertex)) else decide (InPath q (310 : Vertex))))) else (if i < 72 then (if i < 70 then decide (InPath q (316 : Vertex)) else (if i < 71 then decide (InPath q (317 : Vertex)) else decide (InPath q (318 : Vertex)))) else (if i < 74 then (if i < 73 then decide (InPath q (384 : Vertex)) else decide (InPath q (385 : Vertex))) else (if i < 75 then decide (InPath q (391 : Vertex)) else decide (InPath q (392 : Vertex))))))) else (if i < 89 then (if i < 82 then (if i < 79 then (if i < 77 then decide (InPath q (393 : Vertex)) else (if i < 78 then decide (InPath q (397 : Vertex)) else decide (InPath q (399 : Vertex)))) else (if i < 80 then decide (InPath q (401 : Vertex)) else (if i < 81 then decide (InPath q (402 : Vertex)) else decide (InPath q (403 : Vertex))))) else (if i < 85 then (if i < 83 then decide (InPath q (406 : Vertex)) else (if i < 84 then decide (InPath q (410 : Vertex)) else decide (InPath q (412 : Vertex)))) else (if i < 87 then (if i < 86 then decide (InPath q (413 : Vertex)) else decide (InPath q (414 : Vertex))) else (if i < 88 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex)))))) else (if i < 95 then (if i < 92 then (if i < 90 then decide (InPath q (486 : Vertex)) else (if i < 91 then decide (InPath q (487 : Vertex)) else decide (InPath q (488 : Vertex)))) else (if i < 93 then decide (InPath q (489 : Vertex)) else (if i < 94 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 98 then (if i < 96 then decide (InPath q (497 : Vertex)) else (if i < 97 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 100 then (if i < 99 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 101 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 153 then (if i < 127 then (if i < 114 then (if i < 108 then (if i < 105 then (if i < 103 then decide (InPath q (510 : Vertex)) else (if i < 104 then decide (BallClauseLogic.Endpoint q (34 : Vertex)) else decide (BallClauseLogic.Endpoint q (36 : Vertex)))) else (if i < 106 then decide (BallClauseLogic.Endpoint q (39 : Vertex)) else (if i < 107 then decide (BallClauseLogic.Endpoint q (40 : Vertex)) else decide (BallClauseLogic.Endpoint q (41 : Vertex))))) else (if i < 111 then (if i < 109 then decide (BallClauseLogic.Endpoint q (42 : Vertex)) else (if i < 110 then decide (BallClauseLogic.Endpoint q (44 : Vertex)) else decide (BallClauseLogic.Endpoint q (46 : Vertex)))) else (if i < 112 then decide (BallClauseLogic.Endpoint q (52 : Vertex)) else (if i < 113 then decide (BallClauseLogic.Endpoint q (53 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex)))))) else (if i < 120 then (if i < 117 then (if i < 115 then decide (BallClauseLogic.Endpoint q (57 : Vertex)) else (if i < 116 then decide (BallClauseLogic.Endpoint q (58 : Vertex)) else decide (BallClauseLogic.Endpoint q (59 : Vertex)))) else (if i < 118 then decide (BallClauseLogic.Endpoint q (63 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (96 : Vertex)) else decide (BallClauseLogic.Endpoint q (97 : Vertex))))) else (if i < 123 then (if i < 121 then decide (BallClauseLogic.Endpoint q (102 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (104 : Vertex)))) else (if i < 125 then (if i < 124 then decide (BallClauseLogic.Endpoint q (105 : Vertex)) else decide (BallClauseLogic.Endpoint q (109 : Vertex))) else (if i < 126 then decide (BallClauseLogic.Endpoint q (111 : Vertex)) else decide (BallClauseLogic.Endpoint q (113 : Vertex))))))) else (if i < 140 then (if i < 133 then (if i < 130 then (if i < 128 then decide (BallClauseLogic.Endpoint q (114 : Vertex)) else (if i < 129 then decide (BallClauseLogic.Endpoint q (115 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex)))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (122 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (124 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex))))) else (if i < 136 then (if i < 134 then decide (BallClauseLogic.Endpoint q (126 : Vertex)) else (if i < 135 then decide (BallClauseLogic.Endpoint q (130 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex)))) else (if i < 138 then (if i < 137 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex))) else (if i < 139 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (138 : Vertex)))))) else (if i < 146 then (if i < 143 then (if i < 141 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else (if i < 142 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex)))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (153 : Vertex))))) else (if i < 149 then (if i < 147 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex)))) else (if i < 151 then (if i < 150 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (200 : Vertex))) else (if i < 152 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex)))))))) else (if i < 179 then (if i < 166 then (if i < 159 then (if i < 156 then (if i < 154 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else (if i < 155 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex)))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else decide (BallClauseLogic.Endpoint q (222 : Vertex))))) else (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (230 : Vertex)) else decide (BallClauseLogic.Endpoint q (232 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else decide (BallClauseLogic.Endpoint q (238 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex)))))) else (if i < 172 then (if i < 169 then (if i < 167 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else (if i < 168 then decide (BallClauseLogic.Endpoint q (297 : Vertex)) else decide (BallClauseLogic.Endpoint q (301 : Vertex)))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (303 : Vertex)) else (if i < 171 then decide (BallClauseLogic.Endpoint q (310 : Vertex)) else decide (BallClauseLogic.Endpoint q (316 : Vertex))))) else (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (318 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (391 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (392 : Vertex)) else decide (BallClauseLogic.Endpoint q (393 : Vertex))))))) else (if i < 192 then (if i < 185 then (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (399 : Vertex)) else decide (BallClauseLogic.Endpoint q (401 : Vertex)))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (406 : Vertex))))) else (if i < 188 then (if i < 186 then decide (BallClauseLogic.Endpoint q (410 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else decide (BallClauseLogic.Endpoint q (480 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (481 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex)))))) else (if i < 198 then (if i < 195 then (if i < 193 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else (if i < 194 then decide (BallClauseLogic.Endpoint q (488 : Vertex)) else decide (BallClauseLogic.Endpoint q (489 : Vertex)))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 201 then (if i < 199 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else (if i < 200 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count205 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count207 (b : Nat → Bool) : Nat := countLit b [103, 104, 105]
def count209 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count211 (b : Nat → Bool) : Nat := countLit b [106, 107, 108]
def count213 (b : Nat → Bool) : Nat := countLit b [103, 104, 105, 106, 107, 108]
def count215 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count217 (b : Nat → Bool) : Nat := countLit b [109, 110, 111]
def count219 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count221 (b : Nat → Bool) : Nat := countLit b [112, 113, 114]
def count223 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114]
def count225 (b : Nat → Bool) : Nat := countLit b [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114]
def count227 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [115, 116, 117]
def count231 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count233 (b : Nat → Bool) : Nat := countLit b [118, 119, 120]
def count235 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120]
def count237 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count239 (b : Nat → Bool) : Nat := countLit b [121, 122, 123]
def count241 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count243 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count245 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124, 125, 126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]
def count253 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [134, 135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count269 (b : Nat → Bool) : Nat := countLit b [137, 138, 139]
def count271 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137, 138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count281 (b : Nat → Bool) : Nat := countLit b [143, 144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count291 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count303 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [162, 163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 171]
def count331 (b : Nat → Bool) : Nat := countLit b [168, 169, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count337 (b : Nat → Bool) : Nat := countLit b [172, 173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count341 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count343 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [179, 180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [185, 186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count367 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count377 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196, 197]
def count383 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count387 (b : Nat → Bool) : Nat := countLit b [198, 199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count391 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count395 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count403 (b : Nat → Bool) : Nat := countLit b [103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count405 (b : Nat → Bool) : Nat := countLit b [2, 3]
def count407 (b : Nat → Bool) : Nat := countLit b [1, 2, 3]
def count410 (b : Nat → Bool) : Nat := countLit b [8, 10]
def count412 (b : Nat → Bool) : Nat := countLit b [4, 8, 10]
def count415 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 4, 8, 10]
def count421 (b : Nat → Bool) : Nat := countLit b [13, 15]
def count423 (b : Nat → Bool) : Nat := countLit b [12, 13, 15]
def count426 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count428 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count430 (b : Nat → Bool) : Nat := countLit b [16, 18, 21, 23]
def count434 (b : Nat → Bool) : Nat := countLit b [12, 13, 15, 16, 18, 21, 23]
def count441 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 4, 8, 10, 12, 13, 15, 16, 18, 21, 23]
def count454 (b : Nat → Bool) : Nat := countLit b [25, 30]
def count456 (b : Nat → Bool) : Nat := countLit b [24, 25, 30]
def count459 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count461 (b : Nat → Bool) : Nat := countLit b [33, 34]
def count463 (b : Nat → Bool) : Nat := countLit b [31, 32, 33, 34]
def count467 (b : Nat → Bool) : Nat := countLit b [24, 25, 30, 31, 32, 33, 34]
def count474 (b : Nat → Bool) : Nat := countLit b [39, 41]
def count476 (b : Nat → Bool) : Nat := countLit b [35, 39, 41]
def count479 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count481 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count483 (b : Nat → Bool) : Nat := countLit b [43, 44, 46, 47]
def count487 (b : Nat → Bool) : Nat := countLit b [35, 39, 41, 43, 44, 46, 47]
def count494 (b : Nat → Bool) : Nat := countLit b [24, 25, 30, 31, 32, 33, 34, 35, 39, 41, 43, 44, 46, 47]
def count508 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 4, 8, 10, 12, 13, 15, 16, 18, 21, 23, 24, 25, 30, 31, 32, 33, 34, 35, 39, 41, 43, 44, 46, 47]
def count535 (b : Nat → Bool) : Nat := countLit b [51, 55]
def count537 (b : Nat → Bool) : Nat := countLit b [49, 51, 55]
def count540 (b : Nat → Bool) : Nat := countLit b [57, 59]
def count542 (b : Nat → Bool) : Nat := countLit b [56, 57, 59]
def count545 (b : Nat → Bool) : Nat := countLit b [49, 51, 55, 56, 57, 59]
def count551 (b : Nat → Bool) : Nat := countLit b [62, 65]
def count553 (b : Nat → Bool) : Nat := countLit b [61, 62, 65]
def count556 (b : Nat → Bool) : Nat := countLit b [67, 70]
def count558 (b : Nat → Bool) : Nat := countLit b [71, 72]
def count560 (b : Nat → Bool) : Nat := countLit b [67, 70, 71, 72]
def count564 (b : Nat → Bool) : Nat := countLit b [61, 62, 65, 67, 70, 71, 72]
def count571 (b : Nat → Bool) : Nat := countLit b [49, 51, 55, 56, 57, 59, 61, 62, 65, 67, 70, 71, 72]
def count584 (b : Nat → Bool) : Nat := countLit b [78, 79]
def count586 (b : Nat → Bool) : Nat := countLit b [76, 78, 79]
def count589 (b : Nat → Bool) : Nat := countLit b [80, 85]
def count591 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count593 (b : Nat → Bool) : Nat := countLit b [80, 85, 86, 87]
def count597 (b : Nat → Bool) : Nat := countLit b [76, 78, 79, 80, 85, 86, 87]
def count604 (b : Nat → Bool) : Nat := countLit b [92, 94]
def count606 (b : Nat → Bool) : Nat := countLit b [89, 92, 94]
def count609 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count611 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count613 (b : Nat → Bool) : Nat := countLit b [95, 96, 101, 102]
def count617 (b : Nat → Bool) : Nat := countLit b [89, 92, 94, 95, 96, 101, 102]
def count624 (b : Nat → Bool) : Nat := countLit b [76, 78, 79, 80, 85, 86, 87, 89, 92, 94, 95, 96, 101, 102]
def count638 (b : Nat → Bool) : Nat := countLit b [49, 51, 55, 56, 57, 59, 61, 62, 65, 67, 70, 71, 72, 76, 78, 79, 80, 85, 86, 87, 89, 92, 94, 95, 96, 101, 102]
def count665 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 4, 8, 10, 12, 13, 15, 16, 18, 21, 23, 24, 25, 30, 31, 32, 33, 34, 35, 39, 41, 43, 44, 46, 47, 49, 51, 55, 56, 57, 59, 61, 62, 65, 67, 70, 71, 72, 76, 78, 79, 80, 85, 86, 87, 89, 92, 94, 95, 96, 101, 102]
def count707 (b : Nat → Bool) : Nat := countLit b [-2, -3]
def count709 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3]
def count712 (b : Nat → Bool) : Nat := countLit b [-8, -10]
def count714 (b : Nat → Bool) : Nat := countLit b [-4, -8, -10]
def count717 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -4, -8, -10]
def count723 (b : Nat → Bool) : Nat := countLit b [-13, -15]
def count725 (b : Nat → Bool) : Nat := countLit b [-12, -13, -15]
def count728 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count730 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count732 (b : Nat → Bool) : Nat := countLit b [-16, -18, -21, -23]
def count736 (b : Nat → Bool) : Nat := countLit b [-12, -13, -15, -16, -18, -21, -23]
def count743 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -4, -8, -10, -12, -13, -15, -16, -18, -21, -23]
def count756 (b : Nat → Bool) : Nat := countLit b [-25, -30]
def count758 (b : Nat → Bool) : Nat := countLit b [-24, -25, -30]
def count761 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count763 (b : Nat → Bool) : Nat := countLit b [-33, -34]
def count765 (b : Nat → Bool) : Nat := countLit b [-31, -32, -33, -34]
def count769 (b : Nat → Bool) : Nat := countLit b [-24, -25, -30, -31, -32, -33, -34]
def count776 (b : Nat → Bool) : Nat := countLit b [-39, -41]
def count778 (b : Nat → Bool) : Nat := countLit b [-35, -39, -41]
def count781 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count783 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count785 (b : Nat → Bool) : Nat := countLit b [-43, -44, -46, -47]
def count789 (b : Nat → Bool) : Nat := countLit b [-35, -39, -41, -43, -44, -46, -47]
def count796 (b : Nat → Bool) : Nat := countLit b [-24, -25, -30, -31, -32, -33, -34, -35, -39, -41, -43, -44, -46, -47]
def count810 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -4, -8, -10, -12, -13, -15, -16, -18, -21, -23, -24, -25, -30, -31, -32, -33, -34, -35, -39, -41, -43, -44, -46, -47]
def count824 (b : Nat → Bool) : Nat := countLit b [-51, -55]
def count826 (b : Nat → Bool) : Nat := countLit b [-49, -51, -55]
def count829 (b : Nat → Bool) : Nat := countLit b [-57, -59]
def count831 (b : Nat → Bool) : Nat := countLit b [-56, -57, -59]
def count834 (b : Nat → Bool) : Nat := countLit b [-49, -51, -55, -56, -57, -59]
def count840 (b : Nat → Bool) : Nat := countLit b [-62, -65]
def count842 (b : Nat → Bool) : Nat := countLit b [-61, -62, -65]
def count845 (b : Nat → Bool) : Nat := countLit b [-67, -70]
def count847 (b : Nat → Bool) : Nat := countLit b [-71, -72]
def count849 (b : Nat → Bool) : Nat := countLit b [-67, -70, -71, -72]
def count853 (b : Nat → Bool) : Nat := countLit b [-61, -62, -65, -67, -70, -71, -72]
def count860 (b : Nat → Bool) : Nat := countLit b [-49, -51, -55, -56, -57, -59, -61, -62, -65, -67, -70, -71, -72]
def count873 (b : Nat → Bool) : Nat := countLit b [-78, -79]
def count875 (b : Nat → Bool) : Nat := countLit b [-76, -78, -79]
def count878 (b : Nat → Bool) : Nat := countLit b [-80, -85]
def count880 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count882 (b : Nat → Bool) : Nat := countLit b [-80, -85, -86, -87]
def count886 (b : Nat → Bool) : Nat := countLit b [-76, -78, -79, -80, -85, -86, -87]
def count893 (b : Nat → Bool) : Nat := countLit b [-92, -94]
def count895 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94]
def count898 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count900 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count902 (b : Nat → Bool) : Nat := countLit b [-95, -96, -101, -102]
def count906 (b : Nat → Bool) : Nat := countLit b [-89, -92, -94, -95, -96, -101, -102]
def count913 (b : Nat → Bool) : Nat := countLit b [-76, -78, -79, -80, -85, -86, -87, -89, -92, -94, -95, -96, -101, -102]
def count927 (b : Nat → Bool) : Nat := countLit b [-49, -51, -55, -56, -57, -59, -61, -62, -65, -67, -70, -71, -72, -76, -78, -79, -80, -85, -86, -87, -89, -92, -94, -95, -96, -101, -102]
def count941 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -4, -8, -10, -12, -13, -15, -16, -18, -21, -23, -24, -25, -30, -31, -32, -33, -34, -35, -39, -41, -43, -44, -46, -47, -49, -51, -55, -56, -57, -59, -61, -62, -65, -67, -70, -71, -72, -76, -78, -79, -80, -85, -86, -87, -89, -92, -94, -95, -96, -101, -102]
def count955 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count957 (b : Nat → Bool) : Nat := countLit b [5, 6, 7]
def count960 (b : Nat → Bool) : Nat := countLit b [11, 14]
def count962 (b : Nat → Bool) : Nat := countLit b [9, 11, 14]
def count965 (b : Nat → Bool) : Nat := countLit b [5, 6, 7, 9, 11, 14]
def count971 (b : Nat → Bool) : Nat := countLit b [19, 20]
def count973 (b : Nat → Bool) : Nat := countLit b [17, 19, 20]
def count976 (b : Nat → Bool) : Nat := countLit b [26, 27]
def count978 (b : Nat → Bool) : Nat := countLit b [22, 26, 27]
def count981 (b : Nat → Bool) : Nat := countLit b [17, 19, 20, 22, 26, 27]
def count987 (b : Nat → Bool) : Nat := countLit b [5, 6, 7, 9, 11, 14, 17, 19, 20, 22, 26, 27]
def count999 (b : Nat → Bool) : Nat := countLit b [29, 36]
def count1001 (b : Nat → Bool) : Nat := countLit b [28, 29, 36]
def count1004 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count1006 (b : Nat → Bool) : Nat := countLit b [37, 38, 40]
def count1009 (b : Nat → Bool) : Nat := countLit b [28, 29, 36, 37, 38, 40]
def count1015 (b : Nat → Bool) : Nat := countLit b [45, 48]
def count1017 (b : Nat → Bool) : Nat := countLit b [42, 45, 48]
def count1020 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count1022 (b : Nat → Bool) : Nat := countLit b [50, 52, 53]
def count1025 (b : Nat → Bool) : Nat := countLit b [42, 45, 48, 50, 52, 53]
def count1031 (b : Nat → Bool) : Nat := countLit b [28, 29, 36, 37, 38, 40, 42, 45, 48, 50, 52, 53]
def count1043 (b : Nat → Bool) : Nat := countLit b [5, 6, 7, 9, 11, 14, 17, 19, 20, 22, 26, 27, 28, 29, 36, 37, 38, 40, 42, 45, 48, 50, 52, 53]
def count1067 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count1069 (b : Nat → Bool) : Nat := countLit b [54, 58, 60]
def count1072 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count1074 (b : Nat → Bool) : Nat := countLit b [63, 64, 66]
def count1077 (b : Nat → Bool) : Nat := countLit b [54, 58, 60, 63, 64, 66]
def count1083 (b : Nat → Bool) : Nat := countLit b [69, 73]
def count1085 (b : Nat → Bool) : Nat := countLit b [68, 69, 73]
def count1088 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count1090 (b : Nat → Bool) : Nat := countLit b [74, 75, 77]
def count1093 (b : Nat → Bool) : Nat := countLit b [68, 69, 73, 74, 75, 77]
def count1099 (b : Nat → Bool) : Nat := countLit b [54, 58, 60, 63, 64, 66, 68, 69, 73, 74, 75, 77]
def count1111 (b : Nat → Bool) : Nat := countLit b [82, 83]
def count1113 (b : Nat → Bool) : Nat := countLit b [81, 82, 83]
def count1116 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count1118 (b : Nat → Bool) : Nat := countLit b [84, 88, 90]
def count1121 (b : Nat → Bool) : Nat := countLit b [81, 82, 83, 84, 88, 90]
def count1127 (b : Nat → Bool) : Nat := countLit b [93, 97]
def count1129 (b : Nat → Bool) : Nat := countLit b [91, 93, 97]
def count1132 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count1134 (b : Nat → Bool) : Nat := countLit b [98, 99, 100]
def count1137 (b : Nat → Bool) : Nat := countLit b [91, 93, 97, 98, 99, 100]
def count1143 (b : Nat → Bool) : Nat := countLit b [81, 82, 83, 84, 88, 90, 91, 93, 97, 98, 99, 100]
def count1155 (b : Nat → Bool) : Nat := countLit b [54, 58, 60, 63, 64, 66, 68, 69, 73, 74, 75, 77, 81, 82, 83, 84, 88, 90, 91, 93, 97, 98, 99, 100]
def count1179 (b : Nat → Bool) : Nat := countLit b [5, 6, 7, 9, 11, 14, 17, 19, 20, 22, 26, 27, 28, 29, 36, 37, 38, 40, 42, 45, 48, 50, 52, 53, 54, 58, 60, 63, 64, 66, 68, 69, 73, 74, 75, 77, 81, 82, 83, 84, 88, 90, 91, 93, 97, 98, 99, 100]
def count1221 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count1223 (b : Nat → Bool) : Nat := countLit b [-5, -6, -7]
def count1226 (b : Nat → Bool) : Nat := countLit b [-11, -14]
def count1228 (b : Nat → Bool) : Nat := countLit b [-9, -11, -14]
def count1231 (b : Nat → Bool) : Nat := countLit b [-5, -6, -7, -9, -11, -14]
def count1237 (b : Nat → Bool) : Nat := countLit b [-19, -20]
def count1239 (b : Nat → Bool) : Nat := countLit b [-17, -19, -20]
def count1242 (b : Nat → Bool) : Nat := countLit b [-26, -27]
def count1244 (b : Nat → Bool) : Nat := countLit b [-22, -26, -27]
def count1247 (b : Nat → Bool) : Nat := countLit b [-17, -19, -20, -22, -26, -27]
def count1253 (b : Nat → Bool) : Nat := countLit b [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27]
def count1261 (b : Nat → Bool) : Nat := countLit b [-29, -36]
def count1263 (b : Nat → Bool) : Nat := countLit b [-28, -29, -36]
def count1266 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1268 (b : Nat → Bool) : Nat := countLit b [-37, -38, -40]
def count1271 (b : Nat → Bool) : Nat := countLit b [-28, -29, -36, -37, -38, -40]
def count1277 (b : Nat → Bool) : Nat := countLit b [-45, -48]
def count1279 (b : Nat → Bool) : Nat := countLit b [-42, -45, -48]
def count1282 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count1284 (b : Nat → Bool) : Nat := countLit b [-50, -52, -53]
def count1287 (b : Nat → Bool) : Nat := countLit b [-42, -45, -48, -50, -52, -53]
def count1293 (b : Nat → Bool) : Nat := countLit b [-28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]
def count1301 (b : Nat → Bool) : Nat := countLit b [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53]
def count1309 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count1311 (b : Nat → Bool) : Nat := countLit b [-54, -58, -60]
def count1314 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1316 (b : Nat → Bool) : Nat := countLit b [-63, -64, -66]
def count1319 (b : Nat → Bool) : Nat := countLit b [-54, -58, -60, -63, -64, -66]
def count1325 (b : Nat → Bool) : Nat := countLit b [-69, -73]
def count1327 (b : Nat → Bool) : Nat := countLit b [-68, -69, -73]
def count1330 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count1332 (b : Nat → Bool) : Nat := countLit b [-74, -75, -77]
def count1335 (b : Nat → Bool) : Nat := countLit b [-68, -69, -73, -74, -75, -77]
def count1341 (b : Nat → Bool) : Nat := countLit b [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77]
def count1349 (b : Nat → Bool) : Nat := countLit b [-82, -83]
def count1351 (b : Nat → Bool) : Nat := countLit b [-81, -82, -83]
def count1354 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count1356 (b : Nat → Bool) : Nat := countLit b [-84, -88, -90]
def count1359 (b : Nat → Bool) : Nat := countLit b [-81, -82, -83, -84, -88, -90]
def count1365 (b : Nat → Bool) : Nat := countLit b [-93, -97]
def count1367 (b : Nat → Bool) : Nat := countLit b [-91, -93, -97]
def count1370 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1372 (b : Nat → Bool) : Nat := countLit b [-98, -99, -100]
def count1375 (b : Nat → Bool) : Nat := countLit b [-91, -93, -97, -98, -99, -100]
def count1381 (b : Nat → Bool) : Nat := countLit b [-81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]
def count1389 (b : Nat → Bool) : Nat := countLit b [-54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]
def count1397 (b : Nat → Bool) : Nat := countLit b [-5, -6, -7, -9, -11, -14, -17, -19, -20, -22, -26, -27, -28, -29, -36, -37, -38, -40, -42, -45, -48, -50, -52, -53, -54, -58, -60, -63, -64, -66, -68, -69, -73, -74, -75, -77, -81, -82, -83, -84, -88, -90, -91, -93, -97, -98, -99, -100]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 702 then (if i < 351 then (if i < 175 then (if i < 87 then (if i < 43 then (if i < 21 then (if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 7 then (if i < 6 then b 5 else b 6) else (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)))) else (if i < 15 then (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else (if i < 14 then b 13 else b 14))) else (if i < 18 then (if i < 16 then b 15 else (if i < 17 then b 16 else b 17)) else (if i < 19 then b 18 else (if i < 20 then b 19 else b 20))))) else (if i < 32 then (if i < 26 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else (if i < 25 then b 24 else b 25))) else (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)))) else (if i < 37 then (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else (if i < 36 then b 35 else b 36))) else (if i < 40 then (if i < 38 then b 37 else (if i < 39 then b 38 else b 39)) else (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)))))) else (if i < 65 then (if i < 54 then (if i < 48 then (if i < 45 then (if i < 44 then b 43 else b 44) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47))) else (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 52 then b 51 else (if i < 53 then b 52 else b 53)))) else (if i < 59 then (if i < 56 then (if i < 55 then b 54 else b 55) else (if i < 57 then b 56 else (if i < 58 then b 57 else b 58))) else (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 63 then b 62 else (if i < 64 then b 63 else b 64))))) else (if i < 76 then (if i < 70 then (if i < 67 then (if i < 66 then b 65 else b 66) else (if i < 68 then b 67 else (if i < 69 then b 68 else b 69))) else (if i < 73 then (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)) else (if i < 74 then b 73 else (if i < 75 then b 74 else b 75)))) else (if i < 81 then (if i < 78 then (if i < 77 then b 76 else b 77) else (if i < 79 then b 78 else (if i < 80 then b 79 else b 80))) else (if i < 84 then (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)) else (if i < 85 then b 84 else (if i < 86 then b 85 else b 86))))))) else (if i < 131 then (if i < 109 then (if i < 98 then (if i < 92 then (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else (if i < 91 then b 90 else b 91))) else (if i < 95 then (if i < 93 then b 92 else (if i < 94 then b 93 else b 94)) else (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)))) else (if i < 103 then (if i < 100 then (if i < 99 then b 98 else b 99) else (if i < 101 then b 100 else (if i < 102 then b 101 else b 102))) else (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 107 then b 106 else (if i < 108 then b 107 else b 108))))) else (if i < 120 then (if i < 114 then (if i < 111 then (if i < 110 then b 109 else b 110) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113))) else (if i < 117 then (if i < 115 then b 114 else (if i < 116 then b 115 else b 116)) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)))) else (if i < 125 then (if i < 122 then (if i < 121 then b 120 else b 121) else (if i < 123 then b 122 else (if i < 124 then b 123 else b 124))) else (if i < 128 then (if i < 126 then b 125 else (if i < 127 then b 126 else b 127)) else (if i < 129 then b 128 else (if i < 130 then b 129 else b 130)))))) else (if i < 153 then (if i < 142 then (if i < 136 then (if i < 133 then (if i < 132 then b 131 else b 132) else (if i < 134 then b 133 else (if i < 135 then b 134 else b 135))) else (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 140 then b 139 else (if i < 141 then b 140 else b 141)))) else (if i < 147 then (if i < 144 then (if i < 143 then b 142 else b 143) else (if i < 145 then b 144 else (if i < 146 then b 145 else b 146))) else (if i < 150 then (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)) else (if i < 151 then b 150 else (if i < 152 then b 151 else b 152))))) else (if i < 164 then (if i < 158 then (if i < 155 then (if i < 154 then b 153 else b 154) else (if i < 156 then b 155 else (if i < 157 then b 156 else b 157))) else (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 162 then b 161 else (if i < 163 then b 162 else b 163)))) else (if i < 169 then (if i < 166 then (if i < 165 then b 164 else b 165) else (if i < 167 then b 166 else (if i < 168 then b 167 else b 168))) else (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174)))))))) else (if i < 263 then (if i < 219 then (if i < 197 then (if i < 186 then (if i < 180 then (if i < 177 then (if i < 176 then b 175 else b 176) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179))) else (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185)))) else (if i < 191 then (if i < 188 then (if i < 187 then b 186 else b 187) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190))) else (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196))))) else (if i < 208 then (if i < 202 then (if i < 199 then (if i < 198 then b 197 else b 198) else (if i < 200 then b 199 else (if i < 201 then b 200 else b 201))) else (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 206 then decide (1 ≤ count205 b) else (if i < 207 then decide (2 ≤ count205 b) else decide (1 ≤ count207 b))))) else (if i < 213 then (if i < 210 then (if i < 209 then decide (2 ≤ count207 b) else decide (1 ≤ count209 b)) else (if i < 211 then decide (2 ≤ count209 b) else (if i < 212 then decide (1 ≤ count211 b) else decide (2 ≤ count211 b)))) else (if i < 216 then (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))) else (if i < 217 then decide (2 ≤ count215 b) else (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b))))))) else (if i < 241 then (if i < 230 then (if i < 224 then (if i < 221 then (if i < 220 then decide (1 ≤ count219 b) else decide (2 ≤ count219 b)) else (if i < 222 then decide (1 ≤ count221 b) else (if i < 223 then decide (2 ≤ count221 b) else decide (1 ≤ count223 b)))) else (if i < 227 then (if i < 225 then decide (2 ≤ count223 b) else (if i < 226 then decide (1 ≤ count225 b) else decide (2 ≤ count225 b))) else (if i < 228 then decide (1 ≤ count227 b) else (if i < 229 then decide (2 ≤ count227 b) else decide (1 ≤ count229 b))))) else (if i < 235 then (if i < 232 then (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b)) else (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))) else (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b)))))) else (if i < 252 then (if i < 246 then (if i < 243 then (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b)) else (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b)))) else (if i < 249 then (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b))) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))))) else (if i < 257 then (if i < 254 then (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)) else (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b)))) else (if i < 260 then (if i < 258 then decide (1 ≤ count257 b) else (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b))) else (if i < 261 then decide (2 ≤ count259 b) else (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b)))))))) else (if i < 307 then (if i < 285 then (if i < 274 then (if i < 268 then (if i < 265 then (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)) else (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)))) else (if i < 271 then (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b))) else (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))))) else (if i < 279 then (if i < 276 then (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)) else (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)))) else (if i < 282 then (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))) else (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)))))) else (if i < 296 then (if i < 290 then (if i < 287 then (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)) else (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)))) else (if i < 293 then (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))) else (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))))) else (if i < 301 then (if i < 298 then (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)) else (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b)))) else (if i < 304 then (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))) else (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))))))) else (if i < 329 then (if i < 318 then (if i < 312 then (if i < 309 then (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)) else (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))) else (if i < 315 then (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))) else (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b))))) else (if i < 323 then (if i < 320 then (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)) else (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)))) else (if i < 326 then (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))) else (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)))))) else (if i < 340 then (if i < 334 then (if i < 331 then (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)) else (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)))) else (if i < 337 then (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b))) else (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))))) else (if i < 345 then (if i < 342 then (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)) else (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)))) else (if i < 348 then (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))) else (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b)))))))))) else (if i < 526 then (if i < 438 then (if i < 394 then (if i < 372 then (if i < 361 then (if i < 356 then (if i < 353 then (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b)) else (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b)))) else (if i < 358 then (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b)) else (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))))) else (if i < 366 then (if i < 363 then (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))) else (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)))))) else (if i < 383 then (if i < 377 then (if i < 374 then (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b)) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)))) else (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b))))) else (if i < 388 then (if i < 385 then (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b)) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)))) else (if i < 391 then (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b))) else (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))))))) else (if i < 416 then (if i < 405 then (if i < 399 then (if i < 396 then (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)) else (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b)))) else (if i < 402 then (if i < 400 then decide (1 ≤ count399 b) else (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b))) else (if i < 403 then decide (2 ≤ count401 b) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b))))) else (if i < 410 then (if i < 407 then (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b)) else (if i < 408 then decide (1 ≤ count407 b) else (if i < 409 then decide (2 ≤ count407 b) else decide (3 ≤ count407 b)))) else (if i < 413 then (if i < 411 then decide (1 ≤ count410 b) else (if i < 412 then decide (2 ≤ count410 b) else decide (1 ≤ count412 b))) else (if i < 414 then decide (2 ≤ count412 b) else (if i < 415 then decide (3 ≤ count412 b) else decide (1 ≤ count415 b)))))) else (if i < 427 then (if i < 421 then (if i < 418 then (if i < 417 then decide (2 ≤ count415 b) else decide (3 ≤ count415 b)) else (if i < 419 then decide (4 ≤ count415 b) else (if i < 420 then decide (5 ≤ count415 b) else decide (6 ≤ count415 b)))) else (if i < 424 then (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))) else (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (3 ≤ count423 b) else decide (1 ≤ count426 b))))) else (if i < 432 then (if i < 429 then (if i < 428 then decide (2 ≤ count426 b) else decide (1 ≤ count428 b)) else (if i < 430 then decide (2 ≤ count428 b) else (if i < 431 then decide (1 ≤ count430 b) else decide (2 ≤ count430 b)))) else (if i < 435 then (if i < 433 then decide (3 ≤ count430 b) else (if i < 434 then decide (4 ≤ count430 b) else decide (1 ≤ count434 b))) else (if i < 436 then decide (2 ≤ count434 b) else (if i < 437 then decide (3 ≤ count434 b) else decide (4 ≤ count434 b)))))))) else (if i < 482 then (if i < 460 then (if i < 449 then (if i < 443 then (if i < 440 then (if i < 439 then decide (5 ≤ count434 b) else decide (6 ≤ count434 b)) else (if i < 441 then decide (7 ≤ count434 b) else (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b)))) else (if i < 446 then (if i < 444 then decide (3 ≤ count441 b) else (if i < 445 then decide (4 ≤ count441 b) else decide (5 ≤ count441 b))) else (if i < 447 then decide (6 ≤ count441 b) else (if i < 448 then decide (7 ≤ count441 b) else decide (8 ≤ count441 b))))) else (if i < 454 then (if i < 451 then (if i < 450 then decide (9 ≤ count441 b) else decide (10 ≤ count441 b)) else (if i < 452 then decide (11 ≤ count441 b) else (if i < 453 then decide (12 ≤ count441 b) else decide (13 ≤ count441 b)))) else (if i < 457 then (if i < 455 then decide (1 ≤ count454 b) else (if i < 456 then decide (2 ≤ count454 b) else decide (1 ≤ count456 b))) else (if i < 458 then decide (2 ≤ count456 b) else (if i < 459 then decide (3 ≤ count456 b) else decide (1 ≤ count459 b)))))) else (if i < 471 then (if i < 465 then (if i < 462 then (if i < 461 then decide (2 ≤ count459 b) else decide (1 ≤ count461 b)) else (if i < 463 then decide (2 ≤ count461 b) else (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b)))) else (if i < 468 then (if i < 466 then decide (3 ≤ count463 b) else (if i < 467 then decide (4 ≤ count463 b) else decide (1 ≤ count467 b))) else (if i < 469 then decide (2 ≤ count467 b) else (if i < 470 then decide (3 ≤ count467 b) else decide (4 ≤ count467 b))))) else (if i < 476 then (if i < 473 then (if i < 472 then decide (5 ≤ count467 b) else decide (6 ≤ count467 b)) else (if i < 474 then decide (7 ≤ count467 b) else (if i < 475 then decide (1 ≤ count474 b) else decide (2 ≤ count474 b)))) else (if i < 479 then (if i < 477 then decide (1 ≤ count476 b) else (if i < 478 then decide (2 ≤ count476 b) else decide (3 ≤ count476 b))) else (if i < 480 then decide (1 ≤ count479 b) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b))))))) else (if i < 504 then (if i < 493 then (if i < 487 then (if i < 484 then (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b)) else (if i < 485 then decide (2 ≤ count483 b) else (if i < 486 then decide (3 ≤ count483 b) else decide (4 ≤ count483 b)))) else (if i < 490 then (if i < 488 then decide (1 ≤ count487 b) else (if i < 489 then decide (2 ≤ count487 b) else decide (3 ≤ count487 b))) else (if i < 491 then decide (4 ≤ count487 b) else (if i < 492 then decide (5 ≤ count487 b) else decide (6 ≤ count487 b))))) else (if i < 498 then (if i < 495 then (if i < 494 then decide (7 ≤ count487 b) else decide (1 ≤ count494 b)) else (if i < 496 then decide (2 ≤ count494 b) else (if i < 497 then decide (3 ≤ count494 b) else decide (4 ≤ count494 b)))) else (if i < 501 then (if i < 499 then decide (5 ≤ count494 b) else (if i < 500 then decide (6 ≤ count494 b) else decide (7 ≤ count494 b))) else (if i < 502 then decide (8 ≤ count494 b) else (if i < 503 then decide (9 ≤ count494 b) else decide (10 ≤ count494 b)))))) else (if i < 515 then (if i < 509 then (if i < 506 then (if i < 505 then decide (11 ≤ count494 b) else decide (12 ≤ count494 b)) else (if i < 507 then decide (13 ≤ count494 b) else (if i < 508 then decide (14 ≤ count494 b) else decide (1 ≤ count508 b)))) else (if i < 512 then (if i < 510 then decide (2 ≤ count508 b) else (if i < 511 then decide (3 ≤ count508 b) else decide (4 ≤ count508 b))) else (if i < 513 then decide (5 ≤ count508 b) else (if i < 514 then decide (6 ≤ count508 b) else decide (7 ≤ count508 b))))) else (if i < 520 then (if i < 517 then (if i < 516 then decide (8 ≤ count508 b) else decide (9 ≤ count508 b)) else (if i < 518 then decide (10 ≤ count508 b) else (if i < 519 then decide (11 ≤ count508 b) else decide (12 ≤ count508 b)))) else (if i < 523 then (if i < 521 then decide (13 ≤ count508 b) else (if i < 522 then decide (14 ≤ count508 b) else decide (15 ≤ count508 b))) else (if i < 524 then decide (16 ≤ count508 b) else (if i < 525 then decide (17 ≤ count508 b) else decide (18 ≤ count508 b))))))))) else (if i < 614 then (if i < 570 then (if i < 548 then (if i < 537 then (if i < 531 then (if i < 528 then (if i < 527 then decide (19 ≤ count508 b) else decide (20 ≤ count508 b)) else (if i < 529 then decide (21 ≤ count508 b) else (if i < 530 then decide (22 ≤ count508 b) else decide (23 ≤ count508 b)))) else (if i < 534 then (if i < 532 then decide (24 ≤ count508 b) else (if i < 533 then decide (25 ≤ count508 b) else decide (26 ≤ count508 b))) else (if i < 535 then decide (27 ≤ count508 b) else (if i < 536 then decide (1 ≤ count535 b) else decide (2 ≤ count535 b))))) else (if i < 542 then (if i < 539 then (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b)) else (if i < 540 then decide (3 ≤ count537 b) else (if i < 541 then decide (1 ≤ count540 b) else decide (2 ≤ count540 b)))) else (if i < 545 then (if i < 543 then decide (1 ≤ count542 b) else (if i < 544 then decide (2 ≤ count542 b) else decide (3 ≤ count542 b))) else (if i < 546 then decide (1 ≤ count545 b) else (if i < 547 then decide (2 ≤ count545 b) else decide (3 ≤ count545 b)))))) else (if i < 559 then (if i < 553 then (if i < 550 then (if i < 549 then decide (4 ≤ count545 b) else decide (5 ≤ count545 b)) else (if i < 551 then decide (6 ≤ count545 b) else (if i < 552 then decide (1 ≤ count551 b) else decide (2 ≤ count551 b)))) else (if i < 556 then (if i < 554 then decide (1 ≤ count553 b) else (if i < 555 then decide (2 ≤ count553 b) else decide (3 ≤ count553 b))) else (if i < 557 then decide (1 ≤ count556 b) else (if i < 558 then decide (2 ≤ count556 b) else decide (1 ≤ count558 b))))) else (if i < 564 then (if i < 561 then (if i < 560 then decide (2 ≤ count558 b) else decide (1 ≤ count560 b)) else (if i < 562 then decide (2 ≤ count560 b) else (if i < 563 then decide (3 ≤ count560 b) else decide (4 ≤ count560 b)))) else (if i < 567 then (if i < 565 then decide (1 ≤ count564 b) else (if i < 566 then decide (2 ≤ count564 b) else decide (3 ≤ count564 b))) else (if i < 568 then decide (4 ≤ count564 b) else (if i < 569 then decide (5 ≤ count564 b) else decide (6 ≤ count564 b))))))) else (if i < 592 then (if i < 581 then (if i < 575 then (if i < 572 then (if i < 571 then decide (7 ≤ count564 b) else decide (1 ≤ count571 b)) else (if i < 573 then decide (2 ≤ count571 b) else (if i < 574 then decide (3 ≤ count571 b) else decide (4 ≤ count571 b)))) else (if i < 578 then (if i < 576 then decide (5 ≤ count571 b) else (if i < 577 then decide (6 ≤ count571 b) else decide (7 ≤ count571 b))) else (if i < 579 then decide (8 ≤ count571 b) else (if i < 580 then decide (9 ≤ count571 b) else decide (10 ≤ count571 b))))) else (if i < 586 then (if i < 583 then (if i < 582 then decide (11 ≤ count571 b) else decide (12 ≤ count571 b)) else (if i < 584 then decide (13 ≤ count571 b) else (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b)))) else (if i < 589 then (if i < 587 then decide (1 ≤ count586 b) else (if i < 588 then decide (2 ≤ count586 b) else decide (3 ≤ count586 b))) else (if i < 590 then decide (1 ≤ count589 b) else (if i < 591 then decide (2 ≤ count589 b) else decide (1 ≤ count591 b)))))) else (if i < 603 then (if i < 597 then (if i < 594 then (if i < 593 then decide (2 ≤ count591 b) else decide (1 ≤ count593 b)) else (if i < 595 then decide (2 ≤ count593 b) else (if i < 596 then decide (3 ≤ count593 b) else decide (4 ≤ count593 b)))) else (if i < 600 then (if i < 598 then decide (1 ≤ count597 b) else (if i < 599 then decide (2 ≤ count597 b) else decide (3 ≤ count597 b))) else (if i < 601 then decide (4 ≤ count597 b) else (if i < 602 then decide (5 ≤ count597 b) else decide (6 ≤ count597 b))))) else (if i < 608 then (if i < 605 then (if i < 604 then decide (7 ≤ count597 b) else decide (1 ≤ count604 b)) else (if i < 606 then decide (2 ≤ count604 b) else (if i < 607 then decide (1 ≤ count606 b) else decide (2 ≤ count606 b)))) else (if i < 611 then (if i < 609 then decide (3 ≤ count606 b) else (if i < 610 then decide (1 ≤ count609 b) else decide (2 ≤ count609 b))) else (if i < 612 then decide (1 ≤ count611 b) else (if i < 613 then decide (2 ≤ count611 b) else decide (1 ≤ count613 b)))))))) else (if i < 658 then (if i < 636 then (if i < 625 then (if i < 619 then (if i < 616 then (if i < 615 then decide (2 ≤ count613 b) else decide (3 ≤ count613 b)) else (if i < 617 then decide (4 ≤ count613 b) else (if i < 618 then decide (1 ≤ count617 b) else decide (2 ≤ count617 b)))) else (if i < 622 then (if i < 620 then decide (3 ≤ count617 b) else (if i < 621 then decide (4 ≤ count617 b) else decide (5 ≤ count617 b))) else (if i < 623 then decide (6 ≤ count617 b) else (if i < 624 then decide (7 ≤ count617 b) else decide (1 ≤ count624 b))))) else (if i < 630 then (if i < 627 then (if i < 626 then decide (2 ≤ count624 b) else decide (3 ≤ count624 b)) else (if i < 628 then decide (4 ≤ count624 b) else (if i < 629 then decide (5 ≤ count624 b) else decide (6 ≤ count624 b)))) else (if i < 633 then (if i < 631 then decide (7 ≤ count624 b) else (if i < 632 then decide (8 ≤ count624 b) else decide (9 ≤ count624 b))) else (if i < 634 then decide (10 ≤ count624 b) else (if i < 635 then decide (11 ≤ count624 b) else decide (12 ≤ count624 b)))))) else (if i < 647 then (if i < 641 then (if i < 638 then (if i < 637 then decide (13 ≤ count624 b) else decide (14 ≤ count624 b)) else (if i < 639 then decide (1 ≤ count638 b) else (if i < 640 then decide (2 ≤ count638 b) else decide (3 ≤ count638 b)))) else (if i < 644 then (if i < 642 then decide (4 ≤ count638 b) else (if i < 643 then decide (5 ≤ count638 b) else decide (6 ≤ count638 b))) else (if i < 645 then decide (7 ≤ count638 b) else (if i < 646 then decide (8 ≤ count638 b) else decide (9 ≤ count638 b))))) else (if i < 652 then (if i < 649 then (if i < 648 then decide (10 ≤ count638 b) else decide (11 ≤ count638 b)) else (if i < 650 then decide (12 ≤ count638 b) else (if i < 651 then decide (13 ≤ count638 b) else decide (14 ≤ count638 b)))) else (if i < 655 then (if i < 653 then decide (15 ≤ count638 b) else (if i < 654 then decide (16 ≤ count638 b) else decide (17 ≤ count638 b))) else (if i < 656 then decide (18 ≤ count638 b) else (if i < 657 then decide (19 ≤ count638 b) else decide (20 ≤ count638 b))))))) else (if i < 680 then (if i < 669 then (if i < 663 then (if i < 660 then (if i < 659 then decide (21 ≤ count638 b) else decide (22 ≤ count638 b)) else (if i < 661 then decide (23 ≤ count638 b) else (if i < 662 then decide (24 ≤ count638 b) else decide (25 ≤ count638 b)))) else (if i < 666 then (if i < 664 then decide (26 ≤ count638 b) else (if i < 665 then decide (27 ≤ count638 b) else decide (1 ≤ count665 b))) else (if i < 667 then decide (2 ≤ count665 b) else (if i < 668 then decide (3 ≤ count665 b) else decide (4 ≤ count665 b))))) else (if i < 674 then (if i < 671 then (if i < 670 then decide (5 ≤ count665 b) else decide (6 ≤ count665 b)) else (if i < 672 then decide (7 ≤ count665 b) else (if i < 673 then decide (8 ≤ count665 b) else decide (9 ≤ count665 b)))) else (if i < 677 then (if i < 675 then decide (10 ≤ count665 b) else (if i < 676 then decide (11 ≤ count665 b) else decide (12 ≤ count665 b))) else (if i < 678 then decide (13 ≤ count665 b) else (if i < 679 then decide (14 ≤ count665 b) else decide (15 ≤ count665 b)))))) else (if i < 691 then (if i < 685 then (if i < 682 then (if i < 681 then decide (16 ≤ count665 b) else decide (17 ≤ count665 b)) else (if i < 683 then decide (18 ≤ count665 b) else (if i < 684 then decide (19 ≤ count665 b) else decide (20 ≤ count665 b)))) else (if i < 688 then (if i < 686 then decide (21 ≤ count665 b) else (if i < 687 then decide (22 ≤ count665 b) else decide (23 ≤ count665 b))) else (if i < 689 then decide (24 ≤ count665 b) else (if i < 690 then decide (25 ≤ count665 b) else decide (26 ≤ count665 b))))) else (if i < 696 then (if i < 693 then (if i < 692 then decide (27 ≤ count665 b) else decide (28 ≤ count665 b)) else (if i < 694 then decide (29 ≤ count665 b) else (if i < 695 then decide (30 ≤ count665 b) else decide (31 ≤ count665 b)))) else (if i < 699 then (if i < 697 then decide (32 ≤ count665 b) else (if i < 698 then decide (33 ≤ count665 b) else decide (34 ≤ count665 b))) else (if i < 700 then decide (35 ≤ count665 b) else (if i < 701 then decide (36 ≤ count665 b) else decide (37 ≤ count665 b))))))))))) else (if i < 1053 then (if i < 877 then (if i < 789 then (if i < 745 then (if i < 723 then (if i < 712 then (if i < 707 then (if i < 704 then (if i < 703 then decide (38 ≤ count665 b) else decide (39 ≤ count665 b)) else (if i < 705 then decide (40 ≤ count665 b) else (if i < 706 then decide (41 ≤ count665 b) else decide (42 ≤ count665 b)))) else (if i < 709 then (if i < 708 then decide (1 ≤ count707 b) else decide (2 ≤ count707 b)) else (if i < 710 then decide (1 ≤ count709 b) else (if i < 711 then decide (2 ≤ count709 b) else decide (3 ≤ count709 b))))) else (if i < 717 then (if i < 714 then (if i < 713 then decide (1 ≤ count712 b) else decide (2 ≤ count712 b)) else (if i < 715 then decide (1 ≤ count714 b) else (if i < 716 then decide (2 ≤ count714 b) else decide (3 ≤ count714 b)))) else (if i < 720 then (if i < 718 then decide (1 ≤ count717 b) else (if i < 719 then decide (2 ≤ count717 b) else decide (3 ≤ count717 b))) else (if i < 721 then decide (4 ≤ count717 b) else (if i < 722 then decide (5 ≤ count717 b) else decide (6 ≤ count717 b)))))) else (if i < 734 then (if i < 728 then (if i < 725 then (if i < 724 then decide (1 ≤ count723 b) else decide (2 ≤ count723 b)) else (if i < 726 then decide (1 ≤ count725 b) else (if i < 727 then decide (2 ≤ count725 b) else decide (3 ≤ count725 b)))) else (if i < 731 then (if i < 729 then decide (1 ≤ count728 b) else (if i < 730 then decide (2 ≤ count728 b) else decide (1 ≤ count730 b))) else (if i < 732 then decide (2 ≤ count730 b) else (if i < 733 then decide (1 ≤ count732 b) else decide (2 ≤ count732 b))))) else (if i < 739 then (if i < 736 then (if i < 735 then decide (3 ≤ count732 b) else decide (4 ≤ count732 b)) else (if i < 737 then decide (1 ≤ count736 b) else (if i < 738 then decide (2 ≤ count736 b) else decide (3 ≤ count736 b)))) else (if i < 742 then (if i < 740 then decide (4 ≤ count736 b) else (if i < 741 then decide (5 ≤ count736 b) else decide (6 ≤ count736 b))) else (if i < 743 then decide (7 ≤ count736 b) else (if i < 744 then decide (1 ≤ count743 b) else decide (2 ≤ count743 b))))))) else (if i < 767 then (if i < 756 then (if i < 750 then (if i < 747 then (if i < 746 then decide (3 ≤ count743 b) else decide (4 ≤ count743 b)) else (if i < 748 then decide (5 ≤ count743 b) else (if i < 749 then decide (6 ≤ count743 b) else decide (7 ≤ count743 b)))) else (if i < 753 then (if i < 751 then decide (8 ≤ count743 b) else (if i < 752 then decide (9 ≤ count743 b) else decide (10 ≤ count743 b))) else (if i < 754 then decide (11 ≤ count743 b) else (if i < 755 then decide (12 ≤ count743 b) else decide (13 ≤ count743 b))))) else (if i < 761 then (if i < 758 then (if i < 757 then decide (1 ≤ count756 b) else decide (2 ≤ count756 b)) else (if i < 759 then decide (1 ≤ count758 b) else (if i < 760 then decide (2 ≤ count758 b) else decide (3 ≤ count758 b)))) else (if i < 764 then (if i < 762 then decide (1 ≤ count761 b) else (if i < 763 then decide (2 ≤ count761 b) else decide (1 ≤ count763 b))) else (if i < 765 then decide (2 ≤ count763 b) else (if i < 766 then decide (1 ≤ count765 b) else decide (2 ≤ count765 b)))))) else (if i < 778 then (if i < 772 then (if i < 769 then (if i < 768 then decide (3 ≤ count765 b) else decide (4 ≤ count765 b)) else (if i < 770 then decide (1 ≤ count769 b) else (if i < 771 then decide (2 ≤ count769 b) else decide (3 ≤ count769 b)))) else (if i < 775 then (if i < 773 then decide (4 ≤ count769 b) else (if i < 774 then decide (5 ≤ count769 b) else decide (6 ≤ count769 b))) else (if i < 776 then decide (7 ≤ count769 b) else (if i < 777 then decide (1 ≤ count776 b) else decide (2 ≤ count776 b))))) else (if i < 783 then (if i < 780 then (if i < 779 then decide (1 ≤ count778 b) else decide (2 ≤ count778 b)) else (if i < 781 then decide (3 ≤ count778 b) else (if i < 782 then decide (1 ≤ count781 b) else decide (2 ≤ count781 b)))) else (if i < 786 then (if i < 784 then decide (1 ≤ count783 b) else (if i < 785 then decide (2 ≤ count783 b) else decide (1 ≤ count785 b))) else (if i < 787 then decide (2 ≤ count785 b) else (if i < 788 then decide (3 ≤ count785 b) else decide (4 ≤ count785 b)))))))) else (if i < 833 then (if i < 811 then (if i < 800 then (if i < 794 then (if i < 791 then (if i < 790 then decide (1 ≤ count789 b) else decide (2 ≤ count789 b)) else (if i < 792 then decide (3 ≤ count789 b) else (if i < 793 then decide (4 ≤ count789 b) else decide (5 ≤ count789 b)))) else (if i < 797 then (if i < 795 then decide (6 ≤ count789 b) else (if i < 796 then decide (7 ≤ count789 b) else decide (1 ≤ count796 b))) else (if i < 798 then decide (2 ≤ count796 b) else (if i < 799 then decide (3 ≤ count796 b) else decide (4 ≤ count796 b))))) else (if i < 805 then (if i < 802 then (if i < 801 then decide (5 ≤ count796 b) else decide (6 ≤ count796 b)) else (if i < 803 then decide (7 ≤ count796 b) else (if i < 804 then decide (8 ≤ count796 b) else decide (9 ≤ count796 b)))) else (if i < 808 then (if i < 806 then decide (10 ≤ count796 b) else (if i < 807 then decide (11 ≤ count796 b) else decide (12 ≤ count796 b))) else (if i < 809 then decide (13 ≤ count796 b) else (if i < 810 then decide (14 ≤ count796 b) else decide (1 ≤ count810 b)))))) else (if i < 822 then (if i < 816 then (if i < 813 then (if i < 812 then decide (2 ≤ count810 b) else decide (3 ≤ count810 b)) else (if i < 814 then decide (4 ≤ count810 b) else (if i < 815 then decide (5 ≤ count810 b) else decide (6 ≤ count810 b)))) else (if i < 819 then (if i < 817 then decide (7 ≤ count810 b) else (if i < 818 then decide (8 ≤ count810 b) else decide (9 ≤ count810 b))) else (if i < 820 then decide (10 ≤ count810 b) else (if i < 821 then decide (11 ≤ count810 b) else decide (12 ≤ count810 b))))) else (if i < 827 then (if i < 824 then (if i < 823 then decide (13 ≤ count810 b) else decide (14 ≤ count810 b)) else (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (1 ≤ count826 b)))) else (if i < 830 then (if i < 828 then decide (2 ≤ count826 b) else (if i < 829 then decide (3 ≤ count826 b) else decide (1 ≤ count829 b))) else (if i < 831 then decide (2 ≤ count829 b) else (if i < 832 then decide (1 ≤ count831 b) else decide (2 ≤ count831 b))))))) else (if i < 855 then (if i < 844 then (if i < 838 then (if i < 835 then (if i < 834 then decide (3 ≤ count831 b) else decide (1 ≤ count834 b)) else (if i < 836 then decide (2 ≤ count834 b) else (if i < 837 then decide (3 ≤ count834 b) else decide (4 ≤ count834 b)))) else (if i < 841 then (if i < 839 then decide (5 ≤ count834 b) else (if i < 840 then decide (6 ≤ count834 b) else decide (1 ≤ count840 b))) else (if i < 842 then decide (2 ≤ count840 b) else (if i < 843 then decide (1 ≤ count842 b) else decide (2 ≤ count842 b))))) else (if i < 849 then (if i < 846 then (if i < 845 then decide (3 ≤ count842 b) else decide (1 ≤ count845 b)) else (if i < 847 then decide (2 ≤ count845 b) else (if i < 848 then decide (1 ≤ count847 b) else decide (2 ≤ count847 b)))) else (if i < 852 then (if i < 850 then decide (1 ≤ count849 b) else (if i < 851 then decide (2 ≤ count849 b) else decide (3 ≤ count849 b))) else (if i < 853 then decide (4 ≤ count849 b) else (if i < 854 then decide (1 ≤ count853 b) else decide (2 ≤ count853 b)))))) else (if i < 866 then (if i < 860 then (if i < 857 then (if i < 856 then decide (3 ≤ count853 b) else decide (4 ≤ count853 b)) else (if i < 858 then decide (5 ≤ count853 b) else (if i < 859 then decide (6 ≤ count853 b) else decide (7 ≤ count853 b)))) else (if i < 863 then (if i < 861 then decide (1 ≤ count860 b) else (if i < 862 then decide (2 ≤ count860 b) else decide (3 ≤ count860 b))) else (if i < 864 then decide (4 ≤ count860 b) else (if i < 865 then decide (5 ≤ count860 b) else decide (6 ≤ count860 b))))) else (if i < 871 then (if i < 868 then (if i < 867 then decide (7 ≤ count860 b) else decide (8 ≤ count860 b)) else (if i < 869 then decide (9 ≤ count860 b) else (if i < 870 then decide (10 ≤ count860 b) else decide (11 ≤ count860 b)))) else (if i < 874 then (if i < 872 then decide (12 ≤ count860 b) else (if i < 873 then decide (13 ≤ count860 b) else decide (1 ≤ count873 b))) else (if i < 875 then decide (2 ≤ count873 b) else (if i < 876 then decide (1 ≤ count875 b) else decide (2 ≤ count875 b))))))))) else (if i < 965 then (if i < 921 then (if i < 899 then (if i < 888 then (if i < 882 then (if i < 879 then (if i < 878 then decide (3 ≤ count875 b) else decide (1 ≤ count878 b)) else (if i < 880 then decide (2 ≤ count878 b) else (if i < 881 then decide (1 ≤ count880 b) else decide (2 ≤ count880 b)))) else (if i < 885 then (if i < 883 then decide (1 ≤ count882 b) else (if i < 884 then decide (2 ≤ count882 b) else decide (3 ≤ count882 b))) else (if i < 886 then decide (4 ≤ count882 b) else (if i < 887 then decide (1 ≤ count886 b) else decide (2 ≤ count886 b))))) else (if i < 893 then (if i < 890 then (if i < 889 then decide (3 ≤ count886 b) else decide (4 ≤ count886 b)) else (if i < 891 then decide (5 ≤ count886 b) else (if i < 892 then decide (6 ≤ count886 b) else decide (7 ≤ count886 b)))) else (if i < 896 then (if i < 894 then decide (1 ≤ count893 b) else (if i < 895 then decide (2 ≤ count893 b) else decide (1 ≤ count895 b))) else (if i < 897 then decide (2 ≤ count895 b) else (if i < 898 then decide (3 ≤ count895 b) else decide (1 ≤ count898 b)))))) else (if i < 910 then (if i < 904 then (if i < 901 then (if i < 900 then decide (2 ≤ count898 b) else decide (1 ≤ count900 b)) else (if i < 902 then decide (2 ≤ count900 b) else (if i < 903 then decide (1 ≤ count902 b) else decide (2 ≤ count902 b)))) else (if i < 907 then (if i < 905 then decide (3 ≤ count902 b) else (if i < 906 then decide (4 ≤ count902 b) else decide (1 ≤ count906 b))) else (if i < 908 then decide (2 ≤ count906 b) else (if i < 909 then decide (3 ≤ count906 b) else decide (4 ≤ count906 b))))) else (if i < 915 then (if i < 912 then (if i < 911 then decide (5 ≤ count906 b) else decide (6 ≤ count906 b)) else (if i < 913 then decide (7 ≤ count906 b) else (if i < 914 then decide (1 ≤ count913 b) else decide (2 ≤ count913 b)))) else (if i < 918 then (if i < 916 then decide (3 ≤ count913 b) else (if i < 917 then decide (4 ≤ count913 b) else decide (5 ≤ count913 b))) else (if i < 919 then decide (6 ≤ count913 b) else (if i < 920 then decide (7 ≤ count913 b) else decide (8 ≤ count913 b))))))) else (if i < 943 then (if i < 932 then (if i < 926 then (if i < 923 then (if i < 922 then decide (9 ≤ count913 b) else decide (10 ≤ count913 b)) else (if i < 924 then decide (11 ≤ count913 b) else (if i < 925 then decide (12 ≤ count913 b) else decide (13 ≤ count913 b)))) else (if i < 929 then (if i < 927 then decide (14 ≤ count913 b) else (if i < 928 then decide (1 ≤ count927 b) else decide (2 ≤ count927 b))) else (if i < 930 then decide (3 ≤ count927 b) else (if i < 931 then decide (4 ≤ count927 b) else decide (5 ≤ count927 b))))) else (if i < 937 then (if i < 934 then (if i < 933 then decide (6 ≤ count927 b) else decide (7 ≤ count927 b)) else (if i < 935 then decide (8 ≤ count927 b) else (if i < 936 then decide (9 ≤ count927 b) else decide (10 ≤ count927 b)))) else (if i < 940 then (if i < 938 then decide (11 ≤ count927 b) else (if i < 939 then decide (12 ≤ count927 b) else decide (13 ≤ count927 b))) else (if i < 941 then decide (14 ≤ count927 b) else (if i < 942 then decide (1 ≤ count941 b) else decide (2 ≤ count941 b)))))) else (if i < 954 then (if i < 948 then (if i < 945 then (if i < 944 then decide (3 ≤ count941 b) else decide (4 ≤ count941 b)) else (if i < 946 then decide (5 ≤ count941 b) else (if i < 947 then decide (6 ≤ count941 b) else decide (7 ≤ count941 b)))) else (if i < 951 then (if i < 949 then decide (8 ≤ count941 b) else (if i < 950 then decide (9 ≤ count941 b) else decide (10 ≤ count941 b))) else (if i < 952 then decide (11 ≤ count941 b) else (if i < 953 then decide (12 ≤ count941 b) else decide (13 ≤ count941 b))))) else (if i < 959 then (if i < 956 then (if i < 955 then decide (14 ≤ count941 b) else decide (1 ≤ count955 b)) else (if i < 957 then decide (2 ≤ count955 b) else (if i < 958 then decide (1 ≤ count957 b) else decide (2 ≤ count957 b)))) else (if i < 962 then (if i < 960 then decide (3 ≤ count957 b) else (if i < 961 then decide (1 ≤ count960 b) else decide (2 ≤ count960 b))) else (if i < 963 then decide (1 ≤ count962 b) else (if i < 964 then decide (2 ≤ count962 b) else decide (3 ≤ count962 b)))))))) else (if i < 1009 then (if i < 987 then (if i < 976 then (if i < 970 then (if i < 967 then (if i < 966 then decide (1 ≤ count965 b) else decide (2 ≤ count965 b)) else (if i < 968 then decide (3 ≤ count965 b) else (if i < 969 then decide (4 ≤ count965 b) else decide (5 ≤ count965 b)))) else (if i < 973 then (if i < 971 then decide (6 ≤ count965 b) else (if i < 972 then decide (1 ≤ count971 b) else decide (2 ≤ count971 b))) else (if i < 974 then decide (1 ≤ count973 b) else (if i < 975 then decide (2 ≤ count973 b) else decide (3 ≤ count973 b))))) else (if i < 981 then (if i < 978 then (if i < 977 then decide (1 ≤ count976 b) else decide (2 ≤ count976 b)) else (if i < 979 then decide (1 ≤ count978 b) else (if i < 980 then decide (2 ≤ count978 b) else decide (3 ≤ count978 b)))) else (if i < 984 then (if i < 982 then decide (1 ≤ count981 b) else (if i < 983 then decide (2 ≤ count981 b) else decide (3 ≤ count981 b))) else (if i < 985 then decide (4 ≤ count981 b) else (if i < 986 then decide (5 ≤ count981 b) else decide (6 ≤ count981 b)))))) else (if i < 998 then (if i < 992 then (if i < 989 then (if i < 988 then decide (1 ≤ count987 b) else decide (2 ≤ count987 b)) else (if i < 990 then decide (3 ≤ count987 b) else (if i < 991 then decide (4 ≤ count987 b) else decide (5 ≤ count987 b)))) else (if i < 995 then (if i < 993 then decide (6 ≤ count987 b) else (if i < 994 then decide (7 ≤ count987 b) else decide (8 ≤ count987 b))) else (if i < 996 then decide (9 ≤ count987 b) else (if i < 997 then decide (10 ≤ count987 b) else decide (11 ≤ count987 b))))) else (if i < 1003 then (if i < 1000 then (if i < 999 then decide (12 ≤ count987 b) else decide (1 ≤ count999 b)) else (if i < 1001 then decide (2 ≤ count999 b) else (if i < 1002 then decide (1 ≤ count1001 b) else decide (2 ≤ count1001 b)))) else (if i < 1006 then (if i < 1004 then decide (3 ≤ count1001 b) else (if i < 1005 then decide (1 ≤ count1004 b) else decide (2 ≤ count1004 b))) else (if i < 1007 then decide (1 ≤ count1006 b) else (if i < 1008 then decide (2 ≤ count1006 b) else decide (3 ≤ count1006 b))))))) else (if i < 1031 then (if i < 1020 then (if i < 1014 then (if i < 1011 then (if i < 1010 then decide (1 ≤ count1009 b) else decide (2 ≤ count1009 b)) else (if i < 1012 then decide (3 ≤ count1009 b) else (if i < 1013 then decide (4 ≤ count1009 b) else decide (5 ≤ count1009 b)))) else (if i < 1017 then (if i < 1015 then decide (6 ≤ count1009 b) else (if i < 1016 then decide (1 ≤ count1015 b) else decide (2 ≤ count1015 b))) else (if i < 1018 then decide (1 ≤ count1017 b) else (if i < 1019 then decide (2 ≤ count1017 b) else decide (3 ≤ count1017 b))))) else (if i < 1025 then (if i < 1022 then (if i < 1021 then decide (1 ≤ count1020 b) else decide (2 ≤ count1020 b)) else (if i < 1023 then decide (1 ≤ count1022 b) else (if i < 1024 then decide (2 ≤ count1022 b) else decide (3 ≤ count1022 b)))) else (if i < 1028 then (if i < 1026 then decide (1 ≤ count1025 b) else (if i < 1027 then decide (2 ≤ count1025 b) else decide (3 ≤ count1025 b))) else (if i < 1029 then decide (4 ≤ count1025 b) else (if i < 1030 then decide (5 ≤ count1025 b) else decide (6 ≤ count1025 b)))))) else (if i < 1042 then (if i < 1036 then (if i < 1033 then (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b)) else (if i < 1034 then decide (3 ≤ count1031 b) else (if i < 1035 then decide (4 ≤ count1031 b) else decide (5 ≤ count1031 b)))) else (if i < 1039 then (if i < 1037 then decide (6 ≤ count1031 b) else (if i < 1038 then decide (7 ≤ count1031 b) else decide (8 ≤ count1031 b))) else (if i < 1040 then decide (9 ≤ count1031 b) else (if i < 1041 then decide (10 ≤ count1031 b) else decide (11 ≤ count1031 b))))) else (if i < 1047 then (if i < 1044 then (if i < 1043 then decide (12 ≤ count1031 b) else decide (1 ≤ count1043 b)) else (if i < 1045 then decide (2 ≤ count1043 b) else (if i < 1046 then decide (3 ≤ count1043 b) else decide (4 ≤ count1043 b)))) else (if i < 1050 then (if i < 1048 then decide (5 ≤ count1043 b) else (if i < 1049 then decide (6 ≤ count1043 b) else decide (7 ≤ count1043 b))) else (if i < 1051 then decide (8 ≤ count1043 b) else (if i < 1052 then decide (9 ≤ count1043 b) else decide (10 ≤ count1043 b)))))))))) else (if i < 1229 then (if i < 1141 then (if i < 1097 then (if i < 1075 then (if i < 1064 then (if i < 1058 then (if i < 1055 then (if i < 1054 then decide (11 ≤ count1043 b) else decide (12 ≤ count1043 b)) else (if i < 1056 then decide (13 ≤ count1043 b) else (if i < 1057 then decide (14 ≤ count1043 b) else decide (15 ≤ count1043 b)))) else (if i < 1061 then (if i < 1059 then decide (16 ≤ count1043 b) else (if i < 1060 then decide (17 ≤ count1043 b) else decide (18 ≤ count1043 b))) else (if i < 1062 then decide (19 ≤ count1043 b) else (if i < 1063 then decide (20 ≤ count1043 b) else decide (21 ≤ count1043 b))))) else (if i < 1069 then (if i < 1066 then (if i < 1065 then decide (22 ≤ count1043 b) else decide (23 ≤ count1043 b)) else (if i < 1067 then decide (24 ≤ count1043 b) else (if i < 1068 then decide (1 ≤ count1067 b) else decide (2 ≤ count1067 b)))) else (if i < 1072 then (if i < 1070 then decide (1 ≤ count1069 b) else (if i < 1071 then decide (2 ≤ count1069 b) else decide (3 ≤ count1069 b))) else (if i < 1073 then decide (1 ≤ count1072 b) else (if i < 1074 then decide (2 ≤ count1072 b) else decide (1 ≤ count1074 b)))))) else (if i < 1086 then (if i < 1080 then (if i < 1077 then (if i < 1076 then decide (2 ≤ count1074 b) else decide (3 ≤ count1074 b)) else (if i < 1078 then decide (1 ≤ count1077 b) else (if i < 1079 then decide (2 ≤ count1077 b) else decide (3 ≤ count1077 b)))) else (if i < 1083 then (if i < 1081 then decide (4 ≤ count1077 b) else (if i < 1082 then decide (5 ≤ count1077 b) else decide (6 ≤ count1077 b))) else (if i < 1084 then decide (1 ≤ count1083 b) else (if i < 1085 then decide (2 ≤ count1083 b) else decide (1 ≤ count1085 b))))) else (if i < 1091 then (if i < 1088 then (if i < 1087 then decide (2 ≤ count1085 b) else decide (3 ≤ count1085 b)) else (if i < 1089 then decide (1 ≤ count1088 b) else (if i < 1090 then decide (2 ≤ count1088 b) else decide (1 ≤ count1090 b)))) else (if i < 1094 then (if i < 1092 then decide (2 ≤ count1090 b) else (if i < 1093 then decide (3 ≤ count1090 b) else decide (1 ≤ count1093 b))) else (if i < 1095 then decide (2 ≤ count1093 b) else (if i < 1096 then decide (3 ≤ count1093 b) else decide (4 ≤ count1093 b))))))) else (if i < 1119 then (if i < 1108 then (if i < 1102 then (if i < 1099 then (if i < 1098 then decide (5 ≤ count1093 b) else decide (6 ≤ count1093 b)) else (if i < 1100 then decide (1 ≤ count1099 b) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (3 ≤ count1099 b)))) else (if i < 1105 then (if i < 1103 then decide (4 ≤ count1099 b) else (if i < 1104 then decide (5 ≤ count1099 b) else decide (6 ≤ count1099 b))) else (if i < 1106 then decide (7 ≤ count1099 b) else (if i < 1107 then decide (8 ≤ count1099 b) else decide (9 ≤ count1099 b))))) else (if i < 1113 then (if i < 1110 then (if i < 1109 then decide (10 ≤ count1099 b) else decide (11 ≤ count1099 b)) else (if i < 1111 then decide (12 ≤ count1099 b) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b)))) else (if i < 1116 then (if i < 1114 then decide (1 ≤ count1113 b) else (if i < 1115 then decide (2 ≤ count1113 b) else decide (3 ≤ count1113 b))) else (if i < 1117 then decide (1 ≤ count1116 b) else (if i < 1118 then decide (2 ≤ count1116 b) else decide (1 ≤ count1118 b)))))) else (if i < 1130 then (if i < 1124 then (if i < 1121 then (if i < 1120 then decide (2 ≤ count1118 b) else decide (3 ≤ count1118 b)) else (if i < 1122 then decide (1 ≤ count1121 b) else (if i < 1123 then decide (2 ≤ count1121 b) else decide (3 ≤ count1121 b)))) else (if i < 1127 then (if i < 1125 then decide (4 ≤ count1121 b) else (if i < 1126 then decide (5 ≤ count1121 b) else decide (6 ≤ count1121 b))) else (if i < 1128 then decide (1 ≤ count1127 b) else (if i < 1129 then decide (2 ≤ count1127 b) else decide (1 ≤ count1129 b))))) else (if i < 1135 then (if i < 1132 then (if i < 1131 then decide (2 ≤ count1129 b) else decide (3 ≤ count1129 b)) else (if i < 1133 then decide (1 ≤ count1132 b) else (if i < 1134 then decide (2 ≤ count1132 b) else decide (1 ≤ count1134 b)))) else (if i < 1138 then (if i < 1136 then decide (2 ≤ count1134 b) else (if i < 1137 then decide (3 ≤ count1134 b) else decide (1 ≤ count1137 b))) else (if i < 1139 then decide (2 ≤ count1137 b) else (if i < 1140 then decide (3 ≤ count1137 b) else decide (4 ≤ count1137 b)))))))) else (if i < 1185 then (if i < 1163 then (if i < 1152 then (if i < 1146 then (if i < 1143 then (if i < 1142 then decide (5 ≤ count1137 b) else decide (6 ≤ count1137 b)) else (if i < 1144 then decide (1 ≤ count1143 b) else (if i < 1145 then decide (2 ≤ count1143 b) else decide (3 ≤ count1143 b)))) else (if i < 1149 then (if i < 1147 then decide (4 ≤ count1143 b) else (if i < 1148 then decide (5 ≤ count1143 b) else decide (6 ≤ count1143 b))) else (if i < 1150 then decide (7 ≤ count1143 b) else (if i < 1151 then decide (8 ≤ count1143 b) else decide (9 ≤ count1143 b))))) else (if i < 1157 then (if i < 1154 then (if i < 1153 then decide (10 ≤ count1143 b) else decide (11 ≤ count1143 b)) else (if i < 1155 then decide (12 ≤ count1143 b) else (if i < 1156 then decide (1 ≤ count1155 b) else decide (2 ≤ count1155 b)))) else (if i < 1160 then (if i < 1158 then decide (3 ≤ count1155 b) else (if i < 1159 then decide (4 ≤ count1155 b) else decide (5 ≤ count1155 b))) else (if i < 1161 then decide (6 ≤ count1155 b) else (if i < 1162 then decide (7 ≤ count1155 b) else decide (8 ≤ count1155 b)))))) else (if i < 1174 then (if i < 1168 then (if i < 1165 then (if i < 1164 then decide (9 ≤ count1155 b) else decide (10 ≤ count1155 b)) else (if i < 1166 then decide (11 ≤ count1155 b) else (if i < 1167 then decide (12 ≤ count1155 b) else decide (13 ≤ count1155 b)))) else (if i < 1171 then (if i < 1169 then decide (14 ≤ count1155 b) else (if i < 1170 then decide (15 ≤ count1155 b) else decide (16 ≤ count1155 b))) else (if i < 1172 then decide (17 ≤ count1155 b) else (if i < 1173 then decide (18 ≤ count1155 b) else decide (19 ≤ count1155 b))))) else (if i < 1179 then (if i < 1176 then (if i < 1175 then decide (20 ≤ count1155 b) else decide (21 ≤ count1155 b)) else (if i < 1177 then decide (22 ≤ count1155 b) else (if i < 1178 then decide (23 ≤ count1155 b) else decide (24 ≤ count1155 b)))) else (if i < 1182 then (if i < 1180 then decide (1 ≤ count1179 b) else (if i < 1181 then decide (2 ≤ count1179 b) else decide (3 ≤ count1179 b))) else (if i < 1183 then decide (4 ≤ count1179 b) else (if i < 1184 then decide (5 ≤ count1179 b) else decide (6 ≤ count1179 b))))))) else (if i < 1207 then (if i < 1196 then (if i < 1190 then (if i < 1187 then (if i < 1186 then decide (7 ≤ count1179 b) else decide (8 ≤ count1179 b)) else (if i < 1188 then decide (9 ≤ count1179 b) else (if i < 1189 then decide (10 ≤ count1179 b) else decide (11 ≤ count1179 b)))) else (if i < 1193 then (if i < 1191 then decide (12 ≤ count1179 b) else (if i < 1192 then decide (13 ≤ count1179 b) else decide (14 ≤ count1179 b))) else (if i < 1194 then decide (15 ≤ count1179 b) else (if i < 1195 then decide (16 ≤ count1179 b) else decide (17 ≤ count1179 b))))) else (if i < 1201 then (if i < 1198 then (if i < 1197 then decide (18 ≤ count1179 b) else decide (19 ≤ count1179 b)) else (if i < 1199 then decide (20 ≤ count1179 b) else (if i < 1200 then decide (21 ≤ count1179 b) else decide (22 ≤ count1179 b)))) else (if i < 1204 then (if i < 1202 then decide (23 ≤ count1179 b) else (if i < 1203 then decide (24 ≤ count1179 b) else decide (25 ≤ count1179 b))) else (if i < 1205 then decide (26 ≤ count1179 b) else (if i < 1206 then decide (27 ≤ count1179 b) else decide (28 ≤ count1179 b)))))) else (if i < 1218 then (if i < 1212 then (if i < 1209 then (if i < 1208 then decide (29 ≤ count1179 b) else decide (30 ≤ count1179 b)) else (if i < 1210 then decide (31 ≤ count1179 b) else (if i < 1211 then decide (32 ≤ count1179 b) else decide (33 ≤ count1179 b)))) else (if i < 1215 then (if i < 1213 then decide (34 ≤ count1179 b) else (if i < 1214 then decide (35 ≤ count1179 b) else decide (36 ≤ count1179 b))) else (if i < 1216 then decide (37 ≤ count1179 b) else (if i < 1217 then decide (38 ≤ count1179 b) else decide (39 ≤ count1179 b))))) else (if i < 1223 then (if i < 1220 then (if i < 1219 then decide (40 ≤ count1179 b) else decide (41 ≤ count1179 b)) else (if i < 1221 then decide (42 ≤ count1179 b) else (if i < 1222 then decide (1 ≤ count1221 b) else decide (2 ≤ count1221 b)))) else (if i < 1226 then (if i < 1224 then decide (1 ≤ count1223 b) else (if i < 1225 then decide (2 ≤ count1223 b) else decide (3 ≤ count1223 b))) else (if i < 1227 then decide (1 ≤ count1226 b) else (if i < 1228 then decide (2 ≤ count1226 b) else decide (1 ≤ count1228 b))))))))) else (if i < 1317 then (if i < 1273 then (if i < 1251 then (if i < 1240 then (if i < 1234 then (if i < 1231 then (if i < 1230 then decide (2 ≤ count1228 b) else decide (3 ≤ count1228 b)) else (if i < 1232 then decide (1 ≤ count1231 b) else (if i < 1233 then decide (2 ≤ count1231 b) else decide (3 ≤ count1231 b)))) else (if i < 1237 then (if i < 1235 then decide (4 ≤ count1231 b) else (if i < 1236 then decide (5 ≤ count1231 b) else decide (6 ≤ count1231 b))) else (if i < 1238 then decide (1 ≤ count1237 b) else (if i < 1239 then decide (2 ≤ count1237 b) else decide (1 ≤ count1239 b))))) else (if i < 1245 then (if i < 1242 then (if i < 1241 then decide (2 ≤ count1239 b) else decide (3 ≤ count1239 b)) else (if i < 1243 then decide (1 ≤ count1242 b) else (if i < 1244 then decide (2 ≤ count1242 b) else decide (1 ≤ count1244 b)))) else (if i < 1248 then (if i < 1246 then decide (2 ≤ count1244 b) else (if i < 1247 then decide (3 ≤ count1244 b) else decide (1 ≤ count1247 b))) else (if i < 1249 then decide (2 ≤ count1247 b) else (if i < 1250 then decide (3 ≤ count1247 b) else decide (4 ≤ count1247 b)))))) else (if i < 1262 then (if i < 1256 then (if i < 1253 then (if i < 1252 then decide (5 ≤ count1247 b) else decide (6 ≤ count1247 b)) else (if i < 1254 then decide (1 ≤ count1253 b) else (if i < 1255 then decide (2 ≤ count1253 b) else decide (3 ≤ count1253 b)))) else (if i < 1259 then (if i < 1257 then decide (4 ≤ count1253 b) else (if i < 1258 then decide (5 ≤ count1253 b) else decide (6 ≤ count1253 b))) else (if i < 1260 then decide (7 ≤ count1253 b) else (if i < 1261 then decide (8 ≤ count1253 b) else decide (1 ≤ count1261 b))))) else (if i < 1267 then (if i < 1264 then (if i < 1263 then decide (2 ≤ count1261 b) else decide (1 ≤ count1263 b)) else (if i < 1265 then decide (2 ≤ count1263 b) else (if i < 1266 then decide (3 ≤ count1263 b) else decide (1 ≤ count1266 b)))) else (if i < 1270 then (if i < 1268 then decide (2 ≤ count1266 b) else (if i < 1269 then decide (1 ≤ count1268 b) else decide (2 ≤ count1268 b))) else (if i < 1271 then decide (3 ≤ count1268 b) else (if i < 1272 then decide (1 ≤ count1271 b) else decide (2 ≤ count1271 b))))))) else (if i < 1295 then (if i < 1284 then (if i < 1278 then (if i < 1275 then (if i < 1274 then decide (3 ≤ count1271 b) else decide (4 ≤ count1271 b)) else (if i < 1276 then decide (5 ≤ count1271 b) else (if i < 1277 then decide (6 ≤ count1271 b) else decide (1 ≤ count1277 b)))) else (if i < 1281 then (if i < 1279 then decide (2 ≤ count1277 b) else (if i < 1280 then decide (1 ≤ count1279 b) else decide (2 ≤ count1279 b))) else (if i < 1282 then decide (3 ≤ count1279 b) else (if i < 1283 then decide (1 ≤ count1282 b) else decide (2 ≤ count1282 b))))) else (if i < 1289 then (if i < 1286 then (if i < 1285 then decide (1 ≤ count1284 b) else decide (2 ≤ count1284 b)) else (if i < 1287 then decide (3 ≤ count1284 b) else (if i < 1288 then decide (1 ≤ count1287 b) else decide (2 ≤ count1287 b)))) else (if i < 1292 then (if i < 1290 then decide (3 ≤ count1287 b) else (if i < 1291 then decide (4 ≤ count1287 b) else decide (5 ≤ count1287 b))) else (if i < 1293 then decide (6 ≤ count1287 b) else (if i < 1294 then decide (1 ≤ count1293 b) else decide (2 ≤ count1293 b)))))) else (if i < 1306 then (if i < 1300 then (if i < 1297 then (if i < 1296 then decide (3 ≤ count1293 b) else decide (4 ≤ count1293 b)) else (if i < 1298 then decide (5 ≤ count1293 b) else (if i < 1299 then decide (6 ≤ count1293 b) else decide (7 ≤ count1293 b)))) else (if i < 1303 then (if i < 1301 then decide (8 ≤ count1293 b) else (if i < 1302 then decide (1 ≤ count1301 b) else decide (2 ≤ count1301 b))) else (if i < 1304 then decide (3 ≤ count1301 b) else (if i < 1305 then decide (4 ≤ count1301 b) else decide (5 ≤ count1301 b))))) else (if i < 1311 then (if i < 1308 then (if i < 1307 then decide (6 ≤ count1301 b) else decide (7 ≤ count1301 b)) else (if i < 1309 then decide (8 ≤ count1301 b) else (if i < 1310 then decide (1 ≤ count1309 b) else decide (2 ≤ count1309 b)))) else (if i < 1314 then (if i < 1312 then decide (1 ≤ count1311 b) else (if i < 1313 then decide (2 ≤ count1311 b) else decide (3 ≤ count1311 b))) else (if i < 1315 then decide (1 ≤ count1314 b) else (if i < 1316 then decide (2 ≤ count1314 b) else decide (1 ≤ count1316 b)))))))) else (if i < 1361 then (if i < 1339 then (if i < 1328 then (if i < 1322 then (if i < 1319 then (if i < 1318 then decide (2 ≤ count1316 b) else decide (3 ≤ count1316 b)) else (if i < 1320 then decide (1 ≤ count1319 b) else (if i < 1321 then decide (2 ≤ count1319 b) else decide (3 ≤ count1319 b)))) else (if i < 1325 then (if i < 1323 then decide (4 ≤ count1319 b) else (if i < 1324 then decide (5 ≤ count1319 b) else decide (6 ≤ count1319 b))) else (if i < 1326 then decide (1 ≤ count1325 b) else (if i < 1327 then decide (2 ≤ count1325 b) else decide (1 ≤ count1327 b))))) else (if i < 1333 then (if i < 1330 then (if i < 1329 then decide (2 ≤ count1327 b) else decide (3 ≤ count1327 b)) else (if i < 1331 then decide (1 ≤ count1330 b) else (if i < 1332 then decide (2 ≤ count1330 b) else decide (1 ≤ count1332 b)))) else (if i < 1336 then (if i < 1334 then decide (2 ≤ count1332 b) else (if i < 1335 then decide (3 ≤ count1332 b) else decide (1 ≤ count1335 b))) else (if i < 1337 then decide (2 ≤ count1335 b) else (if i < 1338 then decide (3 ≤ count1335 b) else decide (4 ≤ count1335 b)))))) else (if i < 1350 then (if i < 1344 then (if i < 1341 then (if i < 1340 then decide (5 ≤ count1335 b) else decide (6 ≤ count1335 b)) else (if i < 1342 then decide (1 ≤ count1341 b) else (if i < 1343 then decide (2 ≤ count1341 b) else decide (3 ≤ count1341 b)))) else (if i < 1347 then (if i < 1345 then decide (4 ≤ count1341 b) else (if i < 1346 then decide (5 ≤ count1341 b) else decide (6 ≤ count1341 b))) else (if i < 1348 then decide (7 ≤ count1341 b) else (if i < 1349 then decide (8 ≤ count1341 b) else decide (1 ≤ count1349 b))))) else (if i < 1355 then (if i < 1352 then (if i < 1351 then decide (2 ≤ count1349 b) else decide (1 ≤ count1351 b)) else (if i < 1353 then decide (2 ≤ count1351 b) else (if i < 1354 then decide (3 ≤ count1351 b) else decide (1 ≤ count1354 b)))) else (if i < 1358 then (if i < 1356 then decide (2 ≤ count1354 b) else (if i < 1357 then decide (1 ≤ count1356 b) else decide (2 ≤ count1356 b))) else (if i < 1359 then decide (3 ≤ count1356 b) else (if i < 1360 then decide (1 ≤ count1359 b) else decide (2 ≤ count1359 b))))))) else (if i < 1383 then (if i < 1372 then (if i < 1366 then (if i < 1363 then (if i < 1362 then decide (3 ≤ count1359 b) else decide (4 ≤ count1359 b)) else (if i < 1364 then decide (5 ≤ count1359 b) else (if i < 1365 then decide (6 ≤ count1359 b) else decide (1 ≤ count1365 b)))) else (if i < 1369 then (if i < 1367 then decide (2 ≤ count1365 b) else (if i < 1368 then decide (1 ≤ count1367 b) else decide (2 ≤ count1367 b))) else (if i < 1370 then decide (3 ≤ count1367 b) else (if i < 1371 then decide (1 ≤ count1370 b) else decide (2 ≤ count1370 b))))) else (if i < 1377 then (if i < 1374 then (if i < 1373 then decide (1 ≤ count1372 b) else decide (2 ≤ count1372 b)) else (if i < 1375 then decide (3 ≤ count1372 b) else (if i < 1376 then decide (1 ≤ count1375 b) else decide (2 ≤ count1375 b)))) else (if i < 1380 then (if i < 1378 then decide (3 ≤ count1375 b) else (if i < 1379 then decide (4 ≤ count1375 b) else decide (5 ≤ count1375 b))) else (if i < 1381 then decide (6 ≤ count1375 b) else (if i < 1382 then decide (1 ≤ count1381 b) else decide (2 ≤ count1381 b)))))) else (if i < 1394 then (if i < 1388 then (if i < 1385 then (if i < 1384 then decide (3 ≤ count1381 b) else decide (4 ≤ count1381 b)) else (if i < 1386 then decide (5 ≤ count1381 b) else (if i < 1387 then decide (6 ≤ count1381 b) else decide (7 ≤ count1381 b)))) else (if i < 1391 then (if i < 1389 then decide (8 ≤ count1381 b) else (if i < 1390 then decide (1 ≤ count1389 b) else decide (2 ≤ count1389 b))) else (if i < 1392 then decide (3 ≤ count1389 b) else (if i < 1393 then decide (4 ≤ count1389 b) else decide (5 ≤ count1389 b))))) else (if i < 1399 then (if i < 1396 then (if i < 1395 then decide (6 ≤ count1389 b) else decide (7 ≤ count1389 b)) else (if i < 1397 then decide (8 ≤ count1389 b) else (if i < 1398 then decide (1 ≤ count1397 b) else decide (2 ≤ count1397 b)))) else (if i < 1402 then (if i < 1400 then decide (3 ≤ count1397 b) else (if i < 1401 then decide (4 ≤ count1397 b) else decide (5 ≤ count1397 b))) else (if i < 1403 then decide (6 ≤ count1397 b) else (if i < 1404 then decide (7 ≤ count1397 b) else decide (8 ≤ count1397 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (40 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (41 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (42 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (44 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (97 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (104 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (105 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (109 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (114 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (115 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (118 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (122 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (124 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (126 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (135 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (136 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (137 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (138 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (140 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (142 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (148 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (149 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (151 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (153 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (154 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (155 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (159 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (198 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (200 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (201 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (205 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (207 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (214 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (218 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (220 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (221 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (222 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (230 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (232 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (236 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (238 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (268 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (296 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (297 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (301 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (391 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (392 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (402 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (403 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (406 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (410 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (481 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (486 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (487 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (488 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (489 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (493 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (502 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (506 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (508 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (510 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (41 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (104 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (124 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value350 (q : Snake 81) : valuation q 350 = decide (2 ≤ count349 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value1221 (q : Snake 81) : valuation q 1221 = decide (1 ≤ count1221 (baseVal q)) := rfl
theorem value1223 (q : Snake 81) : valuation q 1223 = decide (1 ≤ count1223 (baseVal q)) := rfl
theorem value1231 (q : Snake 81) : valuation q 1231 = decide (1 ≤ count1231 (baseVal q)) := rfl
theorem value1237 (q : Snake 81) : valuation q 1237 = decide (1 ≤ count1237 (baseVal q)) := rfl
theorem value1239 (q : Snake 81) : valuation q 1239 = decide (1 ≤ count1239 (baseVal q)) := rfl
theorem value1240 (q : Snake 81) : valuation q 1240 = decide (2 ≤ count1239 (baseVal q)) := rfl
theorem value1242 (q : Snake 81) : valuation q 1242 = decide (1 ≤ count1242 (baseVal q)) := rfl
theorem value1244 (q : Snake 81) : valuation q 1244 = decide (1 ≤ count1244 (baseVal q)) := rfl
theorem value1245 (q : Snake 81) : valuation q 1245 = decide (2 ≤ count1244 (baseVal q)) := rfl
theorem value1247 (q : Snake 81) : valuation q 1247 = decide (1 ≤ count1247 (baseVal q)) := rfl
theorem value1248 (q : Snake 81) : valuation q 1248 = decide (2 ≤ count1247 (baseVal q)) := rfl
theorem value1253 (q : Snake 81) : valuation q 1253 = decide (1 ≤ count1253 (baseVal q)) := rfl
theorem value1254 (q : Snake 81) : valuation q 1254 = decide (2 ≤ count1253 (baseVal q)) := rfl
theorem value1261 (q : Snake 81) : valuation q 1261 = decide (1 ≤ count1261 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (2 ≤ count1261 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (1 ≤ count1263 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (2 ≤ count1263 (baseVal q)) := rfl
theorem value1266 (q : Snake 81) : valuation q 1266 = decide (1 ≤ count1266 (baseVal q)) := rfl
theorem value1268 (q : Snake 81) : valuation q 1268 = decide (1 ≤ count1268 (baseVal q)) := rfl
theorem value1269 (q : Snake 81) : valuation q 1269 = decide (2 ≤ count1268 (baseVal q)) := rfl
theorem value1271 (q : Snake 81) : valuation q 1271 = decide (1 ≤ count1271 (baseVal q)) := rfl
theorem value1272 (q : Snake 81) : valuation q 1272 = decide (2 ≤ count1271 (baseVal q)) := rfl
theorem value1273 (q : Snake 81) : valuation q 1273 = decide (3 ≤ count1271 (baseVal q)) := rfl
theorem value1277 (q : Snake 81) : valuation q 1277 = decide (1 ≤ count1277 (baseVal q)) := rfl
theorem value1278 (q : Snake 81) : valuation q 1278 = decide (2 ≤ count1277 (baseVal q)) := rfl
theorem value1279 (q : Snake 81) : valuation q 1279 = decide (1 ≤ count1279 (baseVal q)) := rfl
theorem value1280 (q : Snake 81) : valuation q 1280 = decide (2 ≤ count1279 (baseVal q)) := rfl
theorem value1282 (q : Snake 81) : valuation q 1282 = decide (1 ≤ count1282 (baseVal q)) := rfl
theorem value1283 (q : Snake 81) : valuation q 1283 = decide (2 ≤ count1282 (baseVal q)) := rfl
theorem value1284 (q : Snake 81) : valuation q 1284 = decide (1 ≤ count1284 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (2 ≤ count1284 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (3 ≤ count1284 (baseVal q)) := rfl
theorem value1287 (q : Snake 81) : valuation q 1287 = decide (1 ≤ count1287 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (2 ≤ count1287 (baseVal q)) := rfl
theorem value1289 (q : Snake 81) : valuation q 1289 = decide (3 ≤ count1287 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (1 ≤ count1293 (baseVal q)) := rfl
theorem value1294 (q : Snake 81) : valuation q 1294 = decide (2 ≤ count1293 (baseVal q)) := rfl
theorem value1295 (q : Snake 81) : valuation q 1295 = decide (3 ≤ count1293 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (4 ≤ count1293 (baseVal q)) := rfl
theorem value1302 (q : Snake 81) : valuation q 1302 = decide (2 ≤ count1301 (baseVal q)) := rfl
theorem value1303 (q : Snake 81) : valuation q 1303 = decide (3 ≤ count1301 (baseVal q)) := rfl
theorem value1304 (q : Snake 81) : valuation q 1304 = decide (4 ≤ count1301 (baseVal q)) := rfl
theorem value1305 (q : Snake 81) : valuation q 1305 = decide (5 ≤ count1301 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (1 ≤ count1309 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (1 ≤ count1311 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (2 ≤ count1311 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (1 ≤ count1314 (baseVal q)) := rfl
theorem value1316 (q : Snake 81) : valuation q 1316 = decide (1 ≤ count1316 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (2 ≤ count1316 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (1 ≤ count1319 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (2 ≤ count1319 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (3 ≤ count1319 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (4 ≤ count1319 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (1 ≤ count1330 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (2 ≤ count1332 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (2 ≤ count1335 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (1 ≤ count1341 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (2 ≤ count1341 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (3 ≤ count1341 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (4 ≤ count1341 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (1 ≤ count1351 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (1 ≤ count1354 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (1 ≤ count1356 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (1 ≤ count1359 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (2 ≤ count1359 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (1 ≤ count1365 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (1 ≤ count1367 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (1 ≤ count1370 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (1 ≤ count1372 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (1 ≤ count1375 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (2 ≤ count1375 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (1 ≤ count1381 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (2 ≤ count1381 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (3 ≤ count1381 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (4 ≤ count1381 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (3 ≤ count1389 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (4 ≤ count1389 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (5 ≤ count1389 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (6 ≤ count1389 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (8 ≤ count1397 (baseVal q)) := rfl
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
theorem meaningNeg93 (b : Nat → Bool) : literal (valuationOf b) (-93) = decide (1 ≤ countLit b [-93]) := by
  change literal b (-93) = decide (1 ≤ countLit b [-93])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-93) <;> decide
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
theorem meaningNeg83 (b : Nat → Bool) : literal (valuationOf b) (-83) = decide (1 ≤ countLit b [-83]) := by
  change literal b (-83) = decide (1 ≤ countLit b [-83])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-83) <;> decide
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
theorem meaningNeg52 (b : Nat → Bool) : literal (valuationOf b) (-52) = decide (1 ≤ countLit b [-52]) := by
  change literal b (-52) = decide (1 ≤ countLit b [-52])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-52) <;> decide
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
theorem meaningNeg45 (b : Nat → Bool) : literal (valuationOf b) (-45) = decide (1 ≤ countLit b [-45]) := by
  change literal b (-45) = decide (1 ≤ countLit b [-45])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-45) <;> decide
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
theorem meaningNeg5 (b : Nat → Bool) : literal (valuationOf b) (-5) = decide (1 ≤ countLit b [-5]) := by
  change literal b (-5) = decide (1 ≤ countLit b [-5])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-5) <;> decide
theorem meaning141 (b : Nat → Bool) : literal (valuationOf b) (141) = decide (1 ≤ countLit b [141]) := by
  change literal b (141) = decide (1 ≤ countLit b [141])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (141) <;> decide
theorem meaning143 (b : Nat → Bool) : literal (valuationOf b) (143) = decide (1 ≤ countLit b [143]) := by
  change literal b (143) = decide (1 ≤ countLit b [143])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (143) <;> decide
theorem meaning153 (b : Nat → Bool) : literal (valuationOf b) (153) = decide (1 ≤ countLit b [153]) := by
  change literal b (153) = decide (1 ≤ countLit b [153])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (153) <;> decide
theorem meaning157 (b : Nat → Bool) : literal (valuationOf b) (157) = decide (1 ≤ countLit b [157]) := by
  change literal b (157) = decide (1 ≤ countLit b [157])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (157) <;> decide
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning350 (b : Nat → Bool) : literal (valuationOf b) 350 = decide (2 ≤ count349 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning402 (b : Nat → Bool) : literal (valuationOf b) 402 = decide (2 ≤ count401 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning1221 (b : Nat → Bool) : literal (valuationOf b) 1221 = decide (1 ≤ count1221 b) := rfl
theorem meaning1223 (b : Nat → Bool) : literal (valuationOf b) 1223 = decide (1 ≤ count1223 b) := rfl
theorem meaning1231 (b : Nat → Bool) : literal (valuationOf b) 1231 = decide (1 ≤ count1231 b) := rfl
theorem meaning1237 (b : Nat → Bool) : literal (valuationOf b) 1237 = decide (1 ≤ count1237 b) := rfl
theorem meaning1239 (b : Nat → Bool) : literal (valuationOf b) 1239 = decide (1 ≤ count1239 b) := rfl
theorem meaning1240 (b : Nat → Bool) : literal (valuationOf b) 1240 = decide (2 ≤ count1239 b) := rfl
theorem meaning1242 (b : Nat → Bool) : literal (valuationOf b) 1242 = decide (1 ≤ count1242 b) := rfl
theorem meaning1244 (b : Nat → Bool) : literal (valuationOf b) 1244 = decide (1 ≤ count1244 b) := rfl
theorem meaning1245 (b : Nat → Bool) : literal (valuationOf b) 1245 = decide (2 ≤ count1244 b) := rfl
theorem meaning1247 (b : Nat → Bool) : literal (valuationOf b) 1247 = decide (1 ≤ count1247 b) := rfl
theorem meaning1248 (b : Nat → Bool) : literal (valuationOf b) 1248 = decide (2 ≤ count1247 b) := rfl
theorem meaning1253 (b : Nat → Bool) : literal (valuationOf b) 1253 = decide (1 ≤ count1253 b) := rfl
theorem meaning1254 (b : Nat → Bool) : literal (valuationOf b) 1254 = decide (2 ≤ count1253 b) := rfl
theorem meaning1261 (b : Nat → Bool) : literal (valuationOf b) 1261 = decide (1 ≤ count1261 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (2 ≤ count1261 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (1 ≤ count1263 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (2 ≤ count1263 b) := rfl
theorem meaning1266 (b : Nat → Bool) : literal (valuationOf b) 1266 = decide (1 ≤ count1266 b) := rfl
theorem meaning1268 (b : Nat → Bool) : literal (valuationOf b) 1268 = decide (1 ≤ count1268 b) := rfl
theorem meaning1269 (b : Nat → Bool) : literal (valuationOf b) 1269 = decide (2 ≤ count1268 b) := rfl
theorem meaning1271 (b : Nat → Bool) : literal (valuationOf b) 1271 = decide (1 ≤ count1271 b) := rfl
theorem meaning1272 (b : Nat → Bool) : literal (valuationOf b) 1272 = decide (2 ≤ count1271 b) := rfl
theorem meaning1273 (b : Nat → Bool) : literal (valuationOf b) 1273 = decide (3 ≤ count1271 b) := rfl
theorem meaning1277 (b : Nat → Bool) : literal (valuationOf b) 1277 = decide (1 ≤ count1277 b) := rfl
theorem meaning1278 (b : Nat → Bool) : literal (valuationOf b) 1278 = decide (2 ≤ count1277 b) := rfl
theorem meaning1279 (b : Nat → Bool) : literal (valuationOf b) 1279 = decide (1 ≤ count1279 b) := rfl
theorem meaning1280 (b : Nat → Bool) : literal (valuationOf b) 1280 = decide (2 ≤ count1279 b) := rfl
theorem meaning1282 (b : Nat → Bool) : literal (valuationOf b) 1282 = decide (1 ≤ count1282 b) := rfl
theorem meaning1283 (b : Nat → Bool) : literal (valuationOf b) 1283 = decide (2 ≤ count1282 b) := rfl
theorem meaning1284 (b : Nat → Bool) : literal (valuationOf b) 1284 = decide (1 ≤ count1284 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (2 ≤ count1284 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (3 ≤ count1284 b) := rfl
theorem meaning1287 (b : Nat → Bool) : literal (valuationOf b) 1287 = decide (1 ≤ count1287 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (2 ≤ count1287 b) := rfl
theorem meaning1289 (b : Nat → Bool) : literal (valuationOf b) 1289 = decide (3 ≤ count1287 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (1 ≤ count1293 b) := rfl
theorem meaning1294 (b : Nat → Bool) : literal (valuationOf b) 1294 = decide (2 ≤ count1293 b) := rfl
theorem meaning1295 (b : Nat → Bool) : literal (valuationOf b) 1295 = decide (3 ≤ count1293 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (4 ≤ count1293 b) := rfl
theorem meaning1302 (b : Nat → Bool) : literal (valuationOf b) 1302 = decide (2 ≤ count1301 b) := rfl
theorem meaning1303 (b : Nat → Bool) : literal (valuationOf b) 1303 = decide (3 ≤ count1301 b) := rfl
theorem meaning1304 (b : Nat → Bool) : literal (valuationOf b) 1304 = decide (4 ≤ count1301 b) := rfl
theorem meaning1305 (b : Nat → Bool) : literal (valuationOf b) 1305 = decide (5 ≤ count1301 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (1 ≤ count1309 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (1 ≤ count1311 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (2 ≤ count1311 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (1 ≤ count1314 b) := rfl
theorem meaning1316 (b : Nat → Bool) : literal (valuationOf b) 1316 = decide (1 ≤ count1316 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (2 ≤ count1316 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (1 ≤ count1319 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (2 ≤ count1319 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (3 ≤ count1319 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (4 ≤ count1319 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (1 ≤ count1330 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (2 ≤ count1332 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (2 ≤ count1335 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (1 ≤ count1341 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (2 ≤ count1341 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (3 ≤ count1341 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (4 ≤ count1341 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (1 ≤ count1351 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (1 ≤ count1354 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (1 ≤ count1356 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (1 ≤ count1359 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (2 ≤ count1359 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (1 ≤ count1365 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (1 ≤ count1367 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (1 ≤ count1370 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (1 ≤ count1372 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (1 ≤ count1375 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (2 ≤ count1375 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (1 ≤ count1381 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (2 ≤ count1381 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (3 ≤ count1381 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (4 ≤ count1381 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (3 ≤ count1389 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (4 ≤ count1389 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (5 ≤ count1389 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (6 ≤ count1389 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (8 ≤ count1397 b) := rfl
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
end Snake9.Regrowth.E112182
