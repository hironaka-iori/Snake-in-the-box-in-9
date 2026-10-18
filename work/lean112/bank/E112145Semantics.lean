import E112145Data
namespace Snake9.Regrowth.E112145
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 104 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 4 then decide (InPath q (6 : Vertex)) else (if i < 5 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (19 : Vertex)) else (if i < 8 then decide (InPath q (22 : Vertex)) else decide (InPath q (32 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (34 : Vertex)) else decide (InPath q (36 : Vertex))) else (if i < 12 then decide (InPath q (38 : Vertex)) else decide (InPath q (39 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (42 : Vertex)) else (if i < 15 then decide (InPath q (44 : Vertex)) else decide (InPath q (46 : Vertex)))) else (if i < 17 then decide (InPath q (52 : Vertex)) else (if i < 18 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (58 : Vertex)) else (if i < 21 then decide (InPath q (96 : Vertex)) else decide (InPath q (97 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (102 : Vertex)) else decide (InPath q (103 : Vertex))) else (if i < 25 then decide (InPath q (104 : Vertex)) else decide (InPath q (109 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (111 : Vertex)) else (if i < 28 then decide (InPath q (113 : Vertex)) else decide (InPath q (114 : Vertex)))) else (if i < 30 then decide (InPath q (115 : Vertex)) else (if i < 31 then decide (InPath q (118 : Vertex)) else decide (InPath q (122 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (124 : Vertex)) else (if i < 34 then decide (InPath q (125 : Vertex)) else decide (InPath q (126 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (128 : Vertex)) else decide (InPath q (130 : Vertex))) else (if i < 38 then decide (InPath q (132 : Vertex)) else decide (InPath q (134 : Vertex)))))) else (if i < 45 then (if i < 42 then (if i < 40 then decide (InPath q (135 : Vertex)) else (if i < 41 then decide (InPath q (136 : Vertex)) else decide (InPath q (137 : Vertex)))) else (if i < 43 then decide (InPath q (138 : Vertex)) else (if i < 44 then decide (InPath q (140 : Vertex)) else decide (InPath q (142 : Vertex))))) else (if i < 48 then (if i < 46 then decide (InPath q (148 : Vertex)) else (if i < 47 then decide (InPath q (149 : Vertex)) else decide (InPath q (151 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (153 : Vertex)) else decide (InPath q (154 : Vertex))) else (if i < 51 then decide (InPath q (155 : Vertex)) else decide (InPath q (159 : Vertex)))))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then decide (InPath q (198 : Vertex)) else (if i < 54 then decide (InPath q (200 : Vertex)) else decide (InPath q (201 : Vertex)))) else (if i < 56 then decide (InPath q (205 : Vertex)) else (if i < 57 then decide (InPath q (207 : Vertex)) else decide (InPath q (214 : Vertex))))) else (if i < 61 then (if i < 59 then decide (InPath q (218 : Vertex)) else (if i < 60 then decide (InPath q (220 : Vertex)) else decide (InPath q (221 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (222 : Vertex)) else decide (InPath q (226 : Vertex))) else (if i < 64 then decide (InPath q (230 : Vertex)) else decide (InPath q (232 : Vertex)))))) else (if i < 71 then (if i < 68 then (if i < 66 then decide (InPath q (236 : Vertex)) else (if i < 67 then decide (InPath q (238 : Vertex)) else decide (InPath q (256 : Vertex)))) else (if i < 69 then decide (InPath q (258 : Vertex)) else (if i < 70 then decide (InPath q (262 : Vertex)) else decide (InPath q (264 : Vertex))))) else (if i < 74 then (if i < 72 then decide (InPath q (268 : Vertex)) else (if i < 73 then decide (InPath q (270 : Vertex)) else decide (InPath q (384 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (385 : Vertex)) else decide (InPath q (390 : Vertex))) else (if i < 77 then decide (InPath q (391 : Vertex)) else decide (InPath q (392 : Vertex))))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then decide (InPath q (393 : Vertex)) else (if i < 80 then decide (InPath q (397 : Vertex)) else decide (InPath q (399 : Vertex)))) else (if i < 82 then decide (InPath q (401 : Vertex)) else (if i < 83 then decide (InPath q (402 : Vertex)) else decide (InPath q (403 : Vertex))))) else (if i < 87 then (if i < 85 then decide (InPath q (406 : Vertex)) else (if i < 86 then decide (InPath q (410 : Vertex)) else decide (InPath q (412 : Vertex)))) else (if i < 89 then (if i < 88 then decide (InPath q (413 : Vertex)) else decide (InPath q (414 : Vertex))) else (if i < 90 then decide (InPath q (480 : Vertex)) else decide (InPath q (481 : Vertex)))))) else (if i < 97 then (if i < 94 then (if i < 92 then decide (InPath q (486 : Vertex)) else (if i < 93 then decide (InPath q (487 : Vertex)) else decide (InPath q (488 : Vertex)))) else (if i < 95 then decide (InPath q (489 : Vertex)) else (if i < 96 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 100 then (if i < 98 then decide (InPath q (497 : Vertex)) else (if i < 99 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 103 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 156 then (if i < 130 then (if i < 117 then (if i < 110 then (if i < 107 then (if i < 105 then decide (InPath q (510 : Vertex)) else (if i < 106 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 108 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else (if i < 109 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex))))) else (if i < 113 then (if i < 111 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (32 : Vertex)))) else (if i < 115 then (if i < 114 then decide (BallClauseLogic.Endpoint q (34 : Vertex)) else decide (BallClauseLogic.Endpoint q (36 : Vertex))) else (if i < 116 then decide (BallClauseLogic.Endpoint q (38 : Vertex)) else decide (BallClauseLogic.Endpoint q (39 : Vertex)))))) else (if i < 123 then (if i < 120 then (if i < 118 then decide (BallClauseLogic.Endpoint q (42 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (44 : Vertex)) else decide (BallClauseLogic.Endpoint q (46 : Vertex)))) else (if i < 121 then decide (BallClauseLogic.Endpoint q (52 : Vertex)) else (if i < 122 then decide (BallClauseLogic.Endpoint q (53 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex))))) else (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (58 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (96 : Vertex)) else decide (BallClauseLogic.Endpoint q (97 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (102 : Vertex)) else decide (BallClauseLogic.Endpoint q (103 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (104 : Vertex)) else decide (BallClauseLogic.Endpoint q (109 : Vertex))))))) else (if i < 143 then (if i < 136 then (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (111 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (113 : Vertex)) else decide (BallClauseLogic.Endpoint q (114 : Vertex)))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (115 : Vertex)) else (if i < 135 then decide (BallClauseLogic.Endpoint q (118 : Vertex)) else decide (BallClauseLogic.Endpoint q (122 : Vertex))))) else (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (124 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (125 : Vertex)) else decide (BallClauseLogic.Endpoint q (126 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (128 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex)))))) else (if i < 149 then (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (136 : Vertex)) else decide (BallClauseLogic.Endpoint q (137 : Vertex)))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (142 : Vertex))))) else (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else decide (BallClauseLogic.Endpoint q (151 : Vertex)))) else (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (153 : Vertex)) else decide (BallClauseLogic.Endpoint q (154 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex)))))))) else (if i < 182 then (if i < 169 then (if i < 162 then (if i < 159 then (if i < 157 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else decide (BallClauseLogic.Endpoint q (201 : Vertex)))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (205 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex))))) else (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex)))) else (if i < 167 then (if i < 166 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else decide (BallClauseLogic.Endpoint q (226 : Vertex))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (230 : Vertex)) else decide (BallClauseLogic.Endpoint q (232 : Vertex)))))) else (if i < 175 then (if i < 172 then (if i < 170 then decide (BallClauseLogic.Endpoint q (236 : Vertex)) else (if i < 171 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else decide (BallClauseLogic.Endpoint q (256 : Vertex)))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (262 : Vertex)) else decide (BallClauseLogic.Endpoint q (264 : Vertex))))) else (if i < 178 then (if i < 176 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (390 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (392 : Vertex))))))) else (if i < 195 then (if i < 188 then (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (393 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else decide (BallClauseLogic.Endpoint q (399 : Vertex)))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else decide (BallClauseLogic.Endpoint q (403 : Vertex))))) else (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (410 : Vertex)) else decide (BallClauseLogic.Endpoint q (412 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))))) else (if i < 202 then (if i < 198 then (if i < 196 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))) else (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 205 then (if i < 203 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else (if i < 204 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
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
def count241 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count243 (b : Nat → Bool) : Nat := countLit b [124, 125, 126]
def count245 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count247 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count249 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130]
def count251 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count269 (b : Nat → Bool) : Nat := countLit b [137, 138, 139]
def count271 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count273 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143]
def count277 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count283 (b : Nat → Bool) : Nat := countLit b [144, 145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148, 149]
def count289 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count293 (b : Nat → Bool) : Nat := countLit b [150, 151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count297 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156]
def count301 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156]
def count303 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169]
def count329 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169]
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
def count357 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182]
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
def count409 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count411 (b : Nat → Bool) : Nat := countLit b [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count413 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count415 (b : Nat → Bool) : Nat := countLit b [1, 3, 4]
def count418 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count420 (b : Nat → Bool) : Nat := countLit b [5, 9, 10]
def count423 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10]
def count429 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count431 (b : Nat → Bool) : Nat := countLit b [12, 15, 17]
def count434 (b : Nat → Bool) : Nat := countLit b [19, 20]
def count436 (b : Nat → Bool) : Nat := countLit b [22, 26]
def count438 (b : Nat → Bool) : Nat := countLit b [19, 20, 22, 26]
def count442 (b : Nat → Bool) : Nat := countLit b [12, 15, 17, 19, 20, 22, 26]
def count449 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 12, 15, 17, 19, 20, 22, 26]
def count462 (b : Nat → Bool) : Nat := countLit b [28, 33]
def count464 (b : Nat → Bool) : Nat := countLit b [27, 28, 33]
def count467 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count469 (b : Nat → Bool) : Nat := countLit b [34, 36, 37]
def count472 (b : Nat → Bool) : Nat := countLit b [27, 28, 33, 34, 36, 37]
def count478 (b : Nat → Bool) : Nat := countLit b [40, 44]
def count480 (b : Nat → Bool) : Nat := countLit b [39, 40, 44]
def count483 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count485 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count487 (b : Nat → Bool) : Nat := countLit b [46, 48, 49, 51]
def count491 (b : Nat → Bool) : Nat := countLit b [39, 40, 44, 46, 48, 49, 51]
def count498 (b : Nat → Bool) : Nat := countLit b [27, 28, 33, 34, 36, 37, 39, 40, 44, 46, 48, 49, 51]
def count511 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 12, 15, 17, 19, 20, 22, 26, 27, 28, 33, 34, 36, 37, 39, 40, 44, 46, 48, 49, 51]
def count537 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count539 (b : Nat → Bool) : Nat := countLit b [52, 54, 56]
def count542 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count544 (b : Nat → Bool) : Nat := countLit b [60, 61, 62]
def count547 (b : Nat → Bool) : Nat := countLit b [52, 54, 56, 60, 61, 62]
def count553 (b : Nat → Bool) : Nat := countLit b [66, 68]
def count555 (b : Nat → Bool) : Nat := countLit b [64, 66, 68]
def count558 (b : Nat → Bool) : Nat := countLit b [70, 72]
def count560 (b : Nat → Bool) : Nat := countLit b [73, 75]
def count562 (b : Nat → Bool) : Nat := countLit b [70, 72, 73, 75]
def count566 (b : Nat → Bool) : Nat := countLit b [64, 66, 68, 70, 72, 73, 75]
def count573 (b : Nat → Bool) : Nat := countLit b [52, 54, 56, 60, 61, 62, 64, 66, 68, 70, 72, 73, 75]
def count586 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count588 (b : Nat → Bool) : Nat := countLit b [78, 80, 81]
def count591 (b : Nat → Bool) : Nat := countLit b [82, 87]
def count593 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count595 (b : Nat → Bool) : Nat := countLit b [82, 87, 88, 89]
def count599 (b : Nat → Bool) : Nat := countLit b [78, 80, 81, 82, 87, 88, 89]
def count606 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count608 (b : Nat → Bool) : Nat := countLit b [91, 94, 96]
def count611 (b : Nat → Bool) : Nat := countLit b [97, 98]
def count613 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count615 (b : Nat → Bool) : Nat := countLit b [97, 98, 103, 104]
def count619 (b : Nat → Bool) : Nat := countLit b [91, 94, 96, 97, 98, 103, 104]
def count626 (b : Nat → Bool) : Nat := countLit b [78, 80, 81, 82, 87, 88, 89, 91, 94, 96, 97, 98, 103, 104]
def count640 (b : Nat → Bool) : Nat := countLit b [52, 54, 56, 60, 61, 62, 64, 66, 68, 70, 72, 73, 75, 78, 80, 81, 82, 87, 88, 89, 91, 94, 96, 97, 98, 103, 104]
def count667 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 9, 10, 12, 15, 17, 19, 20, 22, 26, 27, 28, 33, 34, 36, 37, 39, 40, 44, 46, 48, 49, 51, 52, 54, 56, 60, 61, 62, 64, 66, 68, 70, 72, 73, 75, 78, 80, 81, 82, 87, 88, 89, 91, 94, 96, 97, 98, 103, 104]
def count709 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count711 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4]
def count714 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count716 (b : Nat → Bool) : Nat := countLit b [-5, -9, -10]
def count719 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10]
def count725 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count727 (b : Nat → Bool) : Nat := countLit b [-12, -15, -17]
def count730 (b : Nat → Bool) : Nat := countLit b [-19, -20]
def count732 (b : Nat → Bool) : Nat := countLit b [-22, -26]
def count734 (b : Nat → Bool) : Nat := countLit b [-19, -20, -22, -26]
def count738 (b : Nat → Bool) : Nat := countLit b [-12, -15, -17, -19, -20, -22, -26]
def count745 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26]
def count758 (b : Nat → Bool) : Nat := countLit b [-28, -33]
def count760 (b : Nat → Bool) : Nat := countLit b [-27, -28, -33]
def count763 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count765 (b : Nat → Bool) : Nat := countLit b [-34, -36, -37]
def count768 (b : Nat → Bool) : Nat := countLit b [-27, -28, -33, -34, -36, -37]
def count774 (b : Nat → Bool) : Nat := countLit b [-40, -44]
def count776 (b : Nat → Bool) : Nat := countLit b [-39, -40, -44]
def count779 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count781 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count783 (b : Nat → Bool) : Nat := countLit b [-46, -48, -49, -51]
def count787 (b : Nat → Bool) : Nat := countLit b [-39, -40, -44, -46, -48, -49, -51]
def count794 (b : Nat → Bool) : Nat := countLit b [-27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51]
def count807 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26, -27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51]
def count820 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count822 (b : Nat → Bool) : Nat := countLit b [-52, -54, -56]
def count825 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count827 (b : Nat → Bool) : Nat := countLit b [-60, -61, -62]
def count830 (b : Nat → Bool) : Nat := countLit b [-52, -54, -56, -60, -61, -62]
def count836 (b : Nat → Bool) : Nat := countLit b [-66, -68]
def count838 (b : Nat → Bool) : Nat := countLit b [-64, -66, -68]
def count841 (b : Nat → Bool) : Nat := countLit b [-70, -72]
def count843 (b : Nat → Bool) : Nat := countLit b [-73, -75]
def count845 (b : Nat → Bool) : Nat := countLit b [-70, -72, -73, -75]
def count849 (b : Nat → Bool) : Nat := countLit b [-64, -66, -68, -70, -72, -73, -75]
def count856 (b : Nat → Bool) : Nat := countLit b [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75]
def count869 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count871 (b : Nat → Bool) : Nat := countLit b [-78, -80, -81]
def count874 (b : Nat → Bool) : Nat := countLit b [-82, -87]
def count876 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count878 (b : Nat → Bool) : Nat := countLit b [-82, -87, -88, -89]
def count882 (b : Nat → Bool) : Nat := countLit b [-78, -80, -81, -82, -87, -88, -89]
def count889 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count891 (b : Nat → Bool) : Nat := countLit b [-91, -94, -96]
def count894 (b : Nat → Bool) : Nat := countLit b [-97, -98]
def count896 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count898 (b : Nat → Bool) : Nat := countLit b [-97, -98, -103, -104]
def count902 (b : Nat → Bool) : Nat := countLit b [-91, -94, -96, -97, -98, -103, -104]
def count909 (b : Nat → Bool) : Nat := countLit b [-78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104]
def count922 (b : Nat → Bool) : Nat := countLit b [-52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75, -78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104]
def count935 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -9, -10, -12, -15, -17, -19, -20, -22, -26, -27, -28, -33, -34, -36, -37, -39, -40, -44, -46, -48, -49, -51, -52, -54, -56, -60, -61, -62, -64, -66, -68, -70, -72, -73, -75, -78, -80, -81, -82, -87, -88, -89, -91, -94, -96, -97, -98, -103, -104]
def count948 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count950 (b : Nat → Bool) : Nat := countLit b [2, 6, 7]
def count953 (b : Nat → Bool) : Nat := countLit b [11, 13]
def count955 (b : Nat → Bool) : Nat := countLit b [8, 11, 13]
def count958 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13]
def count964 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count966 (b : Nat → Bool) : Nat := countLit b [14, 16, 18]
def count969 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count971 (b : Nat → Bool) : Nat := countLit b [21, 23, 24]
def count974 (b : Nat → Bool) : Nat := countLit b [14, 16, 18, 21, 23, 24]
def count980 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13, 14, 16, 18, 21, 23, 24]
def count992 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count994 (b : Nat → Bool) : Nat := countLit b [25, 29, 30]
def count997 (b : Nat → Bool) : Nat := countLit b [32, 35]
def count999 (b : Nat → Bool) : Nat := countLit b [31, 32, 35]
def count1002 (b : Nat → Bool) : Nat := countLit b [25, 29, 30, 31, 32, 35]
def count1008 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count1010 (b : Nat → Bool) : Nat := countLit b [38, 41, 42]
def count1013 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count1015 (b : Nat → Bool) : Nat := countLit b [47, 50]
def count1017 (b : Nat → Bool) : Nat := countLit b [43, 45, 47, 50]
def count1021 (b : Nat → Bool) : Nat := countLit b [38, 41, 42, 43, 45, 47, 50]
def count1028 (b : Nat → Bool) : Nat := countLit b [25, 29, 30, 31, 32, 35, 38, 41, 42, 43, 45, 47, 50]
def count1041 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13, 14, 16, 18, 21, 23, 24, 25, 29, 30, 31, 32, 35, 38, 41, 42, 43, 45, 47, 50]
def count1066 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count1068 (b : Nat → Bool) : Nat := countLit b [53, 55, 57]
def count1071 (b : Nat → Bool) : Nat := countLit b [59, 63]
def count1073 (b : Nat → Bool) : Nat := countLit b [58, 59, 63]
def count1076 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 58, 59, 63]
def count1082 (b : Nat → Bool) : Nat := countLit b [67, 69]
def count1084 (b : Nat → Bool) : Nat := countLit b [65, 67, 69]
def count1087 (b : Nat → Bool) : Nat := countLit b [71, 74]
def count1089 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count1091 (b : Nat → Bool) : Nat := countLit b [71, 74, 76, 77]
def count1095 (b : Nat → Bool) : Nat := countLit b [65, 67, 69, 71, 74, 76, 77]
def count1102 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 58, 59, 63, 65, 67, 69, 71, 74, 76, 77]
def count1115 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count1117 (b : Nat → Bool) : Nat := countLit b [79, 83, 84]
def count1120 (b : Nat → Bool) : Nat := countLit b [86, 90]
def count1122 (b : Nat → Bool) : Nat := countLit b [85, 86, 90]
def count1125 (b : Nat → Bool) : Nat := countLit b [79, 83, 84, 85, 86, 90]
def count1131 (b : Nat → Bool) : Nat := countLit b [93, 95]
def count1133 (b : Nat → Bool) : Nat := countLit b [92, 93, 95]
def count1136 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count1138 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count1140 (b : Nat → Bool) : Nat := countLit b [99, 100, 101, 102]
def count1144 (b : Nat → Bool) : Nat := countLit b [92, 93, 95, 99, 100, 101, 102]
def count1151 (b : Nat → Bool) : Nat := countLit b [79, 83, 84, 85, 86, 90, 92, 93, 95, 99, 100, 101, 102]
def count1164 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 58, 59, 63, 65, 67, 69, 71, 74, 76, 77, 79, 83, 84, 85, 86, 90, 92, 93, 95, 99, 100, 101, 102]
def count1190 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 8, 11, 13, 14, 16, 18, 21, 23, 24, 25, 29, 30, 31, 32, 35, 38, 41, 42, 43, 45, 47, 50, 53, 55, 57, 58, 59, 63, 65, 67, 69, 71, 74, 76, 77, 79, 83, 84, 85, 86, 90, 92, 93, 95, 99, 100, 101, 102]
def count1232 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count1234 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7]
def count1237 (b : Nat → Bool) : Nat := countLit b [-11, -13]
def count1239 (b : Nat → Bool) : Nat := countLit b [-8, -11, -13]
def count1242 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13]
def count1248 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1250 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18]
def count1253 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count1255 (b : Nat → Bool) : Nat := countLit b [-21, -23, -24]
def count1258 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18, -21, -23, -24]
def count1264 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24]
def count1275 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count1277 (b : Nat → Bool) : Nat := countLit b [-25, -29, -30]
def count1280 (b : Nat → Bool) : Nat := countLit b [-32, -35]
def count1282 (b : Nat → Bool) : Nat := countLit b [-31, -32, -35]
def count1285 (b : Nat → Bool) : Nat := countLit b [-25, -29, -30, -31, -32, -35]
def count1291 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count1293 (b : Nat → Bool) : Nat := countLit b [-38, -41, -42]
def count1296 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count1298 (b : Nat → Bool) : Nat := countLit b [-47, -50]
def count1300 (b : Nat → Bool) : Nat := countLit b [-43, -45, -47, -50]
def count1304 (b : Nat → Bool) : Nat := countLit b [-38, -41, -42, -43, -45, -47, -50]
def count1311 (b : Nat → Bool) : Nat := countLit b [-25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]
def count1322 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50]
def count1333 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count1335 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57]
def count1338 (b : Nat → Bool) : Nat := countLit b [-59, -63]
def count1340 (b : Nat → Bool) : Nat := countLit b [-58, -59, -63]
def count1343 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -58, -59, -63]
def count1349 (b : Nat → Bool) : Nat := countLit b [-67, -69]
def count1351 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69]
def count1354 (b : Nat → Bool) : Nat := countLit b [-71, -74]
def count1356 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count1358 (b : Nat → Bool) : Nat := countLit b [-71, -74, -76, -77]
def count1362 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69, -71, -74, -76, -77]
def count1369 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77]
def count1380 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count1382 (b : Nat → Bool) : Nat := countLit b [-79, -83, -84]
def count1385 (b : Nat → Bool) : Nat := countLit b [-86, -90]
def count1387 (b : Nat → Bool) : Nat := countLit b [-85, -86, -90]
def count1390 (b : Nat → Bool) : Nat := countLit b [-79, -83, -84, -85, -86, -90]
def count1396 (b : Nat → Bool) : Nat := countLit b [-93, -95]
def count1398 (b : Nat → Bool) : Nat := countLit b [-92, -93, -95]
def count1401 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1403 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count1405 (b : Nat → Bool) : Nat := countLit b [-99, -100, -101, -102]
def count1409 (b : Nat → Bool) : Nat := countLit b [-92, -93, -95, -99, -100, -101, -102]
def count1416 (b : Nat → Bool) : Nat := countLit b [-79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]
def count1427 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]
def count1438 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -8, -11, -13, -14, -16, -18, -21, -23, -24, -25, -29, -30, -31, -32, -35, -38, -41, -42, -43, -45, -47, -50, -53, -55, -57, -58, -59, -63, -65, -67, -69, -71, -74, -76, -77, -79, -83, -84, -85, -86, -90, -92, -93, -95, -99, -100, -101, -102]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 724 then (if i < 362 then (if i < 181 then (if i < 90 then (if i < 45 then (if i < 22 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 16 then (if i < 13 then (if i < 12 then b 11 else b 12) else (if i < 14 then b 13 else (if i < 15 then b 14 else b 15))) else (if i < 19 then (if i < 17 then b 16 else (if i < 18 then b 17 else b 18)) else (if i < 20 then b 19 else (if i < 21 then b 20 else b 21))))) else (if i < 33 then (if i < 27 then (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else (if i < 26 then b 25 else b 26))) else (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)))) else (if i < 39 then (if i < 36 then (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)) else (if i < 37 then b 36 else (if i < 38 then b 37 else b 38))) else (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)))))) else (if i < 67 then (if i < 56 then (if i < 50 then (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else (if i < 49 then b 48 else b 49))) else (if i < 53 then (if i < 51 then b 50 else (if i < 52 then b 51 else b 52)) else (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)))) else (if i < 61 then (if i < 58 then (if i < 57 then b 56 else b 57) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60))) else (if i < 64 then (if i < 62 then b 61 else (if i < 63 then b 62 else b 63)) else (if i < 65 then b 64 else (if i < 66 then b 65 else b 66))))) else (if i < 78 then (if i < 72 then (if i < 69 then (if i < 68 then b 67 else b 68) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))) else (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)))) else (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))))))) else (if i < 135 then (if i < 112 then (if i < 101 then (if i < 95 then (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))) else (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)))) else (if i < 106 then (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else (if i < 105 then b 104 else b 105))) else (if i < 109 then (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111))))) else (if i < 123 then (if i < 117 then (if i < 114 then (if i < 113 then b 112 else b 113) else (if i < 115 then b 114 else (if i < 116 then b 115 else b 116))) else (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)))) else (if i < 129 then (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 127 then b 126 else (if i < 128 then b 127 else b 128))) else (if i < 132 then (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)) else (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)))))) else (if i < 158 then (if i < 146 then (if i < 140 then (if i < 137 then (if i < 136 then b 135 else b 136) else (if i < 138 then b 137 else (if i < 139 then b 138 else b 139))) else (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)))) else (if i < 152 then (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 150 then b 149 else (if i < 151 then b 150 else b 151))) else (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 156 then b 155 else (if i < 157 then b 156 else b 157))))) else (if i < 169 then (if i < 163 then (if i < 160 then (if i < 159 then b 158 else b 159) else (if i < 161 then b 160 else (if i < 162 then b 161 else b 162))) else (if i < 166 then (if i < 164 then b 163 else (if i < 165 then b 164 else b 165)) else (if i < 167 then b 166 else (if i < 168 then b 167 else b 168)))) else (if i < 175 then (if i < 172 then (if i < 170 then b 169 else (if i < 171 then b 170 else b 171)) else (if i < 173 then b 172 else (if i < 174 then b 173 else b 174))) else (if i < 178 then (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)) else (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)))))))) else (if i < 271 then (if i < 226 then (if i < 203 then (if i < 192 then (if i < 186 then (if i < 183 then (if i < 182 then b 181 else b 182) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185))) else (if i < 189 then (if i < 187 then b 186 else (if i < 188 then b 187 else b 188)) else (if i < 190 then b 189 else (if i < 191 then b 190 else b 191)))) else (if i < 197 then (if i < 194 then (if i < 193 then b 192 else b 193) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196))) else (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 201 then b 200 else (if i < 202 then b 201 else b 202))))) else (if i < 214 then (if i < 208 then (if i < 205 then (if i < 204 then b 203 else b 204) else (if i < 206 then b 205 else (if i < 207 then b 206 else b 207))) else (if i < 211 then (if i < 209 then b 208 else (if i < 210 then decide (1 ≤ count209 b) else decide (2 ≤ count209 b))) else (if i < 212 then decide (1 ≤ count211 b) else (if i < 213 then decide (2 ≤ count211 b) else decide (1 ≤ count213 b))))) else (if i < 220 then (if i < 217 then (if i < 215 then decide (2 ≤ count213 b) else (if i < 216 then decide (1 ≤ count215 b) else decide (2 ≤ count215 b))) else (if i < 218 then decide (1 ≤ count217 b) else (if i < 219 then decide (2 ≤ count217 b) else decide (1 ≤ count219 b)))) else (if i < 223 then (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b))) else (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b))))))) else (if i < 248 then (if i < 237 then (if i < 231 then (if i < 228 then (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b)) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b)))) else (if i < 234 then (if i < 232 then decide (1 ≤ count231 b) else (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b))) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b))))) else (if i < 242 then (if i < 239 then (if i < 238 then decide (1 ≤ count237 b) else decide (2 ≤ count237 b)) else (if i < 240 then decide (1 ≤ count239 b) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b)))) else (if i < 245 then (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b))) else (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b)))))) else (if i < 259 then (if i < 253 then (if i < 250 then (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b)) else (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)))) else (if i < 256 then (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b))) else (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))))) else (if i < 265 then (if i < 262 then (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))) else (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))) else (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)))))))) else (if i < 316 then (if i < 293 then (if i < 282 then (if i < 276 then (if i < 273 then (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)) else (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)))) else (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))))) else (if i < 287 then (if i < 284 then (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)) else (if i < 285 then decide (2 ≤ count283 b) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)))) else (if i < 290 then (if i < 288 then decide (1 ≤ count287 b) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b))) else (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))))) else (if i < 304 then (if i < 298 then (if i < 295 then (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)) else (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)))) else (if i < 301 then (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))) else (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))))) else (if i < 310 then (if i < 307 then (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))) else (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)))) else (if i < 313 then (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))) else (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))))))) else (if i < 339 then (if i < 327 then (if i < 321 then (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)))) else (if i < 324 then (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b))) else (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))))) else (if i < 333 then (if i < 330 then (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b))) else (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)))) else (if i < 336 then (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))))) else (if i < 350 then (if i < 344 then (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b)))) else (if i < 347 then (if i < 345 then decide (2 ≤ count343 b) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b))) else (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))))) else (if i < 356 then (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b)))) else (if i < 359 then (if i < 357 then decide (2 ≤ count355 b) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b))) else (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)))))))))) else (if i < 543 then (if i < 452 then (if i < 407 then (if i < 384 then (if i < 373 then (if i < 367 then (if i < 364 then (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)))) else (if i < 370 then (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))) else (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))))) else (if i < 378 then (if i < 375 then (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)) else (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)))) else (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)))))) else (if i < 395 then (if i < 389 then (if i < 386 then (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b))))) else (if i < 401 then (if i < 398 then (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))) else (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)))) else (if i < 404 then (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))))))) else (if i < 429 then (if i < 418 then (if i < 412 then (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b)))) else (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (3 ≤ count415 b))))) else (if i < 423 then (if i < 420 then (if i < 419 then decide (1 ≤ count418 b) else decide (2 ≤ count418 b)) else (if i < 421 then decide (1 ≤ count420 b) else (if i < 422 then decide (2 ≤ count420 b) else decide (3 ≤ count420 b)))) else (if i < 426 then (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (3 ≤ count423 b))) else (if i < 427 then decide (4 ≤ count423 b) else (if i < 428 then decide (5 ≤ count423 b) else decide (6 ≤ count423 b)))))) else (if i < 440 then (if i < 434 then (if i < 431 then (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)) else (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (3 ≤ count431 b)))) else (if i < 437 then (if i < 435 then decide (1 ≤ count434 b) else (if i < 436 then decide (2 ≤ count434 b) else decide (1 ≤ count436 b))) else (if i < 438 then decide (2 ≤ count436 b) else (if i < 439 then decide (1 ≤ count438 b) else decide (2 ≤ count438 b))))) else (if i < 446 then (if i < 443 then (if i < 441 then decide (3 ≤ count438 b) else (if i < 442 then decide (4 ≤ count438 b) else decide (1 ≤ count442 b))) else (if i < 444 then decide (2 ≤ count442 b) else (if i < 445 then decide (3 ≤ count442 b) else decide (4 ≤ count442 b)))) else (if i < 449 then (if i < 447 then decide (5 ≤ count442 b) else (if i < 448 then decide (6 ≤ count442 b) else decide (7 ≤ count442 b))) else (if i < 450 then decide (1 ≤ count449 b) else (if i < 451 then decide (2 ≤ count449 b) else decide (3 ≤ count449 b)))))))) else (if i < 497 then (if i < 474 then (if i < 463 then (if i < 457 then (if i < 454 then (if i < 453 then decide (4 ≤ count449 b) else decide (5 ≤ count449 b)) else (if i < 455 then decide (6 ≤ count449 b) else (if i < 456 then decide (7 ≤ count449 b) else decide (8 ≤ count449 b)))) else (if i < 460 then (if i < 458 then decide (9 ≤ count449 b) else (if i < 459 then decide (10 ≤ count449 b) else decide (11 ≤ count449 b))) else (if i < 461 then decide (12 ≤ count449 b) else (if i < 462 then decide (13 ≤ count449 b) else decide (1 ≤ count462 b))))) else (if i < 468 then (if i < 465 then (if i < 464 then decide (2 ≤ count462 b) else decide (1 ≤ count464 b)) else (if i < 466 then decide (2 ≤ count464 b) else (if i < 467 then decide (3 ≤ count464 b) else decide (1 ≤ count467 b)))) else (if i < 471 then (if i < 469 then decide (2 ≤ count467 b) else (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b))) else (if i < 472 then decide (3 ≤ count469 b) else (if i < 473 then decide (1 ≤ count472 b) else decide (2 ≤ count472 b)))))) else (if i < 485 then (if i < 479 then (if i < 476 then (if i < 475 then decide (3 ≤ count472 b) else decide (4 ≤ count472 b)) else (if i < 477 then decide (5 ≤ count472 b) else (if i < 478 then decide (6 ≤ count472 b) else decide (1 ≤ count478 b)))) else (if i < 482 then (if i < 480 then decide (2 ≤ count478 b) else (if i < 481 then decide (1 ≤ count480 b) else decide (2 ≤ count480 b))) else (if i < 483 then decide (3 ≤ count480 b) else (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b))))) else (if i < 491 then (if i < 488 then (if i < 486 then decide (1 ≤ count485 b) else (if i < 487 then decide (2 ≤ count485 b) else decide (1 ≤ count487 b))) else (if i < 489 then decide (2 ≤ count487 b) else (if i < 490 then decide (3 ≤ count487 b) else decide (4 ≤ count487 b)))) else (if i < 494 then (if i < 492 then decide (1 ≤ count491 b) else (if i < 493 then decide (2 ≤ count491 b) else decide (3 ≤ count491 b))) else (if i < 495 then decide (4 ≤ count491 b) else (if i < 496 then decide (5 ≤ count491 b) else decide (6 ≤ count491 b))))))) else (if i < 520 then (if i < 508 then (if i < 502 then (if i < 499 then (if i < 498 then decide (7 ≤ count491 b) else decide (1 ≤ count498 b)) else (if i < 500 then decide (2 ≤ count498 b) else (if i < 501 then decide (3 ≤ count498 b) else decide (4 ≤ count498 b)))) else (if i < 505 then (if i < 503 then decide (5 ≤ count498 b) else (if i < 504 then decide (6 ≤ count498 b) else decide (7 ≤ count498 b))) else (if i < 506 then decide (8 ≤ count498 b) else (if i < 507 then decide (9 ≤ count498 b) else decide (10 ≤ count498 b))))) else (if i < 514 then (if i < 511 then (if i < 509 then decide (11 ≤ count498 b) else (if i < 510 then decide (12 ≤ count498 b) else decide (13 ≤ count498 b))) else (if i < 512 then decide (1 ≤ count511 b) else (if i < 513 then decide (2 ≤ count511 b) else decide (3 ≤ count511 b)))) else (if i < 517 then (if i < 515 then decide (4 ≤ count511 b) else (if i < 516 then decide (5 ≤ count511 b) else decide (6 ≤ count511 b))) else (if i < 518 then decide (7 ≤ count511 b) else (if i < 519 then decide (8 ≤ count511 b) else decide (9 ≤ count511 b)))))) else (if i < 531 then (if i < 525 then (if i < 522 then (if i < 521 then decide (10 ≤ count511 b) else decide (11 ≤ count511 b)) else (if i < 523 then decide (12 ≤ count511 b) else (if i < 524 then decide (13 ≤ count511 b) else decide (14 ≤ count511 b)))) else (if i < 528 then (if i < 526 then decide (15 ≤ count511 b) else (if i < 527 then decide (16 ≤ count511 b) else decide (17 ≤ count511 b))) else (if i < 529 then decide (18 ≤ count511 b) else (if i < 530 then decide (19 ≤ count511 b) else decide (20 ≤ count511 b))))) else (if i < 537 then (if i < 534 then (if i < 532 then decide (21 ≤ count511 b) else (if i < 533 then decide (22 ≤ count511 b) else decide (23 ≤ count511 b))) else (if i < 535 then decide (24 ≤ count511 b) else (if i < 536 then decide (25 ≤ count511 b) else decide (26 ≤ count511 b)))) else (if i < 540 then (if i < 538 then decide (1 ≤ count537 b) else (if i < 539 then decide (2 ≤ count537 b) else decide (1 ≤ count539 b))) else (if i < 541 then decide (2 ≤ count539 b) else (if i < 542 then decide (3 ≤ count539 b) else decide (1 ≤ count542 b))))))))) else (if i < 633 then (if i < 588 then (if i < 565 then (if i < 554 then (if i < 548 then (if i < 545 then (if i < 544 then decide (2 ≤ count542 b) else decide (1 ≤ count544 b)) else (if i < 546 then decide (2 ≤ count544 b) else (if i < 547 then decide (3 ≤ count544 b) else decide (1 ≤ count547 b)))) else (if i < 551 then (if i < 549 then decide (2 ≤ count547 b) else (if i < 550 then decide (3 ≤ count547 b) else decide (4 ≤ count547 b))) else (if i < 552 then decide (5 ≤ count547 b) else (if i < 553 then decide (6 ≤ count547 b) else decide (1 ≤ count553 b))))) else (if i < 559 then (if i < 556 then (if i < 555 then decide (2 ≤ count553 b) else decide (1 ≤ count555 b)) else (if i < 557 then decide (2 ≤ count555 b) else (if i < 558 then decide (3 ≤ count555 b) else decide (1 ≤ count558 b)))) else (if i < 562 then (if i < 560 then decide (2 ≤ count558 b) else (if i < 561 then decide (1 ≤ count560 b) else decide (2 ≤ count560 b))) else (if i < 563 then decide (1 ≤ count562 b) else (if i < 564 then decide (2 ≤ count562 b) else decide (3 ≤ count562 b)))))) else (if i < 576 then (if i < 570 then (if i < 567 then (if i < 566 then decide (4 ≤ count562 b) else decide (1 ≤ count566 b)) else (if i < 568 then decide (2 ≤ count566 b) else (if i < 569 then decide (3 ≤ count566 b) else decide (4 ≤ count566 b)))) else (if i < 573 then (if i < 571 then decide (5 ≤ count566 b) else (if i < 572 then decide (6 ≤ count566 b) else decide (7 ≤ count566 b))) else (if i < 574 then decide (1 ≤ count573 b) else (if i < 575 then decide (2 ≤ count573 b) else decide (3 ≤ count573 b))))) else (if i < 582 then (if i < 579 then (if i < 577 then decide (4 ≤ count573 b) else (if i < 578 then decide (5 ≤ count573 b) else decide (6 ≤ count573 b))) else (if i < 580 then decide (7 ≤ count573 b) else (if i < 581 then decide (8 ≤ count573 b) else decide (9 ≤ count573 b)))) else (if i < 585 then (if i < 583 then decide (10 ≤ count573 b) else (if i < 584 then decide (11 ≤ count573 b) else decide (12 ≤ count573 b))) else (if i < 586 then decide (13 ≤ count573 b) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b))))))) else (if i < 610 then (if i < 599 then (if i < 593 then (if i < 590 then (if i < 589 then decide (1 ≤ count588 b) else decide (2 ≤ count588 b)) else (if i < 591 then decide (3 ≤ count588 b) else (if i < 592 then decide (1 ≤ count591 b) else decide (2 ≤ count591 b)))) else (if i < 596 then (if i < 594 then decide (1 ≤ count593 b) else (if i < 595 then decide (2 ≤ count593 b) else decide (1 ≤ count595 b))) else (if i < 597 then decide (2 ≤ count595 b) else (if i < 598 then decide (3 ≤ count595 b) else decide (4 ≤ count595 b))))) else (if i < 604 then (if i < 601 then (if i < 600 then decide (1 ≤ count599 b) else decide (2 ≤ count599 b)) else (if i < 602 then decide (3 ≤ count599 b) else (if i < 603 then decide (4 ≤ count599 b) else decide (5 ≤ count599 b)))) else (if i < 607 then (if i < 605 then decide (6 ≤ count599 b) else (if i < 606 then decide (7 ≤ count599 b) else decide (1 ≤ count606 b))) else (if i < 608 then decide (2 ≤ count606 b) else (if i < 609 then decide (1 ≤ count608 b) else decide (2 ≤ count608 b)))))) else (if i < 621 then (if i < 615 then (if i < 612 then (if i < 611 then decide (3 ≤ count608 b) else decide (1 ≤ count611 b)) else (if i < 613 then decide (2 ≤ count611 b) else (if i < 614 then decide (1 ≤ count613 b) else decide (2 ≤ count613 b)))) else (if i < 618 then (if i < 616 then decide (1 ≤ count615 b) else (if i < 617 then decide (2 ≤ count615 b) else decide (3 ≤ count615 b))) else (if i < 619 then decide (4 ≤ count615 b) else (if i < 620 then decide (1 ≤ count619 b) else decide (2 ≤ count619 b))))) else (if i < 627 then (if i < 624 then (if i < 622 then decide (3 ≤ count619 b) else (if i < 623 then decide (4 ≤ count619 b) else decide (5 ≤ count619 b))) else (if i < 625 then decide (6 ≤ count619 b) else (if i < 626 then decide (7 ≤ count619 b) else decide (1 ≤ count626 b)))) else (if i < 630 then (if i < 628 then decide (2 ≤ count626 b) else (if i < 629 then decide (3 ≤ count626 b) else decide (4 ≤ count626 b))) else (if i < 631 then decide (5 ≤ count626 b) else (if i < 632 then decide (6 ≤ count626 b) else decide (7 ≤ count626 b)))))))) else (if i < 678 then (if i < 655 then (if i < 644 then (if i < 638 then (if i < 635 then (if i < 634 then decide (8 ≤ count626 b) else decide (9 ≤ count626 b)) else (if i < 636 then decide (10 ≤ count626 b) else (if i < 637 then decide (11 ≤ count626 b) else decide (12 ≤ count626 b)))) else (if i < 641 then (if i < 639 then decide (13 ≤ count626 b) else (if i < 640 then decide (14 ≤ count626 b) else decide (1 ≤ count640 b))) else (if i < 642 then decide (2 ≤ count640 b) else (if i < 643 then decide (3 ≤ count640 b) else decide (4 ≤ count640 b))))) else (if i < 649 then (if i < 646 then (if i < 645 then decide (5 ≤ count640 b) else decide (6 ≤ count640 b)) else (if i < 647 then decide (7 ≤ count640 b) else (if i < 648 then decide (8 ≤ count640 b) else decide (9 ≤ count640 b)))) else (if i < 652 then (if i < 650 then decide (10 ≤ count640 b) else (if i < 651 then decide (11 ≤ count640 b) else decide (12 ≤ count640 b))) else (if i < 653 then decide (13 ≤ count640 b) else (if i < 654 then decide (14 ≤ count640 b) else decide (15 ≤ count640 b)))))) else (if i < 666 then (if i < 660 then (if i < 657 then (if i < 656 then decide (16 ≤ count640 b) else decide (17 ≤ count640 b)) else (if i < 658 then decide (18 ≤ count640 b) else (if i < 659 then decide (19 ≤ count640 b) else decide (20 ≤ count640 b)))) else (if i < 663 then (if i < 661 then decide (21 ≤ count640 b) else (if i < 662 then decide (22 ≤ count640 b) else decide (23 ≤ count640 b))) else (if i < 664 then decide (24 ≤ count640 b) else (if i < 665 then decide (25 ≤ count640 b) else decide (26 ≤ count640 b))))) else (if i < 672 then (if i < 669 then (if i < 667 then decide (27 ≤ count640 b) else (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b))) else (if i < 670 then decide (3 ≤ count667 b) else (if i < 671 then decide (4 ≤ count667 b) else decide (5 ≤ count667 b)))) else (if i < 675 then (if i < 673 then decide (6 ≤ count667 b) else (if i < 674 then decide (7 ≤ count667 b) else decide (8 ≤ count667 b))) else (if i < 676 then decide (9 ≤ count667 b) else (if i < 677 then decide (10 ≤ count667 b) else decide (11 ≤ count667 b))))))) else (if i < 701 then (if i < 689 then (if i < 683 then (if i < 680 then (if i < 679 then decide (12 ≤ count667 b) else decide (13 ≤ count667 b)) else (if i < 681 then decide (14 ≤ count667 b) else (if i < 682 then decide (15 ≤ count667 b) else decide (16 ≤ count667 b)))) else (if i < 686 then (if i < 684 then decide (17 ≤ count667 b) else (if i < 685 then decide (18 ≤ count667 b) else decide (19 ≤ count667 b))) else (if i < 687 then decide (20 ≤ count667 b) else (if i < 688 then decide (21 ≤ count667 b) else decide (22 ≤ count667 b))))) else (if i < 695 then (if i < 692 then (if i < 690 then decide (23 ≤ count667 b) else (if i < 691 then decide (24 ≤ count667 b) else decide (25 ≤ count667 b))) else (if i < 693 then decide (26 ≤ count667 b) else (if i < 694 then decide (27 ≤ count667 b) else decide (28 ≤ count667 b)))) else (if i < 698 then (if i < 696 then decide (29 ≤ count667 b) else (if i < 697 then decide (30 ≤ count667 b) else decide (31 ≤ count667 b))) else (if i < 699 then decide (32 ≤ count667 b) else (if i < 700 then decide (33 ≤ count667 b) else decide (34 ≤ count667 b)))))) else (if i < 712 then (if i < 706 then (if i < 703 then (if i < 702 then decide (35 ≤ count667 b) else decide (36 ≤ count667 b)) else (if i < 704 then decide (37 ≤ count667 b) else (if i < 705 then decide (38 ≤ count667 b) else decide (39 ≤ count667 b)))) else (if i < 709 then (if i < 707 then decide (40 ≤ count667 b) else (if i < 708 then decide (41 ≤ count667 b) else decide (42 ≤ count667 b))) else (if i < 710 then decide (1 ≤ count709 b) else (if i < 711 then decide (2 ≤ count709 b) else decide (1 ≤ count711 b))))) else (if i < 718 then (if i < 715 then (if i < 713 then decide (2 ≤ count711 b) else (if i < 714 then decide (3 ≤ count711 b) else decide (1 ≤ count714 b))) else (if i < 716 then decide (2 ≤ count714 b) else (if i < 717 then decide (1 ≤ count716 b) else decide (2 ≤ count716 b)))) else (if i < 721 then (if i < 719 then decide (3 ≤ count716 b) else (if i < 720 then decide (1 ≤ count719 b) else decide (2 ≤ count719 b))) else (if i < 722 then decide (3 ≤ count719 b) else (if i < 723 then decide (4 ≤ count719 b) else decide (5 ≤ count719 b))))))))))) else (if i < 1086 then (if i < 905 then (if i < 814 then (if i < 769 then (if i < 746 then (if i < 735 then (if i < 729 then (if i < 726 then (if i < 725 then decide (6 ≤ count719 b) else decide (1 ≤ count725 b)) else (if i < 727 then decide (2 ≤ count725 b) else (if i < 728 then decide (1 ≤ count727 b) else decide (2 ≤ count727 b)))) else (if i < 732 then (if i < 730 then decide (3 ≤ count727 b) else (if i < 731 then decide (1 ≤ count730 b) else decide (2 ≤ count730 b))) else (if i < 733 then decide (1 ≤ count732 b) else (if i < 734 then decide (2 ≤ count732 b) else decide (1 ≤ count734 b))))) else (if i < 740 then (if i < 737 then (if i < 736 then decide (2 ≤ count734 b) else decide (3 ≤ count734 b)) else (if i < 738 then decide (4 ≤ count734 b) else (if i < 739 then decide (1 ≤ count738 b) else decide (2 ≤ count738 b)))) else (if i < 743 then (if i < 741 then decide (3 ≤ count738 b) else (if i < 742 then decide (4 ≤ count738 b) else decide (5 ≤ count738 b))) else (if i < 744 then decide (6 ≤ count738 b) else (if i < 745 then decide (7 ≤ count738 b) else decide (1 ≤ count745 b)))))) else (if i < 757 then (if i < 751 then (if i < 748 then (if i < 747 then decide (2 ≤ count745 b) else decide (3 ≤ count745 b)) else (if i < 749 then decide (4 ≤ count745 b) else (if i < 750 then decide (5 ≤ count745 b) else decide (6 ≤ count745 b)))) else (if i < 754 then (if i < 752 then decide (7 ≤ count745 b) else (if i < 753 then decide (8 ≤ count745 b) else decide (9 ≤ count745 b))) else (if i < 755 then decide (10 ≤ count745 b) else (if i < 756 then decide (11 ≤ count745 b) else decide (12 ≤ count745 b))))) else (if i < 763 then (if i < 760 then (if i < 758 then decide (13 ≤ count745 b) else (if i < 759 then decide (1 ≤ count758 b) else decide (2 ≤ count758 b))) else (if i < 761 then decide (1 ≤ count760 b) else (if i < 762 then decide (2 ≤ count760 b) else decide (3 ≤ count760 b)))) else (if i < 766 then (if i < 764 then decide (1 ≤ count763 b) else (if i < 765 then decide (2 ≤ count763 b) else decide (1 ≤ count765 b))) else (if i < 767 then decide (2 ≤ count765 b) else (if i < 768 then decide (3 ≤ count765 b) else decide (1 ≤ count768 b))))))) else (if i < 791 then (if i < 780 then (if i < 774 then (if i < 771 then (if i < 770 then decide (2 ≤ count768 b) else decide (3 ≤ count768 b)) else (if i < 772 then decide (4 ≤ count768 b) else (if i < 773 then decide (5 ≤ count768 b) else decide (6 ≤ count768 b)))) else (if i < 777 then (if i < 775 then decide (1 ≤ count774 b) else (if i < 776 then decide (2 ≤ count774 b) else decide (1 ≤ count776 b))) else (if i < 778 then decide (2 ≤ count776 b) else (if i < 779 then decide (3 ≤ count776 b) else decide (1 ≤ count779 b))))) else (if i < 785 then (if i < 782 then (if i < 781 then decide (2 ≤ count779 b) else decide (1 ≤ count781 b)) else (if i < 783 then decide (2 ≤ count781 b) else (if i < 784 then decide (1 ≤ count783 b) else decide (2 ≤ count783 b)))) else (if i < 788 then (if i < 786 then decide (3 ≤ count783 b) else (if i < 787 then decide (4 ≤ count783 b) else decide (1 ≤ count787 b))) else (if i < 789 then decide (2 ≤ count787 b) else (if i < 790 then decide (3 ≤ count787 b) else decide (4 ≤ count787 b)))))) else (if i < 802 then (if i < 796 then (if i < 793 then (if i < 792 then decide (5 ≤ count787 b) else decide (6 ≤ count787 b)) else (if i < 794 then decide (7 ≤ count787 b) else (if i < 795 then decide (1 ≤ count794 b) else decide (2 ≤ count794 b)))) else (if i < 799 then (if i < 797 then decide (3 ≤ count794 b) else (if i < 798 then decide (4 ≤ count794 b) else decide (5 ≤ count794 b))) else (if i < 800 then decide (6 ≤ count794 b) else (if i < 801 then decide (7 ≤ count794 b) else decide (8 ≤ count794 b))))) else (if i < 808 then (if i < 805 then (if i < 803 then decide (9 ≤ count794 b) else (if i < 804 then decide (10 ≤ count794 b) else decide (11 ≤ count794 b))) else (if i < 806 then decide (12 ≤ count794 b) else (if i < 807 then decide (13 ≤ count794 b) else decide (1 ≤ count807 b)))) else (if i < 811 then (if i < 809 then decide (2 ≤ count807 b) else (if i < 810 then decide (3 ≤ count807 b) else decide (4 ≤ count807 b))) else (if i < 812 then decide (5 ≤ count807 b) else (if i < 813 then decide (6 ≤ count807 b) else decide (7 ≤ count807 b)))))))) else (if i < 859 then (if i < 836 then (if i < 825 then (if i < 819 then (if i < 816 then (if i < 815 then decide (8 ≤ count807 b) else decide (9 ≤ count807 b)) else (if i < 817 then decide (10 ≤ count807 b) else (if i < 818 then decide (11 ≤ count807 b) else decide (12 ≤ count807 b)))) else (if i < 822 then (if i < 820 then decide (13 ≤ count807 b) else (if i < 821 then decide (1 ≤ count820 b) else decide (2 ≤ count820 b))) else (if i < 823 then decide (1 ≤ count822 b) else (if i < 824 then decide (2 ≤ count822 b) else decide (3 ≤ count822 b))))) else (if i < 830 then (if i < 827 then (if i < 826 then decide (1 ≤ count825 b) else decide (2 ≤ count825 b)) else (if i < 828 then decide (1 ≤ count827 b) else (if i < 829 then decide (2 ≤ count827 b) else decide (3 ≤ count827 b)))) else (if i < 833 then (if i < 831 then decide (1 ≤ count830 b) else (if i < 832 then decide (2 ≤ count830 b) else decide (3 ≤ count830 b))) else (if i < 834 then decide (4 ≤ count830 b) else (if i < 835 then decide (5 ≤ count830 b) else decide (6 ≤ count830 b)))))) else (if i < 847 then (if i < 841 then (if i < 838 then (if i < 837 then decide (1 ≤ count836 b) else decide (2 ≤ count836 b)) else (if i < 839 then decide (1 ≤ count838 b) else (if i < 840 then decide (2 ≤ count838 b) else decide (3 ≤ count838 b)))) else (if i < 844 then (if i < 842 then decide (1 ≤ count841 b) else (if i < 843 then decide (2 ≤ count841 b) else decide (1 ≤ count843 b))) else (if i < 845 then decide (2 ≤ count843 b) else (if i < 846 then decide (1 ≤ count845 b) else decide (2 ≤ count845 b))))) else (if i < 853 then (if i < 850 then (if i < 848 then decide (3 ≤ count845 b) else (if i < 849 then decide (4 ≤ count845 b) else decide (1 ≤ count849 b))) else (if i < 851 then decide (2 ≤ count849 b) else (if i < 852 then decide (3 ≤ count849 b) else decide (4 ≤ count849 b)))) else (if i < 856 then (if i < 854 then decide (5 ≤ count849 b) else (if i < 855 then decide (6 ≤ count849 b) else decide (7 ≤ count849 b))) else (if i < 857 then decide (1 ≤ count856 b) else (if i < 858 then decide (2 ≤ count856 b) else decide (3 ≤ count856 b))))))) else (if i < 882 then (if i < 870 then (if i < 864 then (if i < 861 then (if i < 860 then decide (4 ≤ count856 b) else decide (5 ≤ count856 b)) else (if i < 862 then decide (6 ≤ count856 b) else (if i < 863 then decide (7 ≤ count856 b) else decide (8 ≤ count856 b)))) else (if i < 867 then (if i < 865 then decide (9 ≤ count856 b) else (if i < 866 then decide (10 ≤ count856 b) else decide (11 ≤ count856 b))) else (if i < 868 then decide (12 ≤ count856 b) else (if i < 869 then decide (13 ≤ count856 b) else decide (1 ≤ count869 b))))) else (if i < 876 then (if i < 873 then (if i < 871 then decide (2 ≤ count869 b) else (if i < 872 then decide (1 ≤ count871 b) else decide (2 ≤ count871 b))) else (if i < 874 then decide (3 ≤ count871 b) else (if i < 875 then decide (1 ≤ count874 b) else decide (2 ≤ count874 b)))) else (if i < 879 then (if i < 877 then decide (1 ≤ count876 b) else (if i < 878 then decide (2 ≤ count876 b) else decide (1 ≤ count878 b))) else (if i < 880 then decide (2 ≤ count878 b) else (if i < 881 then decide (3 ≤ count878 b) else decide (4 ≤ count878 b)))))) else (if i < 893 then (if i < 887 then (if i < 884 then (if i < 883 then decide (1 ≤ count882 b) else decide (2 ≤ count882 b)) else (if i < 885 then decide (3 ≤ count882 b) else (if i < 886 then decide (4 ≤ count882 b) else decide (5 ≤ count882 b)))) else (if i < 890 then (if i < 888 then decide (6 ≤ count882 b) else (if i < 889 then decide (7 ≤ count882 b) else decide (1 ≤ count889 b))) else (if i < 891 then decide (2 ≤ count889 b) else (if i < 892 then decide (1 ≤ count891 b) else decide (2 ≤ count891 b))))) else (if i < 899 then (if i < 896 then (if i < 894 then decide (3 ≤ count891 b) else (if i < 895 then decide (1 ≤ count894 b) else decide (2 ≤ count894 b))) else (if i < 897 then decide (1 ≤ count896 b) else (if i < 898 then decide (2 ≤ count896 b) else decide (1 ≤ count898 b)))) else (if i < 902 then (if i < 900 then decide (2 ≤ count898 b) else (if i < 901 then decide (3 ≤ count898 b) else decide (4 ≤ count898 b))) else (if i < 903 then decide (1 ≤ count902 b) else (if i < 904 then decide (2 ≤ count902 b) else decide (3 ≤ count902 b))))))))) else (if i < 995 then (if i < 950 then (if i < 927 then (if i < 916 then (if i < 910 then (if i < 907 then (if i < 906 then decide (4 ≤ count902 b) else decide (5 ≤ count902 b)) else (if i < 908 then decide (6 ≤ count902 b) else (if i < 909 then decide (7 ≤ count902 b) else decide (1 ≤ count909 b)))) else (if i < 913 then (if i < 911 then decide (2 ≤ count909 b) else (if i < 912 then decide (3 ≤ count909 b) else decide (4 ≤ count909 b))) else (if i < 914 then decide (5 ≤ count909 b) else (if i < 915 then decide (6 ≤ count909 b) else decide (7 ≤ count909 b))))) else (if i < 921 then (if i < 918 then (if i < 917 then decide (8 ≤ count909 b) else decide (9 ≤ count909 b)) else (if i < 919 then decide (10 ≤ count909 b) else (if i < 920 then decide (11 ≤ count909 b) else decide (12 ≤ count909 b)))) else (if i < 924 then (if i < 922 then decide (13 ≤ count909 b) else (if i < 923 then decide (1 ≤ count922 b) else decide (2 ≤ count922 b))) else (if i < 925 then decide (3 ≤ count922 b) else (if i < 926 then decide (4 ≤ count922 b) else decide (5 ≤ count922 b)))))) else (if i < 938 then (if i < 932 then (if i < 929 then (if i < 928 then decide (6 ≤ count922 b) else decide (7 ≤ count922 b)) else (if i < 930 then decide (8 ≤ count922 b) else (if i < 931 then decide (9 ≤ count922 b) else decide (10 ≤ count922 b)))) else (if i < 935 then (if i < 933 then decide (11 ≤ count922 b) else (if i < 934 then decide (12 ≤ count922 b) else decide (13 ≤ count922 b))) else (if i < 936 then decide (1 ≤ count935 b) else (if i < 937 then decide (2 ≤ count935 b) else decide (3 ≤ count935 b))))) else (if i < 944 then (if i < 941 then (if i < 939 then decide (4 ≤ count935 b) else (if i < 940 then decide (5 ≤ count935 b) else decide (6 ≤ count935 b))) else (if i < 942 then decide (7 ≤ count935 b) else (if i < 943 then decide (8 ≤ count935 b) else decide (9 ≤ count935 b)))) else (if i < 947 then (if i < 945 then decide (10 ≤ count935 b) else (if i < 946 then decide (11 ≤ count935 b) else decide (12 ≤ count935 b))) else (if i < 948 then decide (13 ≤ count935 b) else (if i < 949 then decide (1 ≤ count948 b) else decide (2 ≤ count948 b))))))) else (if i < 972 then (if i < 961 then (if i < 955 then (if i < 952 then (if i < 951 then decide (1 ≤ count950 b) else decide (2 ≤ count950 b)) else (if i < 953 then decide (3 ≤ count950 b) else (if i < 954 then decide (1 ≤ count953 b) else decide (2 ≤ count953 b)))) else (if i < 958 then (if i < 956 then decide (1 ≤ count955 b) else (if i < 957 then decide (2 ≤ count955 b) else decide (3 ≤ count955 b))) else (if i < 959 then decide (1 ≤ count958 b) else (if i < 960 then decide (2 ≤ count958 b) else decide (3 ≤ count958 b))))) else (if i < 966 then (if i < 963 then (if i < 962 then decide (4 ≤ count958 b) else decide (5 ≤ count958 b)) else (if i < 964 then decide (6 ≤ count958 b) else (if i < 965 then decide (1 ≤ count964 b) else decide (2 ≤ count964 b)))) else (if i < 969 then (if i < 967 then decide (1 ≤ count966 b) else (if i < 968 then decide (2 ≤ count966 b) else decide (3 ≤ count966 b))) else (if i < 970 then decide (1 ≤ count969 b) else (if i < 971 then decide (2 ≤ count969 b) else decide (1 ≤ count971 b)))))) else (if i < 983 then (if i < 977 then (if i < 974 then (if i < 973 then decide (2 ≤ count971 b) else decide (3 ≤ count971 b)) else (if i < 975 then decide (1 ≤ count974 b) else (if i < 976 then decide (2 ≤ count974 b) else decide (3 ≤ count974 b)))) else (if i < 980 then (if i < 978 then decide (4 ≤ count974 b) else (if i < 979 then decide (5 ≤ count974 b) else decide (6 ≤ count974 b))) else (if i < 981 then decide (1 ≤ count980 b) else (if i < 982 then decide (2 ≤ count980 b) else decide (3 ≤ count980 b))))) else (if i < 989 then (if i < 986 then (if i < 984 then decide (4 ≤ count980 b) else (if i < 985 then decide (5 ≤ count980 b) else decide (6 ≤ count980 b))) else (if i < 987 then decide (7 ≤ count980 b) else (if i < 988 then decide (8 ≤ count980 b) else decide (9 ≤ count980 b)))) else (if i < 992 then (if i < 990 then decide (10 ≤ count980 b) else (if i < 991 then decide (11 ≤ count980 b) else decide (12 ≤ count980 b))) else (if i < 993 then decide (1 ≤ count992 b) else (if i < 994 then decide (2 ≤ count992 b) else decide (1 ≤ count994 b)))))))) else (if i < 1040 then (if i < 1017 then (if i < 1006 then (if i < 1000 then (if i < 997 then (if i < 996 then decide (2 ≤ count994 b) else decide (3 ≤ count994 b)) else (if i < 998 then decide (1 ≤ count997 b) else (if i < 999 then decide (2 ≤ count997 b) else decide (1 ≤ count999 b)))) else (if i < 1003 then (if i < 1001 then decide (2 ≤ count999 b) else (if i < 1002 then decide (3 ≤ count999 b) else decide (1 ≤ count1002 b))) else (if i < 1004 then decide (2 ≤ count1002 b) else (if i < 1005 then decide (3 ≤ count1002 b) else decide (4 ≤ count1002 b))))) else (if i < 1011 then (if i < 1008 then (if i < 1007 then decide (5 ≤ count1002 b) else decide (6 ≤ count1002 b)) else (if i < 1009 then decide (1 ≤ count1008 b) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (1 ≤ count1010 b)))) else (if i < 1014 then (if i < 1012 then decide (2 ≤ count1010 b) else (if i < 1013 then decide (3 ≤ count1010 b) else decide (1 ≤ count1013 b))) else (if i < 1015 then decide (2 ≤ count1013 b) else (if i < 1016 then decide (1 ≤ count1015 b) else decide (2 ≤ count1015 b)))))) else (if i < 1028 then (if i < 1022 then (if i < 1019 then (if i < 1018 then decide (1 ≤ count1017 b) else decide (2 ≤ count1017 b)) else (if i < 1020 then decide (3 ≤ count1017 b) else (if i < 1021 then decide (4 ≤ count1017 b) else decide (1 ≤ count1021 b)))) else (if i < 1025 then (if i < 1023 then decide (2 ≤ count1021 b) else (if i < 1024 then decide (3 ≤ count1021 b) else decide (4 ≤ count1021 b))) else (if i < 1026 then decide (5 ≤ count1021 b) else (if i < 1027 then decide (6 ≤ count1021 b) else decide (7 ≤ count1021 b))))) else (if i < 1034 then (if i < 1031 then (if i < 1029 then decide (1 ≤ count1028 b) else (if i < 1030 then decide (2 ≤ count1028 b) else decide (3 ≤ count1028 b))) else (if i < 1032 then decide (4 ≤ count1028 b) else (if i < 1033 then decide (5 ≤ count1028 b) else decide (6 ≤ count1028 b)))) else (if i < 1037 then (if i < 1035 then decide (7 ≤ count1028 b) else (if i < 1036 then decide (8 ≤ count1028 b) else decide (9 ≤ count1028 b))) else (if i < 1038 then decide (10 ≤ count1028 b) else (if i < 1039 then decide (11 ≤ count1028 b) else decide (12 ≤ count1028 b))))))) else (if i < 1063 then (if i < 1051 then (if i < 1045 then (if i < 1042 then (if i < 1041 then decide (13 ≤ count1028 b) else decide (1 ≤ count1041 b)) else (if i < 1043 then decide (2 ≤ count1041 b) else (if i < 1044 then decide (3 ≤ count1041 b) else decide (4 ≤ count1041 b)))) else (if i < 1048 then (if i < 1046 then decide (5 ≤ count1041 b) else (if i < 1047 then decide (6 ≤ count1041 b) else decide (7 ≤ count1041 b))) else (if i < 1049 then decide (8 ≤ count1041 b) else (if i < 1050 then decide (9 ≤ count1041 b) else decide (10 ≤ count1041 b))))) else (if i < 1057 then (if i < 1054 then (if i < 1052 then decide (11 ≤ count1041 b) else (if i < 1053 then decide (12 ≤ count1041 b) else decide (13 ≤ count1041 b))) else (if i < 1055 then decide (14 ≤ count1041 b) else (if i < 1056 then decide (15 ≤ count1041 b) else decide (16 ≤ count1041 b)))) else (if i < 1060 then (if i < 1058 then decide (17 ≤ count1041 b) else (if i < 1059 then decide (18 ≤ count1041 b) else decide (19 ≤ count1041 b))) else (if i < 1061 then decide (20 ≤ count1041 b) else (if i < 1062 then decide (21 ≤ count1041 b) else decide (22 ≤ count1041 b)))))) else (if i < 1074 then (if i < 1068 then (if i < 1065 then (if i < 1064 then decide (23 ≤ count1041 b) else decide (24 ≤ count1041 b)) else (if i < 1066 then decide (25 ≤ count1041 b) else (if i < 1067 then decide (1 ≤ count1066 b) else decide (2 ≤ count1066 b)))) else (if i < 1071 then (if i < 1069 then decide (1 ≤ count1068 b) else (if i < 1070 then decide (2 ≤ count1068 b) else decide (3 ≤ count1068 b))) else (if i < 1072 then decide (1 ≤ count1071 b) else (if i < 1073 then decide (2 ≤ count1071 b) else decide (1 ≤ count1073 b))))) else (if i < 1080 then (if i < 1077 then (if i < 1075 then decide (2 ≤ count1073 b) else (if i < 1076 then decide (3 ≤ count1073 b) else decide (1 ≤ count1076 b))) else (if i < 1078 then decide (2 ≤ count1076 b) else (if i < 1079 then decide (3 ≤ count1076 b) else decide (4 ≤ count1076 b)))) else (if i < 1083 then (if i < 1081 then decide (5 ≤ count1076 b) else (if i < 1082 then decide (6 ≤ count1076 b) else decide (1 ≤ count1082 b))) else (if i < 1084 then decide (2 ≤ count1082 b) else (if i < 1085 then decide (1 ≤ count1084 b) else decide (2 ≤ count1084 b)))))))))) else (if i < 1267 then (if i < 1176 then (if i < 1131 then (if i < 1108 then (if i < 1097 then (if i < 1091 then (if i < 1088 then (if i < 1087 then decide (3 ≤ count1084 b) else decide (1 ≤ count1087 b)) else (if i < 1089 then decide (2 ≤ count1087 b) else (if i < 1090 then decide (1 ≤ count1089 b) else decide (2 ≤ count1089 b)))) else (if i < 1094 then (if i < 1092 then decide (1 ≤ count1091 b) else (if i < 1093 then decide (2 ≤ count1091 b) else decide (3 ≤ count1091 b))) else (if i < 1095 then decide (4 ≤ count1091 b) else (if i < 1096 then decide (1 ≤ count1095 b) else decide (2 ≤ count1095 b))))) else (if i < 1102 then (if i < 1099 then (if i < 1098 then decide (3 ≤ count1095 b) else decide (4 ≤ count1095 b)) else (if i < 1100 then decide (5 ≤ count1095 b) else (if i < 1101 then decide (6 ≤ count1095 b) else decide (7 ≤ count1095 b)))) else (if i < 1105 then (if i < 1103 then decide (1 ≤ count1102 b) else (if i < 1104 then decide (2 ≤ count1102 b) else decide (3 ≤ count1102 b))) else (if i < 1106 then decide (4 ≤ count1102 b) else (if i < 1107 then decide (5 ≤ count1102 b) else decide (6 ≤ count1102 b)))))) else (if i < 1119 then (if i < 1113 then (if i < 1110 then (if i < 1109 then decide (7 ≤ count1102 b) else decide (8 ≤ count1102 b)) else (if i < 1111 then decide (9 ≤ count1102 b) else (if i < 1112 then decide (10 ≤ count1102 b) else decide (11 ≤ count1102 b)))) else (if i < 1116 then (if i < 1114 then decide (12 ≤ count1102 b) else (if i < 1115 then decide (13 ≤ count1102 b) else decide (1 ≤ count1115 b))) else (if i < 1117 then decide (2 ≤ count1115 b) else (if i < 1118 then decide (1 ≤ count1117 b) else decide (2 ≤ count1117 b))))) else (if i < 1125 then (if i < 1122 then (if i < 1120 then decide (3 ≤ count1117 b) else (if i < 1121 then decide (1 ≤ count1120 b) else decide (2 ≤ count1120 b))) else (if i < 1123 then decide (1 ≤ count1122 b) else (if i < 1124 then decide (2 ≤ count1122 b) else decide (3 ≤ count1122 b)))) else (if i < 1128 then (if i < 1126 then decide (1 ≤ count1125 b) else (if i < 1127 then decide (2 ≤ count1125 b) else decide (3 ≤ count1125 b))) else (if i < 1129 then decide (4 ≤ count1125 b) else (if i < 1130 then decide (5 ≤ count1125 b) else decide (6 ≤ count1125 b))))))) else (if i < 1153 then (if i < 1142 then (if i < 1136 then (if i < 1133 then (if i < 1132 then decide (1 ≤ count1131 b) else decide (2 ≤ count1131 b)) else (if i < 1134 then decide (1 ≤ count1133 b) else (if i < 1135 then decide (2 ≤ count1133 b) else decide (3 ≤ count1133 b)))) else (if i < 1139 then (if i < 1137 then decide (1 ≤ count1136 b) else (if i < 1138 then decide (2 ≤ count1136 b) else decide (1 ≤ count1138 b))) else (if i < 1140 then decide (2 ≤ count1138 b) else (if i < 1141 then decide (1 ≤ count1140 b) else decide (2 ≤ count1140 b))))) else (if i < 1147 then (if i < 1144 then (if i < 1143 then decide (3 ≤ count1140 b) else decide (4 ≤ count1140 b)) else (if i < 1145 then decide (1 ≤ count1144 b) else (if i < 1146 then decide (2 ≤ count1144 b) else decide (3 ≤ count1144 b)))) else (if i < 1150 then (if i < 1148 then decide (4 ≤ count1144 b) else (if i < 1149 then decide (5 ≤ count1144 b) else decide (6 ≤ count1144 b))) else (if i < 1151 then decide (7 ≤ count1144 b) else (if i < 1152 then decide (1 ≤ count1151 b) else decide (2 ≤ count1151 b)))))) else (if i < 1164 then (if i < 1158 then (if i < 1155 then (if i < 1154 then decide (3 ≤ count1151 b) else decide (4 ≤ count1151 b)) else (if i < 1156 then decide (5 ≤ count1151 b) else (if i < 1157 then decide (6 ≤ count1151 b) else decide (7 ≤ count1151 b)))) else (if i < 1161 then (if i < 1159 then decide (8 ≤ count1151 b) else (if i < 1160 then decide (9 ≤ count1151 b) else decide (10 ≤ count1151 b))) else (if i < 1162 then decide (11 ≤ count1151 b) else (if i < 1163 then decide (12 ≤ count1151 b) else decide (13 ≤ count1151 b))))) else (if i < 1170 then (if i < 1167 then (if i < 1165 then decide (1 ≤ count1164 b) else (if i < 1166 then decide (2 ≤ count1164 b) else decide (3 ≤ count1164 b))) else (if i < 1168 then decide (4 ≤ count1164 b) else (if i < 1169 then decide (5 ≤ count1164 b) else decide (6 ≤ count1164 b)))) else (if i < 1173 then (if i < 1171 then decide (7 ≤ count1164 b) else (if i < 1172 then decide (8 ≤ count1164 b) else decide (9 ≤ count1164 b))) else (if i < 1174 then decide (10 ≤ count1164 b) else (if i < 1175 then decide (11 ≤ count1164 b) else decide (12 ≤ count1164 b)))))))) else (if i < 1221 then (if i < 1198 then (if i < 1187 then (if i < 1181 then (if i < 1178 then (if i < 1177 then decide (13 ≤ count1164 b) else decide (14 ≤ count1164 b)) else (if i < 1179 then decide (15 ≤ count1164 b) else (if i < 1180 then decide (16 ≤ count1164 b) else decide (17 ≤ count1164 b)))) else (if i < 1184 then (if i < 1182 then decide (18 ≤ count1164 b) else (if i < 1183 then decide (19 ≤ count1164 b) else decide (20 ≤ count1164 b))) else (if i < 1185 then decide (21 ≤ count1164 b) else (if i < 1186 then decide (22 ≤ count1164 b) else decide (23 ≤ count1164 b))))) else (if i < 1192 then (if i < 1189 then (if i < 1188 then decide (24 ≤ count1164 b) else decide (25 ≤ count1164 b)) else (if i < 1190 then decide (26 ≤ count1164 b) else (if i < 1191 then decide (1 ≤ count1190 b) else decide (2 ≤ count1190 b)))) else (if i < 1195 then (if i < 1193 then decide (3 ≤ count1190 b) else (if i < 1194 then decide (4 ≤ count1190 b) else decide (5 ≤ count1190 b))) else (if i < 1196 then decide (6 ≤ count1190 b) else (if i < 1197 then decide (7 ≤ count1190 b) else decide (8 ≤ count1190 b)))))) else (if i < 1209 then (if i < 1203 then (if i < 1200 then (if i < 1199 then decide (9 ≤ count1190 b) else decide (10 ≤ count1190 b)) else (if i < 1201 then decide (11 ≤ count1190 b) else (if i < 1202 then decide (12 ≤ count1190 b) else decide (13 ≤ count1190 b)))) else (if i < 1206 then (if i < 1204 then decide (14 ≤ count1190 b) else (if i < 1205 then decide (15 ≤ count1190 b) else decide (16 ≤ count1190 b))) else (if i < 1207 then decide (17 ≤ count1190 b) else (if i < 1208 then decide (18 ≤ count1190 b) else decide (19 ≤ count1190 b))))) else (if i < 1215 then (if i < 1212 then (if i < 1210 then decide (20 ≤ count1190 b) else (if i < 1211 then decide (21 ≤ count1190 b) else decide (22 ≤ count1190 b))) else (if i < 1213 then decide (23 ≤ count1190 b) else (if i < 1214 then decide (24 ≤ count1190 b) else decide (25 ≤ count1190 b)))) else (if i < 1218 then (if i < 1216 then decide (26 ≤ count1190 b) else (if i < 1217 then decide (27 ≤ count1190 b) else decide (28 ≤ count1190 b))) else (if i < 1219 then decide (29 ≤ count1190 b) else (if i < 1220 then decide (30 ≤ count1190 b) else decide (31 ≤ count1190 b))))))) else (if i < 1244 then (if i < 1232 then (if i < 1226 then (if i < 1223 then (if i < 1222 then decide (32 ≤ count1190 b) else decide (33 ≤ count1190 b)) else (if i < 1224 then decide (34 ≤ count1190 b) else (if i < 1225 then decide (35 ≤ count1190 b) else decide (36 ≤ count1190 b)))) else (if i < 1229 then (if i < 1227 then decide (37 ≤ count1190 b) else (if i < 1228 then decide (38 ≤ count1190 b) else decide (39 ≤ count1190 b))) else (if i < 1230 then decide (40 ≤ count1190 b) else (if i < 1231 then decide (41 ≤ count1190 b) else decide (42 ≤ count1190 b))))) else (if i < 1238 then (if i < 1235 then (if i < 1233 then decide (1 ≤ count1232 b) else (if i < 1234 then decide (2 ≤ count1232 b) else decide (1 ≤ count1234 b))) else (if i < 1236 then decide (2 ≤ count1234 b) else (if i < 1237 then decide (3 ≤ count1234 b) else decide (1 ≤ count1237 b)))) else (if i < 1241 then (if i < 1239 then decide (2 ≤ count1237 b) else (if i < 1240 then decide (1 ≤ count1239 b) else decide (2 ≤ count1239 b))) else (if i < 1242 then decide (3 ≤ count1239 b) else (if i < 1243 then decide (1 ≤ count1242 b) else decide (2 ≤ count1242 b)))))) else (if i < 1255 then (if i < 1249 then (if i < 1246 then (if i < 1245 then decide (3 ≤ count1242 b) else decide (4 ≤ count1242 b)) else (if i < 1247 then decide (5 ≤ count1242 b) else (if i < 1248 then decide (6 ≤ count1242 b) else decide (1 ≤ count1248 b)))) else (if i < 1252 then (if i < 1250 then decide (2 ≤ count1248 b) else (if i < 1251 then decide (1 ≤ count1250 b) else decide (2 ≤ count1250 b))) else (if i < 1253 then decide (3 ≤ count1250 b) else (if i < 1254 then decide (1 ≤ count1253 b) else decide (2 ≤ count1253 b))))) else (if i < 1261 then (if i < 1258 then (if i < 1256 then decide (1 ≤ count1255 b) else (if i < 1257 then decide (2 ≤ count1255 b) else decide (3 ≤ count1255 b))) else (if i < 1259 then decide (1 ≤ count1258 b) else (if i < 1260 then decide (2 ≤ count1258 b) else decide (3 ≤ count1258 b)))) else (if i < 1264 then (if i < 1262 then decide (4 ≤ count1258 b) else (if i < 1263 then decide (5 ≤ count1258 b) else decide (6 ≤ count1258 b))) else (if i < 1265 then decide (1 ≤ count1264 b) else (if i < 1266 then decide (2 ≤ count1264 b) else decide (3 ≤ count1264 b))))))))) else (if i < 1358 then (if i < 1312 then (if i < 1289 then (if i < 1278 then (if i < 1272 then (if i < 1269 then (if i < 1268 then decide (4 ≤ count1264 b) else decide (5 ≤ count1264 b)) else (if i < 1270 then decide (6 ≤ count1264 b) else (if i < 1271 then decide (7 ≤ count1264 b) else decide (8 ≤ count1264 b)))) else (if i < 1275 then (if i < 1273 then decide (9 ≤ count1264 b) else (if i < 1274 then decide (10 ≤ count1264 b) else decide (11 ≤ count1264 b))) else (if i < 1276 then decide (1 ≤ count1275 b) else (if i < 1277 then decide (2 ≤ count1275 b) else decide (1 ≤ count1277 b))))) else (if i < 1283 then (if i < 1280 then (if i < 1279 then decide (2 ≤ count1277 b) else decide (3 ≤ count1277 b)) else (if i < 1281 then decide (1 ≤ count1280 b) else (if i < 1282 then decide (2 ≤ count1280 b) else decide (1 ≤ count1282 b)))) else (if i < 1286 then (if i < 1284 then decide (2 ≤ count1282 b) else (if i < 1285 then decide (3 ≤ count1282 b) else decide (1 ≤ count1285 b))) else (if i < 1287 then decide (2 ≤ count1285 b) else (if i < 1288 then decide (3 ≤ count1285 b) else decide (4 ≤ count1285 b)))))) else (if i < 1300 then (if i < 1294 then (if i < 1291 then (if i < 1290 then decide (5 ≤ count1285 b) else decide (6 ≤ count1285 b)) else (if i < 1292 then decide (1 ≤ count1291 b) else (if i < 1293 then decide (2 ≤ count1291 b) else decide (1 ≤ count1293 b)))) else (if i < 1297 then (if i < 1295 then decide (2 ≤ count1293 b) else (if i < 1296 then decide (3 ≤ count1293 b) else decide (1 ≤ count1296 b))) else (if i < 1298 then decide (2 ≤ count1296 b) else (if i < 1299 then decide (1 ≤ count1298 b) else decide (2 ≤ count1298 b))))) else (if i < 1306 then (if i < 1303 then (if i < 1301 then decide (1 ≤ count1300 b) else (if i < 1302 then decide (2 ≤ count1300 b) else decide (3 ≤ count1300 b))) else (if i < 1304 then decide (4 ≤ count1300 b) else (if i < 1305 then decide (1 ≤ count1304 b) else decide (2 ≤ count1304 b)))) else (if i < 1309 then (if i < 1307 then decide (3 ≤ count1304 b) else (if i < 1308 then decide (4 ≤ count1304 b) else decide (5 ≤ count1304 b))) else (if i < 1310 then decide (6 ≤ count1304 b) else (if i < 1311 then decide (7 ≤ count1304 b) else decide (1 ≤ count1311 b))))))) else (if i < 1335 then (if i < 1323 then (if i < 1317 then (if i < 1314 then (if i < 1313 then decide (2 ≤ count1311 b) else decide (3 ≤ count1311 b)) else (if i < 1315 then decide (4 ≤ count1311 b) else (if i < 1316 then decide (5 ≤ count1311 b) else decide (6 ≤ count1311 b)))) else (if i < 1320 then (if i < 1318 then decide (7 ≤ count1311 b) else (if i < 1319 then decide (8 ≤ count1311 b) else decide (9 ≤ count1311 b))) else (if i < 1321 then decide (10 ≤ count1311 b) else (if i < 1322 then decide (11 ≤ count1311 b) else decide (1 ≤ count1322 b))))) else (if i < 1329 then (if i < 1326 then (if i < 1324 then decide (2 ≤ count1322 b) else (if i < 1325 then decide (3 ≤ count1322 b) else decide (4 ≤ count1322 b))) else (if i < 1327 then decide (5 ≤ count1322 b) else (if i < 1328 then decide (6 ≤ count1322 b) else decide (7 ≤ count1322 b)))) else (if i < 1332 then (if i < 1330 then decide (8 ≤ count1322 b) else (if i < 1331 then decide (9 ≤ count1322 b) else decide (10 ≤ count1322 b))) else (if i < 1333 then decide (11 ≤ count1322 b) else (if i < 1334 then decide (1 ≤ count1333 b) else decide (2 ≤ count1333 b)))))) else (if i < 1346 then (if i < 1340 then (if i < 1337 then (if i < 1336 then decide (1 ≤ count1335 b) else decide (2 ≤ count1335 b)) else (if i < 1338 then decide (3 ≤ count1335 b) else (if i < 1339 then decide (1 ≤ count1338 b) else decide (2 ≤ count1338 b)))) else (if i < 1343 then (if i < 1341 then decide (1 ≤ count1340 b) else (if i < 1342 then decide (2 ≤ count1340 b) else decide (3 ≤ count1340 b))) else (if i < 1344 then decide (1 ≤ count1343 b) else (if i < 1345 then decide (2 ≤ count1343 b) else decide (3 ≤ count1343 b))))) else (if i < 1352 then (if i < 1349 then (if i < 1347 then decide (4 ≤ count1343 b) else (if i < 1348 then decide (5 ≤ count1343 b) else decide (6 ≤ count1343 b))) else (if i < 1350 then decide (1 ≤ count1349 b) else (if i < 1351 then decide (2 ≤ count1349 b) else decide (1 ≤ count1351 b)))) else (if i < 1355 then (if i < 1353 then decide (2 ≤ count1351 b) else (if i < 1354 then decide (3 ≤ count1351 b) else decide (1 ≤ count1354 b))) else (if i < 1356 then decide (2 ≤ count1354 b) else (if i < 1357 then decide (1 ≤ count1356 b) else decide (2 ≤ count1356 b)))))))) else (if i < 1403 then (if i < 1380 then (if i < 1369 then (if i < 1363 then (if i < 1360 then (if i < 1359 then decide (1 ≤ count1358 b) else decide (2 ≤ count1358 b)) else (if i < 1361 then decide (3 ≤ count1358 b) else (if i < 1362 then decide (4 ≤ count1358 b) else decide (1 ≤ count1362 b)))) else (if i < 1366 then (if i < 1364 then decide (2 ≤ count1362 b) else (if i < 1365 then decide (3 ≤ count1362 b) else decide (4 ≤ count1362 b))) else (if i < 1367 then decide (5 ≤ count1362 b) else (if i < 1368 then decide (6 ≤ count1362 b) else decide (7 ≤ count1362 b))))) else (if i < 1374 then (if i < 1371 then (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)) else (if i < 1372 then decide (3 ≤ count1369 b) else (if i < 1373 then decide (4 ≤ count1369 b) else decide (5 ≤ count1369 b)))) else (if i < 1377 then (if i < 1375 then decide (6 ≤ count1369 b) else (if i < 1376 then decide (7 ≤ count1369 b) else decide (8 ≤ count1369 b))) else (if i < 1378 then decide (9 ≤ count1369 b) else (if i < 1379 then decide (10 ≤ count1369 b) else decide (11 ≤ count1369 b)))))) else (if i < 1391 then (if i < 1385 then (if i < 1382 then (if i < 1381 then decide (1 ≤ count1380 b) else decide (2 ≤ count1380 b)) else (if i < 1383 then decide (1 ≤ count1382 b) else (if i < 1384 then decide (2 ≤ count1382 b) else decide (3 ≤ count1382 b)))) else (if i < 1388 then (if i < 1386 then decide (1 ≤ count1385 b) else (if i < 1387 then decide (2 ≤ count1385 b) else decide (1 ≤ count1387 b))) else (if i < 1389 then decide (2 ≤ count1387 b) else (if i < 1390 then decide (3 ≤ count1387 b) else decide (1 ≤ count1390 b))))) else (if i < 1397 then (if i < 1394 then (if i < 1392 then decide (2 ≤ count1390 b) else (if i < 1393 then decide (3 ≤ count1390 b) else decide (4 ≤ count1390 b))) else (if i < 1395 then decide (5 ≤ count1390 b) else (if i < 1396 then decide (6 ≤ count1390 b) else decide (1 ≤ count1396 b)))) else (if i < 1400 then (if i < 1398 then decide (2 ≤ count1396 b) else (if i < 1399 then decide (1 ≤ count1398 b) else decide (2 ≤ count1398 b))) else (if i < 1401 then decide (3 ≤ count1398 b) else (if i < 1402 then decide (1 ≤ count1401 b) else decide (2 ≤ count1401 b))))))) else (if i < 1426 then (if i < 1414 then (if i < 1408 then (if i < 1405 then (if i < 1404 then decide (1 ≤ count1403 b) else decide (2 ≤ count1403 b)) else (if i < 1406 then decide (1 ≤ count1405 b) else (if i < 1407 then decide (2 ≤ count1405 b) else decide (3 ≤ count1405 b)))) else (if i < 1411 then (if i < 1409 then decide (4 ≤ count1405 b) else (if i < 1410 then decide (1 ≤ count1409 b) else decide (2 ≤ count1409 b))) else (if i < 1412 then decide (3 ≤ count1409 b) else (if i < 1413 then decide (4 ≤ count1409 b) else decide (5 ≤ count1409 b))))) else (if i < 1420 then (if i < 1417 then (if i < 1415 then decide (6 ≤ count1409 b) else (if i < 1416 then decide (7 ≤ count1409 b) else decide (1 ≤ count1416 b))) else (if i < 1418 then decide (2 ≤ count1416 b) else (if i < 1419 then decide (3 ≤ count1416 b) else decide (4 ≤ count1416 b)))) else (if i < 1423 then (if i < 1421 then decide (5 ≤ count1416 b) else (if i < 1422 then decide (6 ≤ count1416 b) else decide (7 ≤ count1416 b))) else (if i < 1424 then decide (8 ≤ count1416 b) else (if i < 1425 then decide (9 ≤ count1416 b) else decide (10 ≤ count1416 b)))))) else (if i < 1437 then (if i < 1431 then (if i < 1428 then (if i < 1427 then decide (11 ≤ count1416 b) else decide (1 ≤ count1427 b)) else (if i < 1429 then decide (2 ≤ count1427 b) else (if i < 1430 then decide (3 ≤ count1427 b) else decide (4 ≤ count1427 b)))) else (if i < 1434 then (if i < 1432 then decide (5 ≤ count1427 b) else (if i < 1433 then decide (6 ≤ count1427 b) else decide (7 ≤ count1427 b))) else (if i < 1435 then decide (8 ≤ count1427 b) else (if i < 1436 then decide (9 ≤ count1427 b) else decide (10 ≤ count1427 b))))) else (if i < 1443 then (if i < 1440 then (if i < 1438 then decide (11 ≤ count1427 b) else (if i < 1439 then decide (1 ≤ count1438 b) else decide (2 ≤ count1438 b))) else (if i < 1441 then decide (3 ≤ count1438 b) else (if i < 1442 then decide (4 ≤ count1438 b) else decide (5 ≤ count1438 b)))) else (if i < 1446 then (if i < 1444 then decide (6 ≤ count1438 b) else (if i < 1445 then decide (7 ≤ count1438 b) else decide (8 ≤ count1438 b))) else (if i < 1447 then decide (9 ≤ count1438 b) else (if i < 1448 then decide (10 ≤ count1438 b) else decide (11 ≤ count1438 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (17 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (18 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (19 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (22 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (32 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (34 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (36 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (38 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (39 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (42 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (44 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (46 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (52 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (53 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (55 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (58 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (96 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (97 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (102 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (103 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (104 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (109 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (111 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (113 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (114 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (115 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (118 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (122 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (124 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (125 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (126 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (128 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (130 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (132 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (134 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (135 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (136 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (137 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (138 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (140 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (142 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (148 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (149 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (151 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (154 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (155 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (159 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (198 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (200 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (201 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (205 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (207 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (214 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (218 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (220 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (222 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (226 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (232 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (236 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (256 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (258 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (262 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (264 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (268 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (270 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (384 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (385 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (390 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (391 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (392 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (393 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (397 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (399 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (402 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (403 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (406 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (410 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (412 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (414 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (486 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (487 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (488 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (498 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (502 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (506 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (508 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (510 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (32 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (34 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (36 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (38 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (39 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (42 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (44 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (46 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (52 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (53 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (55 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (58 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (96 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (97 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (102 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (103 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (104 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (109 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (111 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (113 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (114 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (124 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (126 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (128 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (153 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (154 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (198 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (226 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (232 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (256 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (262 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (270 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (390 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (392 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (402 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (489 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (510 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (1 ≤ count209 (baseVal q)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (1 ≤ count211 (baseVal q)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (1 ≤ count213 (baseVal q)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (1 ≤ count217 (baseVal q)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (2 ≤ count217 (baseVal q)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (2 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (2 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (2 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (2 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (2 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value262 (q : Snake 81) : valuation q 262 = decide (2 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value264 (q : Snake 81) : valuation q 264 = decide (2 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value288 (q : Snake 81) : valuation q 288 = decide (2 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value316 (q : Snake 81) : valuation q 316 = decide (2 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value332 (q : Snake 81) : valuation q 332 = decide (2 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value382 (q : Snake 81) : valuation q 382 = decide (2 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value398 (q : Snake 81) : valuation q 398 = decide (2 ≤ count397 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value408 (q : Snake 81) : valuation q 408 = decide (2 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value715 (q : Snake 81) : valuation q 715 = decide (2 ≤ count714 (baseVal q)) := rfl
theorem value717 (q : Snake 81) : valuation q 717 = decide (2 ≤ count716 (baseVal q)) := rfl
theorem value720 (q : Snake 81) : valuation q 720 = decide (2 ≤ count719 (baseVal q)) := rfl
theorem value725 (q : Snake 81) : valuation q 725 = decide (1 ≤ count725 (baseVal q)) := rfl
theorem value728 (q : Snake 81) : valuation q 728 = decide (2 ≤ count727 (baseVal q)) := rfl
theorem value733 (q : Snake 81) : valuation q 733 = decide (2 ≤ count732 (baseVal q)) := rfl
theorem value735 (q : Snake 81) : valuation q 735 = decide (2 ≤ count734 (baseVal q)) := rfl
theorem value741 (q : Snake 81) : valuation q 741 = decide (4 ≤ count738 (baseVal q)) := rfl
theorem value750 (q : Snake 81) : valuation q 750 = decide (6 ≤ count745 (baseVal q)) := rfl
theorem value758 (q : Snake 81) : valuation q 758 = decide (1 ≤ count758 (baseVal q)) := rfl
theorem value761 (q : Snake 81) : valuation q 761 = decide (2 ≤ count760 (baseVal q)) := rfl
theorem value769 (q : Snake 81) : valuation q 769 = decide (2 ≤ count768 (baseVal q)) := rfl
theorem value776 (q : Snake 81) : valuation q 776 = decide (1 ≤ count776 (baseVal q)) := rfl
theorem value779 (q : Snake 81) : valuation q 779 = decide (1 ≤ count779 (baseVal q)) := rfl
theorem value781 (q : Snake 81) : valuation q 781 = decide (1 ≤ count781 (baseVal q)) := rfl
theorem value783 (q : Snake 81) : valuation q 783 = decide (1 ≤ count783 (baseVal q)) := rfl
theorem value787 (q : Snake 81) : valuation q 787 = decide (1 ≤ count787 (baseVal q)) := rfl
theorem value796 (q : Snake 81) : valuation q 796 = decide (3 ≤ count794 (baseVal q)) := rfl
theorem value815 (q : Snake 81) : valuation q 815 = decide (9 ≤ count807 (baseVal q)) := rfl
theorem value820 (q : Snake 81) : valuation q 820 = decide (1 ≤ count820 (baseVal q)) := rfl
theorem value822 (q : Snake 81) : valuation q 822 = decide (1 ≤ count822 (baseVal q)) := rfl
theorem value825 (q : Snake 81) : valuation q 825 = decide (1 ≤ count825 (baseVal q)) := rfl
theorem value827 (q : Snake 81) : valuation q 827 = decide (1 ≤ count827 (baseVal q)) := rfl
theorem value831 (q : Snake 81) : valuation q 831 = decide (2 ≤ count830 (baseVal q)) := rfl
theorem value836 (q : Snake 81) : valuation q 836 = decide (1 ≤ count836 (baseVal q)) := rfl
theorem value838 (q : Snake 81) : valuation q 838 = decide (1 ≤ count838 (baseVal q)) := rfl
theorem value841 (q : Snake 81) : valuation q 841 = decide (1 ≤ count841 (baseVal q)) := rfl
theorem value845 (q : Snake 81) : valuation q 845 = decide (1 ≤ count845 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (2 ≤ count849 (baseVal q)) := rfl
theorem value859 (q : Snake 81) : valuation q 859 = decide (4 ≤ count856 (baseVal q)) := rfl
theorem value925 (q : Snake 81) : valuation q 925 = decide (4 ≤ count922 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (13 ≤ count935 (baseVal q)) := rfl
theorem value1232 (q : Snake 81) : valuation q 1232 = decide (1 ≤ count1232 (baseVal q)) := rfl
theorem value1233 (q : Snake 81) : valuation q 1233 = decide (2 ≤ count1232 (baseVal q)) := rfl
theorem value1234 (q : Snake 81) : valuation q 1234 = decide (1 ≤ count1234 (baseVal q)) := rfl
theorem value1235 (q : Snake 81) : valuation q 1235 = decide (2 ≤ count1234 (baseVal q)) := rfl
theorem value1236 (q : Snake 81) : valuation q 1236 = decide (3 ≤ count1234 (baseVal q)) := rfl
theorem value1237 (q : Snake 81) : valuation q 1237 = decide (1 ≤ count1237 (baseVal q)) := rfl
theorem value1238 (q : Snake 81) : valuation q 1238 = decide (2 ≤ count1237 (baseVal q)) := rfl
theorem value1239 (q : Snake 81) : valuation q 1239 = decide (1 ≤ count1239 (baseVal q)) := rfl
theorem value1240 (q : Snake 81) : valuation q 1240 = decide (2 ≤ count1239 (baseVal q)) := rfl
theorem value1241 (q : Snake 81) : valuation q 1241 = decide (3 ≤ count1239 (baseVal q)) := rfl
theorem value1242 (q : Snake 81) : valuation q 1242 = decide (1 ≤ count1242 (baseVal q)) := rfl
theorem value1243 (q : Snake 81) : valuation q 1243 = decide (2 ≤ count1242 (baseVal q)) := rfl
theorem value1244 (q : Snake 81) : valuation q 1244 = decide (3 ≤ count1242 (baseVal q)) := rfl
theorem value1245 (q : Snake 81) : valuation q 1245 = decide (4 ≤ count1242 (baseVal q)) := rfl
theorem value1246 (q : Snake 81) : valuation q 1246 = decide (5 ≤ count1242 (baseVal q)) := rfl
theorem value1248 (q : Snake 81) : valuation q 1248 = decide (1 ≤ count1248 (baseVal q)) := rfl
theorem value1249 (q : Snake 81) : valuation q 1249 = decide (2 ≤ count1248 (baseVal q)) := rfl
theorem value1250 (q : Snake 81) : valuation q 1250 = decide (1 ≤ count1250 (baseVal q)) := rfl
theorem value1251 (q : Snake 81) : valuation q 1251 = decide (2 ≤ count1250 (baseVal q)) := rfl
theorem value1252 (q : Snake 81) : valuation q 1252 = decide (3 ≤ count1250 (baseVal q)) := rfl
theorem value1253 (q : Snake 81) : valuation q 1253 = decide (1 ≤ count1253 (baseVal q)) := rfl
theorem value1254 (q : Snake 81) : valuation q 1254 = decide (2 ≤ count1253 (baseVal q)) := rfl
theorem value1255 (q : Snake 81) : valuation q 1255 = decide (1 ≤ count1255 (baseVal q)) := rfl
theorem value1256 (q : Snake 81) : valuation q 1256 = decide (2 ≤ count1255 (baseVal q)) := rfl
theorem value1257 (q : Snake 81) : valuation q 1257 = decide (3 ≤ count1255 (baseVal q)) := rfl
theorem value1258 (q : Snake 81) : valuation q 1258 = decide (1 ≤ count1258 (baseVal q)) := rfl
theorem value1259 (q : Snake 81) : valuation q 1259 = decide (2 ≤ count1258 (baseVal q)) := rfl
theorem value1260 (q : Snake 81) : valuation q 1260 = decide (3 ≤ count1258 (baseVal q)) := rfl
theorem value1261 (q : Snake 81) : valuation q 1261 = decide (4 ≤ count1258 (baseVal q)) := rfl
theorem value1262 (q : Snake 81) : valuation q 1262 = decide (5 ≤ count1258 (baseVal q)) := rfl
theorem value1263 (q : Snake 81) : valuation q 1263 = decide (6 ≤ count1258 (baseVal q)) := rfl
theorem value1264 (q : Snake 81) : valuation q 1264 = decide (1 ≤ count1264 (baseVal q)) := rfl
theorem value1265 (q : Snake 81) : valuation q 1265 = decide (2 ≤ count1264 (baseVal q)) := rfl
theorem value1266 (q : Snake 81) : valuation q 1266 = decide (3 ≤ count1264 (baseVal q)) := rfl
theorem value1267 (q : Snake 81) : valuation q 1267 = decide (4 ≤ count1264 (baseVal q)) := rfl
theorem value1268 (q : Snake 81) : valuation q 1268 = decide (5 ≤ count1264 (baseVal q)) := rfl
theorem value1269 (q : Snake 81) : valuation q 1269 = decide (6 ≤ count1264 (baseVal q)) := rfl
theorem value1270 (q : Snake 81) : valuation q 1270 = decide (7 ≤ count1264 (baseVal q)) := rfl
theorem value1275 (q : Snake 81) : valuation q 1275 = decide (1 ≤ count1275 (baseVal q)) := rfl
theorem value1276 (q : Snake 81) : valuation q 1276 = decide (2 ≤ count1275 (baseVal q)) := rfl
theorem value1277 (q : Snake 81) : valuation q 1277 = decide (1 ≤ count1277 (baseVal q)) := rfl
theorem value1278 (q : Snake 81) : valuation q 1278 = decide (2 ≤ count1277 (baseVal q)) := rfl
theorem value1280 (q : Snake 81) : valuation q 1280 = decide (1 ≤ count1280 (baseVal q)) := rfl
theorem value1281 (q : Snake 81) : valuation q 1281 = decide (2 ≤ count1280 (baseVal q)) := rfl
theorem value1282 (q : Snake 81) : valuation q 1282 = decide (1 ≤ count1282 (baseVal q)) := rfl
theorem value1283 (q : Snake 81) : valuation q 1283 = decide (2 ≤ count1282 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (1 ≤ count1285 (baseVal q)) := rfl
theorem value1286 (q : Snake 81) : valuation q 1286 = decide (2 ≤ count1285 (baseVal q)) := rfl
theorem value1287 (q : Snake 81) : valuation q 1287 = decide (3 ≤ count1285 (baseVal q)) := rfl
theorem value1288 (q : Snake 81) : valuation q 1288 = decide (4 ≤ count1285 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (1 ≤ count1291 (baseVal q)) := rfl
theorem value1292 (q : Snake 81) : valuation q 1292 = decide (2 ≤ count1291 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (1 ≤ count1293 (baseVal q)) := rfl
theorem value1294 (q : Snake 81) : valuation q 1294 = decide (2 ≤ count1293 (baseVal q)) := rfl
theorem value1295 (q : Snake 81) : valuation q 1295 = decide (3 ≤ count1293 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (1 ≤ count1296 (baseVal q)) := rfl
theorem value1297 (q : Snake 81) : valuation q 1297 = decide (2 ≤ count1296 (baseVal q)) := rfl
theorem value1298 (q : Snake 81) : valuation q 1298 = decide (1 ≤ count1298 (baseVal q)) := rfl
theorem value1300 (q : Snake 81) : valuation q 1300 = decide (1 ≤ count1300 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (2 ≤ count1300 (baseVal q)) := rfl
theorem value1304 (q : Snake 81) : valuation q 1304 = decide (1 ≤ count1304 (baseVal q)) := rfl
theorem value1305 (q : Snake 81) : valuation q 1305 = decide (2 ≤ count1304 (baseVal q)) := rfl
theorem value1306 (q : Snake 81) : valuation q 1306 = decide (3 ≤ count1304 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (1 ≤ count1311 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (2 ≤ count1311 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (3 ≤ count1311 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (4 ≤ count1311 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (5 ≤ count1311 (baseVal q)) := rfl
theorem value1325 (q : Snake 81) : valuation q 1325 = decide (4 ≤ count1322 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (5 ≤ count1322 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (6 ≤ count1322 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (7 ≤ count1322 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (8 ≤ count1322 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (9 ≤ count1322 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (1 ≤ count1333 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (2 ≤ count1333 (baseVal q)) := rfl
theorem value1335 (q : Snake 81) : valuation q 1335 = decide (1 ≤ count1335 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (2 ≤ count1335 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (1 ≤ count1338 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (1 ≤ count1343 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (2 ≤ count1343 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (3 ≤ count1343 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (2 ≤ count1349 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (1 ≤ count1351 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (2 ≤ count1351 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (3 ≤ count1351 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (1 ≤ count1354 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (2 ≤ count1354 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (1 ≤ count1356 (baseVal q)) := rfl
theorem value1358 (q : Snake 81) : valuation q 1358 = decide (1 ≤ count1358 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (2 ≤ count1358 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (1 ≤ count1362 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (2 ≤ count1362 (baseVal q)) := rfl
theorem value1364 (q : Snake 81) : valuation q 1364 = decide (3 ≤ count1362 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (4 ≤ count1362 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (1 ≤ count1369 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (2 ≤ count1369 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (3 ≤ count1369 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (4 ≤ count1369 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (5 ≤ count1369 (baseVal q)) := rfl
theorem value1380 (q : Snake 81) : valuation q 1380 = decide (1 ≤ count1380 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (1 ≤ count1382 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (1 ≤ count1385 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (1 ≤ count1387 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (1 ≤ count1390 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (1 ≤ count1396 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (1 ≤ count1398 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (1 ≤ count1401 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (1 ≤ count1403 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (1 ≤ count1405 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (1 ≤ count1409 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (2 ≤ count1409 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (2 ≤ count1416 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (3 ≤ count1416 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (2 ≤ count1427 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (3 ≤ count1427 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (4 ≤ count1427 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (5 ≤ count1427 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (6 ≤ count1427 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (7 ≤ count1427 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (11 ≤ count1438 (baseVal q)) := rfl
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
theorem meaningNeg74 (b : Nat → Bool) : literal (valuationOf b) (-74) = decide (1 ≤ countLit b [-74]) := by
  change literal b (-74) = decide (1 ≤ countLit b [-74])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-74) <;> decide
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
theorem meaningNeg45 (b : Nat → Bool) : literal (valuationOf b) (-45) = decide (1 ≤ countLit b [-45]) := by
  change literal b (-45) = decide (1 ≤ countLit b [-45])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-45) <;> decide
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
theorem meaningNeg2 (b : Nat → Bool) : literal (valuationOf b) (-2) = decide (1 ≤ countLit b [-2]) := by
  change literal b (-2) = decide (1 ≤ countLit b [-2])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-2) <;> decide
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
theorem meaning112 (b : Nat → Bool) : literal (valuationOf b) (112) = decide (1 ≤ countLit b [112]) := by
  change literal b (112) = decide (1 ≤ countLit b [112])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (112) <;> decide
theorem meaning115 (b : Nat → Bool) : literal (valuationOf b) (115) = decide (1 ≤ countLit b [115]) := by
  change literal b (115) = decide (1 ≤ countLit b [115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (115) <;> decide
theorem meaning117 (b : Nat → Bool) : literal (valuationOf b) (117) = decide (1 ≤ countLit b [117]) := by
  change literal b (117) = decide (1 ≤ countLit b [117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (117) <;> decide
theorem meaning118 (b : Nat → Bool) : literal (valuationOf b) (118) = decide (1 ≤ countLit b [118]) := by
  change literal b (118) = decide (1 ≤ countLit b [118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (118) <;> decide
theorem meaning120 (b : Nat → Bool) : literal (valuationOf b) (120) = decide (1 ≤ countLit b [120]) := by
  change literal b (120) = decide (1 ≤ countLit b [120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (120) <;> decide
theorem meaning122 (b : Nat → Bool) : literal (valuationOf b) (122) = decide (1 ≤ countLit b [122]) := by
  change literal b (122) = decide (1 ≤ countLit b [122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (122) <;> decide
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
theorem meaning127 (b : Nat → Bool) : literal (valuationOf b) (127) = decide (1 ≤ countLit b [127]) := by
  change literal b (127) = decide (1 ≤ countLit b [127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (127) <;> decide
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
theorem meaning139 (b : Nat → Bool) : literal (valuationOf b) (139) = decide (1 ≤ countLit b [139]) := by
  change literal b (139) = decide (1 ≤ countLit b [139])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (139) <;> decide
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
theorem meaning147 (b : Nat → Bool) : literal (valuationOf b) (147) = decide (1 ≤ countLit b [147]) := by
  change literal b (147) = decide (1 ≤ countLit b [147])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (147) <;> decide
theorem meaning149 (b : Nat → Bool) : literal (valuationOf b) (149) = decide (1 ≤ countLit b [149]) := by
  change literal b (149) = decide (1 ≤ countLit b [149])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (149) <;> decide
theorem meaning151 (b : Nat → Bool) : literal (valuationOf b) (151) = decide (1 ≤ countLit b [151]) := by
  change literal b (151) = decide (1 ≤ countLit b [151])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (151) <;> decide
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
theorem meaning159 (b : Nat → Bool) : literal (valuationOf b) (159) = decide (1 ≤ countLit b [159]) := by
  change literal b (159) = decide (1 ≤ countLit b [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (159) <;> decide
theorem meaning161 (b : Nat → Bool) : literal (valuationOf b) (161) = decide (1 ≤ countLit b [161]) := by
  change literal b (161) = decide (1 ≤ countLit b [161])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (161) <;> decide
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
theorem meaning178 (b : Nat → Bool) : literal (valuationOf b) (178) = decide (1 ≤ countLit b [178]) := by
  change literal b (178) = decide (1 ≤ countLit b [178])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (178) <;> decide
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
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
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) (199) = decide (1 ≤ countLit b [199]) := by
  change literal b (199) = decide (1 ≤ countLit b [199])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (199) <;> decide
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
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) 218 = decide (2 ≤ count217 b) := rfl
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) 222 = decide (2 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) 228 = decide (2 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) 230 = decide (2 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) 238 = decide (2 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) 252 = decide (2 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning262 (b : Nat → Bool) : literal (valuationOf b) 262 = decide (2 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning264 (b : Nat → Bool) : literal (valuationOf b) 264 = decide (2 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning288 (b : Nat → Bool) : literal (valuationOf b) 288 = decide (2 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning316 (b : Nat → Bool) : literal (valuationOf b) 316 = decide (2 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning332 (b : Nat → Bool) : literal (valuationOf b) 332 = decide (2 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning356 (b : Nat → Bool) : literal (valuationOf b) 356 = decide (2 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning380 (b : Nat → Bool) : literal (valuationOf b) 380 = decide (2 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning382 (b : Nat → Bool) : literal (valuationOf b) 382 = decide (2 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning398 (b : Nat → Bool) : literal (valuationOf b) 398 = decide (2 ≤ count397 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning402 (b : Nat → Bool) : literal (valuationOf b) 402 = decide (2 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning408 (b : Nat → Bool) : literal (valuationOf b) 408 = decide (2 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning715 (b : Nat → Bool) : literal (valuationOf b) 715 = decide (2 ≤ count714 b) := rfl
theorem meaning717 (b : Nat → Bool) : literal (valuationOf b) 717 = decide (2 ≤ count716 b) := rfl
theorem meaning720 (b : Nat → Bool) : literal (valuationOf b) 720 = decide (2 ≤ count719 b) := rfl
theorem meaning725 (b : Nat → Bool) : literal (valuationOf b) 725 = decide (1 ≤ count725 b) := rfl
theorem meaning728 (b : Nat → Bool) : literal (valuationOf b) 728 = decide (2 ≤ count727 b) := rfl
theorem meaning733 (b : Nat → Bool) : literal (valuationOf b) 733 = decide (2 ≤ count732 b) := rfl
theorem meaning735 (b : Nat → Bool) : literal (valuationOf b) 735 = decide (2 ≤ count734 b) := rfl
theorem meaning741 (b : Nat → Bool) : literal (valuationOf b) 741 = decide (4 ≤ count738 b) := rfl
theorem meaning750 (b : Nat → Bool) : literal (valuationOf b) 750 = decide (6 ≤ count745 b) := rfl
theorem meaning758 (b : Nat → Bool) : literal (valuationOf b) 758 = decide (1 ≤ count758 b) := rfl
theorem meaning761 (b : Nat → Bool) : literal (valuationOf b) 761 = decide (2 ≤ count760 b) := rfl
theorem meaning769 (b : Nat → Bool) : literal (valuationOf b) 769 = decide (2 ≤ count768 b) := rfl
theorem meaning776 (b : Nat → Bool) : literal (valuationOf b) 776 = decide (1 ≤ count776 b) := rfl
theorem meaning779 (b : Nat → Bool) : literal (valuationOf b) 779 = decide (1 ≤ count779 b) := rfl
theorem meaning781 (b : Nat → Bool) : literal (valuationOf b) 781 = decide (1 ≤ count781 b) := rfl
theorem meaning783 (b : Nat → Bool) : literal (valuationOf b) 783 = decide (1 ≤ count783 b) := rfl
theorem meaning787 (b : Nat → Bool) : literal (valuationOf b) 787 = decide (1 ≤ count787 b) := rfl
theorem meaning796 (b : Nat → Bool) : literal (valuationOf b) 796 = decide (3 ≤ count794 b) := rfl
theorem meaning815 (b : Nat → Bool) : literal (valuationOf b) 815 = decide (9 ≤ count807 b) := rfl
theorem meaning820 (b : Nat → Bool) : literal (valuationOf b) 820 = decide (1 ≤ count820 b) := rfl
theorem meaning822 (b : Nat → Bool) : literal (valuationOf b) 822 = decide (1 ≤ count822 b) := rfl
theorem meaning825 (b : Nat → Bool) : literal (valuationOf b) 825 = decide (1 ≤ count825 b) := rfl
theorem meaning827 (b : Nat → Bool) : literal (valuationOf b) 827 = decide (1 ≤ count827 b) := rfl
theorem meaning831 (b : Nat → Bool) : literal (valuationOf b) 831 = decide (2 ≤ count830 b) := rfl
theorem meaning836 (b : Nat → Bool) : literal (valuationOf b) 836 = decide (1 ≤ count836 b) := rfl
theorem meaning838 (b : Nat → Bool) : literal (valuationOf b) 838 = decide (1 ≤ count838 b) := rfl
theorem meaning841 (b : Nat → Bool) : literal (valuationOf b) 841 = decide (1 ≤ count841 b) := rfl
theorem meaning845 (b : Nat → Bool) : literal (valuationOf b) 845 = decide (1 ≤ count845 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (2 ≤ count849 b) := rfl
theorem meaning859 (b : Nat → Bool) : literal (valuationOf b) 859 = decide (4 ≤ count856 b) := rfl
theorem meaning925 (b : Nat → Bool) : literal (valuationOf b) 925 = decide (4 ≤ count922 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (13 ≤ count935 b) := rfl
theorem meaning1232 (b : Nat → Bool) : literal (valuationOf b) 1232 = decide (1 ≤ count1232 b) := rfl
theorem meaning1233 (b : Nat → Bool) : literal (valuationOf b) 1233 = decide (2 ≤ count1232 b) := rfl
theorem meaning1234 (b : Nat → Bool) : literal (valuationOf b) 1234 = decide (1 ≤ count1234 b) := rfl
theorem meaning1235 (b : Nat → Bool) : literal (valuationOf b) 1235 = decide (2 ≤ count1234 b) := rfl
theorem meaning1236 (b : Nat → Bool) : literal (valuationOf b) 1236 = decide (3 ≤ count1234 b) := rfl
theorem meaning1237 (b : Nat → Bool) : literal (valuationOf b) 1237 = decide (1 ≤ count1237 b) := rfl
theorem meaning1238 (b : Nat → Bool) : literal (valuationOf b) 1238 = decide (2 ≤ count1237 b) := rfl
theorem meaning1239 (b : Nat → Bool) : literal (valuationOf b) 1239 = decide (1 ≤ count1239 b) := rfl
theorem meaning1240 (b : Nat → Bool) : literal (valuationOf b) 1240 = decide (2 ≤ count1239 b) := rfl
theorem meaning1241 (b : Nat → Bool) : literal (valuationOf b) 1241 = decide (3 ≤ count1239 b) := rfl
theorem meaning1242 (b : Nat → Bool) : literal (valuationOf b) 1242 = decide (1 ≤ count1242 b) := rfl
theorem meaning1243 (b : Nat → Bool) : literal (valuationOf b) 1243 = decide (2 ≤ count1242 b) := rfl
theorem meaning1244 (b : Nat → Bool) : literal (valuationOf b) 1244 = decide (3 ≤ count1242 b) := rfl
theorem meaning1245 (b : Nat → Bool) : literal (valuationOf b) 1245 = decide (4 ≤ count1242 b) := rfl
theorem meaning1246 (b : Nat → Bool) : literal (valuationOf b) 1246 = decide (5 ≤ count1242 b) := rfl
theorem meaning1248 (b : Nat → Bool) : literal (valuationOf b) 1248 = decide (1 ≤ count1248 b) := rfl
theorem meaning1249 (b : Nat → Bool) : literal (valuationOf b) 1249 = decide (2 ≤ count1248 b) := rfl
theorem meaning1250 (b : Nat → Bool) : literal (valuationOf b) 1250 = decide (1 ≤ count1250 b) := rfl
theorem meaning1251 (b : Nat → Bool) : literal (valuationOf b) 1251 = decide (2 ≤ count1250 b) := rfl
theorem meaning1252 (b : Nat → Bool) : literal (valuationOf b) 1252 = decide (3 ≤ count1250 b) := rfl
theorem meaning1253 (b : Nat → Bool) : literal (valuationOf b) 1253 = decide (1 ≤ count1253 b) := rfl
theorem meaning1254 (b : Nat → Bool) : literal (valuationOf b) 1254 = decide (2 ≤ count1253 b) := rfl
theorem meaning1255 (b : Nat → Bool) : literal (valuationOf b) 1255 = decide (1 ≤ count1255 b) := rfl
theorem meaning1256 (b : Nat → Bool) : literal (valuationOf b) 1256 = decide (2 ≤ count1255 b) := rfl
theorem meaning1257 (b : Nat → Bool) : literal (valuationOf b) 1257 = decide (3 ≤ count1255 b) := rfl
theorem meaning1258 (b : Nat → Bool) : literal (valuationOf b) 1258 = decide (1 ≤ count1258 b) := rfl
theorem meaning1259 (b : Nat → Bool) : literal (valuationOf b) 1259 = decide (2 ≤ count1258 b) := rfl
theorem meaning1260 (b : Nat → Bool) : literal (valuationOf b) 1260 = decide (3 ≤ count1258 b) := rfl
theorem meaning1261 (b : Nat → Bool) : literal (valuationOf b) 1261 = decide (4 ≤ count1258 b) := rfl
theorem meaning1262 (b : Nat → Bool) : literal (valuationOf b) 1262 = decide (5 ≤ count1258 b) := rfl
theorem meaning1263 (b : Nat → Bool) : literal (valuationOf b) 1263 = decide (6 ≤ count1258 b) := rfl
theorem meaning1264 (b : Nat → Bool) : literal (valuationOf b) 1264 = decide (1 ≤ count1264 b) := rfl
theorem meaning1265 (b : Nat → Bool) : literal (valuationOf b) 1265 = decide (2 ≤ count1264 b) := rfl
theorem meaning1266 (b : Nat → Bool) : literal (valuationOf b) 1266 = decide (3 ≤ count1264 b) := rfl
theorem meaning1267 (b : Nat → Bool) : literal (valuationOf b) 1267 = decide (4 ≤ count1264 b) := rfl
theorem meaning1268 (b : Nat → Bool) : literal (valuationOf b) 1268 = decide (5 ≤ count1264 b) := rfl
theorem meaning1269 (b : Nat → Bool) : literal (valuationOf b) 1269 = decide (6 ≤ count1264 b) := rfl
theorem meaning1270 (b : Nat → Bool) : literal (valuationOf b) 1270 = decide (7 ≤ count1264 b) := rfl
theorem meaning1275 (b : Nat → Bool) : literal (valuationOf b) 1275 = decide (1 ≤ count1275 b) := rfl
theorem meaning1276 (b : Nat → Bool) : literal (valuationOf b) 1276 = decide (2 ≤ count1275 b) := rfl
theorem meaning1277 (b : Nat → Bool) : literal (valuationOf b) 1277 = decide (1 ≤ count1277 b) := rfl
theorem meaning1278 (b : Nat → Bool) : literal (valuationOf b) 1278 = decide (2 ≤ count1277 b) := rfl
theorem meaning1280 (b : Nat → Bool) : literal (valuationOf b) 1280 = decide (1 ≤ count1280 b) := rfl
theorem meaning1281 (b : Nat → Bool) : literal (valuationOf b) 1281 = decide (2 ≤ count1280 b) := rfl
theorem meaning1282 (b : Nat → Bool) : literal (valuationOf b) 1282 = decide (1 ≤ count1282 b) := rfl
theorem meaning1283 (b : Nat → Bool) : literal (valuationOf b) 1283 = decide (2 ≤ count1282 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (1 ≤ count1285 b) := rfl
theorem meaning1286 (b : Nat → Bool) : literal (valuationOf b) 1286 = decide (2 ≤ count1285 b) := rfl
theorem meaning1287 (b : Nat → Bool) : literal (valuationOf b) 1287 = decide (3 ≤ count1285 b) := rfl
theorem meaning1288 (b : Nat → Bool) : literal (valuationOf b) 1288 = decide (4 ≤ count1285 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (1 ≤ count1291 b) := rfl
theorem meaning1292 (b : Nat → Bool) : literal (valuationOf b) 1292 = decide (2 ≤ count1291 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (1 ≤ count1293 b) := rfl
theorem meaning1294 (b : Nat → Bool) : literal (valuationOf b) 1294 = decide (2 ≤ count1293 b) := rfl
theorem meaning1295 (b : Nat → Bool) : literal (valuationOf b) 1295 = decide (3 ≤ count1293 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (1 ≤ count1296 b) := rfl
theorem meaning1297 (b : Nat → Bool) : literal (valuationOf b) 1297 = decide (2 ≤ count1296 b) := rfl
theorem meaning1298 (b : Nat → Bool) : literal (valuationOf b) 1298 = decide (1 ≤ count1298 b) := rfl
theorem meaning1300 (b : Nat → Bool) : literal (valuationOf b) 1300 = decide (1 ≤ count1300 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (2 ≤ count1300 b) := rfl
theorem meaning1304 (b : Nat → Bool) : literal (valuationOf b) 1304 = decide (1 ≤ count1304 b) := rfl
theorem meaning1305 (b : Nat → Bool) : literal (valuationOf b) 1305 = decide (2 ≤ count1304 b) := rfl
theorem meaning1306 (b : Nat → Bool) : literal (valuationOf b) 1306 = decide (3 ≤ count1304 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (1 ≤ count1311 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (2 ≤ count1311 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (3 ≤ count1311 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (4 ≤ count1311 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (5 ≤ count1311 b) := rfl
theorem meaning1325 (b : Nat → Bool) : literal (valuationOf b) 1325 = decide (4 ≤ count1322 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (5 ≤ count1322 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (6 ≤ count1322 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (7 ≤ count1322 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (8 ≤ count1322 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (9 ≤ count1322 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (1 ≤ count1333 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (2 ≤ count1333 b) := rfl
theorem meaning1335 (b : Nat → Bool) : literal (valuationOf b) 1335 = decide (1 ≤ count1335 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (2 ≤ count1335 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (1 ≤ count1338 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (1 ≤ count1343 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (2 ≤ count1343 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (3 ≤ count1343 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (2 ≤ count1349 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (1 ≤ count1351 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (2 ≤ count1351 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (3 ≤ count1351 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (1 ≤ count1354 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (2 ≤ count1354 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (1 ≤ count1356 b) := rfl
theorem meaning1358 (b : Nat → Bool) : literal (valuationOf b) 1358 = decide (1 ≤ count1358 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (2 ≤ count1358 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (1 ≤ count1362 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (2 ≤ count1362 b) := rfl
theorem meaning1364 (b : Nat → Bool) : literal (valuationOf b) 1364 = decide (3 ≤ count1362 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (4 ≤ count1362 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (1 ≤ count1369 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (2 ≤ count1369 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (3 ≤ count1369 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (4 ≤ count1369 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (5 ≤ count1369 b) := rfl
theorem meaning1380 (b : Nat → Bool) : literal (valuationOf b) 1380 = decide (1 ≤ count1380 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (1 ≤ count1382 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (1 ≤ count1385 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (1 ≤ count1387 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (1 ≤ count1390 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (1 ≤ count1396 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (1 ≤ count1398 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (1 ≤ count1401 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (1 ≤ count1403 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (1 ≤ count1405 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (1 ≤ count1409 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (2 ≤ count1409 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (2 ≤ count1416 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (3 ≤ count1416 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (2 ≤ count1427 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (3 ≤ count1427 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (4 ≤ count1427 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (5 ≤ count1427 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (6 ≤ count1427 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (7 ≤ count1427 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (11 ≤ count1438 b) := rfl
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
end Snake9.Regrowth.E112145
