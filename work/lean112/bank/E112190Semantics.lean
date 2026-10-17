import E112190Data
namespace Snake9.Regrowth.E112190
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 108 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (34 : Vertex)) else decide (InPath q (35 : Vertex)))) else (if i < 4 then decide (InPath q (36 : Vertex)) else (if i < 5 then decide (InPath q (37 : Vertex)) else decide (InPath q (42 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (43 : Vertex)) else (if i < 8 then decide (InPath q (44 : Vertex)) else decide (InPath q (46 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (48 : Vertex)) else decide (InPath q (52 : Vertex))) else (if i < 12 then decide (InPath q (53 : Vertex)) else decide (InPath q (55 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (56 : Vertex)) else (if i < 15 then decide (InPath q (57 : Vertex)) else decide (InPath q (59 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (63 : Vertex)) else decide (InPath q (80 : Vertex))) else (if i < 19 then decide (InPath q (96 : Vertex)) else decide (InPath q (98 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (99 : Vertex)) else (if i < 22 then decide (InPath q (112 : Vertex)) else decide (InPath q (113 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (114 : Vertex)) else decide (InPath q (115 : Vertex))) else (if i < 26 then decide (InPath q (118 : Vertex)) else decide (InPath q (120 : Vertex))))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then decide (InPath q (124 : Vertex)) else (if i < 29 then decide (InPath q (126 : Vertex)) else decide (InPath q (130 : Vertex)))) else (if i < 31 then decide (InPath q (131 : Vertex)) else (if i < 32 then decide (InPath q (132 : Vertex)) else decide (InPath q (133 : Vertex))))) else (if i < 36 then (if i < 34 then decide (InPath q (138 : Vertex)) else (if i < 35 then decide (InPath q (139 : Vertex)) else decide (InPath q (140 : Vertex)))) else (if i < 38 then (if i < 37 then decide (InPath q (142 : Vertex)) else decide (InPath q (144 : Vertex))) else (if i < 39 then decide (InPath q (148 : Vertex)) else decide (InPath q (149 : Vertex)))))) else (if i < 47 then (if i < 43 then (if i < 41 then decide (InPath q (151 : Vertex)) else (if i < 42 then decide (InPath q (152 : Vertex)) else decide (InPath q (153 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (155 : Vertex)) else decide (InPath q (159 : Vertex))) else (if i < 46 then decide (InPath q (226 : Vertex)) else decide (InPath q (227 : Vertex))))) else (if i < 50 then (if i < 48 then decide (InPath q (228 : Vertex)) else (if i < 49 then decide (InPath q (229 : Vertex)) else decide (InPath q (234 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (235 : Vertex)) else decide (InPath q (236 : Vertex))) else (if i < 53 then decide (InPath q (238 : Vertex)) else decide (InPath q (240 : Vertex)))))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then decide (InPath q (244 : Vertex)) else (if i < 56 then decide (InPath q (245 : Vertex)) else decide (InPath q (247 : Vertex)))) else (if i < 58 then decide (InPath q (248 : Vertex)) else (if i < 59 then decide (InPath q (249 : Vertex)) else decide (InPath q (251 : Vertex))))) else (if i < 63 then (if i < 61 then decide (InPath q (255 : Vertex)) else (if i < 62 then decide (InPath q (258 : Vertex)) else decide (InPath q (259 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (260 : Vertex)) else decide (InPath q (261 : Vertex))) else (if i < 66 then decide (InPath q (266 : Vertex)) else decide (InPath q (268 : Vertex)))))) else (if i < 74 then (if i < 70 then (if i < 68 then decide (InPath q (270 : Vertex)) else (if i < 69 then decide (InPath q (272 : Vertex)) else decide (InPath q (276 : Vertex)))) else (if i < 72 then (if i < 71 then decide (InPath q (277 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 73 then decide (InPath q (280 : Vertex)) else decide (InPath q (281 : Vertex))))) else (if i < 77 then (if i < 75 then decide (InPath q (283 : Vertex)) else (if i < 76 then decide (InPath q (287 : Vertex)) else decide (InPath q (384 : Vertex)))) else (if i < 79 then (if i < 78 then decide (InPath q (387 : Vertex)) else decide (InPath q (400 : Vertex))) else (if i < 80 then decide (InPath q (401 : Vertex)) else decide (InPath q (403 : Vertex))))))) else (if i < 94 then (if i < 87 then (if i < 84 then (if i < 82 then decide (InPath q (419 : Vertex)) else (if i < 83 then decide (InPath q (421 : Vertex)) else decide (InPath q (427 : Vertex)))) else (if i < 85 then decide (InPath q (432 : Vertex)) else (if i < 86 then decide (InPath q (436 : Vertex)) else decide (InPath q (437 : Vertex))))) else (if i < 90 then (if i < 88 then decide (InPath q (439 : Vertex)) else (if i < 89 then decide (InPath q (441 : Vertex)) else decide (InPath q (443 : Vertex)))) else (if i < 92 then (if i < 91 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex))) else (if i < 93 then decide (InPath q (481 : Vertex)) else decide (InPath q (482 : Vertex)))))) else (if i < 101 then (if i < 97 then (if i < 95 then decide (InPath q (483 : Vertex)) else (if i < 96 then decide (InPath q (485 : Vertex)) else decide (InPath q (491 : Vertex)))) else (if i < 99 then (if i < 98 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))) else (if i < 100 then decide (InPath q (496 : Vertex)) else decide (InPath q (497 : Vertex))))) else (if i < 104 then (if i < 102 then decide (InPath q (498 : Vertex)) else (if i < 103 then decide (InPath q (499 : Vertex)) else decide (InPath q (502 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (504 : Vertex)) else decide (InPath q (508 : Vertex))) else (if i < 107 then decide (InPath q (509 : Vertex)) else decide (InPath q (510 : Vertex))))))))) else (if i < 162 then (if i < 135 then (if i < 121 then (if i < 114 then (if i < 111 then (if i < 109 then decide (InPath q (511 : Vertex)) else (if i < 110 then decide (BallClauseLogic.Endpoint q (34 : Vertex)) else decide (BallClauseLogic.Endpoint q (35 : Vertex)))) else (if i < 112 then decide (BallClauseLogic.Endpoint q (36 : Vertex)) else (if i < 113 then decide (BallClauseLogic.Endpoint q (37 : Vertex)) else decide (BallClauseLogic.Endpoint q (42 : Vertex))))) else (if i < 117 then (if i < 115 then decide (BallClauseLogic.Endpoint q (43 : Vertex)) else (if i < 116 then decide (BallClauseLogic.Endpoint q (44 : Vertex)) else decide (BallClauseLogic.Endpoint q (46 : Vertex)))) else (if i < 119 then (if i < 118 then decide (BallClauseLogic.Endpoint q (48 : Vertex)) else decide (BallClauseLogic.Endpoint q (52 : Vertex))) else (if i < 120 then decide (BallClauseLogic.Endpoint q (53 : Vertex)) else decide (BallClauseLogic.Endpoint q (55 : Vertex)))))) else (if i < 128 then (if i < 124 then (if i < 122 then decide (BallClauseLogic.Endpoint q (56 : Vertex)) else (if i < 123 then decide (BallClauseLogic.Endpoint q (57 : Vertex)) else decide (BallClauseLogic.Endpoint q (59 : Vertex)))) else (if i < 126 then (if i < 125 then decide (BallClauseLogic.Endpoint q (63 : Vertex)) else decide (BallClauseLogic.Endpoint q (80 : Vertex))) else (if i < 127 then decide (BallClauseLogic.Endpoint q (96 : Vertex)) else decide (BallClauseLogic.Endpoint q (98 : Vertex))))) else (if i < 131 then (if i < 129 then decide (BallClauseLogic.Endpoint q (99 : Vertex)) else (if i < 130 then decide (BallClauseLogic.Endpoint q (112 : Vertex)) else decide (BallClauseLogic.Endpoint q (113 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (114 : Vertex)) else decide (BallClauseLogic.Endpoint q (115 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (118 : Vertex)) else decide (BallClauseLogic.Endpoint q (120 : Vertex))))))) else (if i < 148 then (if i < 141 then (if i < 138 then (if i < 136 then decide (BallClauseLogic.Endpoint q (124 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (126 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex)))) else (if i < 139 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else (if i < 140 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else decide (BallClauseLogic.Endpoint q (133 : Vertex))))) else (if i < 144 then (if i < 142 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else (if i < 143 then decide (BallClauseLogic.Endpoint q (139 : Vertex)) else decide (BallClauseLogic.Endpoint q (140 : Vertex)))) else (if i < 146 then (if i < 145 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (144 : Vertex))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (149 : Vertex)))))) else (if i < 155 then (if i < 151 then (if i < 149 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else (if i < 150 then decide (BallClauseLogic.Endpoint q (152 : Vertex)) else decide (BallClauseLogic.Endpoint q (153 : Vertex)))) else (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex))))) else (if i < 158 then (if i < 156 then decide (BallClauseLogic.Endpoint q (228 : Vertex)) else (if i < 157 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (234 : Vertex)))) else (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (235 : Vertex)) else decide (BallClauseLogic.Endpoint q (236 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else decide (BallClauseLogic.Endpoint q (240 : Vertex)))))))) else (if i < 189 then (if i < 175 then (if i < 168 then (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (244 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (247 : Vertex)))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (249 : Vertex)) else decide (BallClauseLogic.Endpoint q (251 : Vertex))))) else (if i < 171 then (if i < 169 then decide (BallClauseLogic.Endpoint q (255 : Vertex)) else (if i < 170 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else decide (BallClauseLogic.Endpoint q (259 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (260 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex)))))) else (if i < 182 then (if i < 178 then (if i < 176 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else decide (BallClauseLogic.Endpoint q (279 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else decide (BallClauseLogic.Endpoint q (281 : Vertex))))) else (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex)))) else (if i < 187 then (if i < 186 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex))) else (if i < 188 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (403 : Vertex))))))) else (if i < 203 then (if i < 196 then (if i < 192 then (if i < 190 then decide (BallClauseLogic.Endpoint q (419 : Vertex)) else (if i < 191 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex)))) else (if i < 194 then (if i < 193 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else decide (BallClauseLogic.Endpoint q (436 : Vertex))) else (if i < 195 then decide (BallClauseLogic.Endpoint q (437 : Vertex)) else decide (BallClauseLogic.Endpoint q (439 : Vertex))))) else (if i < 199 then (if i < 197 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else (if i < 198 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex)))) else (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (482 : Vertex)) else decide (BallClauseLogic.Endpoint q (483 : Vertex)))))) else (if i < 210 then (if i < 206 then (if i < 204 then decide (BallClauseLogic.Endpoint q (485 : Vertex)) else (if i < 205 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex)))) else (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (496 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))))) else (if i < 213 then (if i < 211 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else (if i < 212 then decide (BallClauseLogic.Endpoint q (502 : Vertex)) else decide (BallClauseLogic.Endpoint q (504 : Vertex)))) else (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (508 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (510 : Vertex)) else decide (BallClauseLogic.Endpoint q (511 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count217 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count219 (b : Nat → Bool) : Nat := countLit b [109, 110, 111]
def count221 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count223 (b : Nat → Bool) : Nat := countLit b [112, 113, 114]
def count225 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114]
def count227 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [115, 116, 117]
def count231 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count235 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121]
def count237 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121]
def count239 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121]
def count241 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count283 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145, 146, 147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count309 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162]
def count313 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162]
def count321 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [169, 170, 171, 172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]
def count345 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189]
def count367 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]
def count371 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]
def count373 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count375 (b : Nat → Bool) : Nat := countLit b [190, 191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [193, 194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count391 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202]
def count393 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199, 200, 201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202]
def count397 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count399 (b : Nat → Bool) : Nat := countLit b [203, 204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count403 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count405 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206, 207, 208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count411 (b : Nat → Bool) : Nat := countLit b [210, 211, 212]
def count413 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count415 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count417 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216]
def count419 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213, 214, 215, 216]
def count421 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]
def count425 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]
def count427 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]
def count429 (b : Nat → Bool) : Nat := countLit b [3, 6]
def count431 (b : Nat → Bool) : Nat := countLit b [1, 3, 6]
def count434 (b : Nat → Bool) : Nat := countLit b [9, 11]
def count436 (b : Nat → Bool) : Nat := countLit b [8, 9, 11]
def count439 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 11]
def count445 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count447 (b : Nat → Bool) : Nat := countLit b [14, 16, 17]
def count450 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count452 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count454 (b : Nat → Bool) : Nat := countLit b [18, 20, 22, 23]
def count458 (b : Nat → Bool) : Nat := countLit b [14, 16, 17, 18, 20, 22, 23]
def count465 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 11, 14, 16, 17, 18, 20, 22, 23]
def count478 (b : Nat → Bool) : Nat := countLit b [28, 29]
def count480 (b : Nat → Bool) : Nat := countLit b [26, 28, 29]
def count483 (b : Nat → Bool) : Nat := countLit b [31, 34]
def count485 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count487 (b : Nat → Bool) : Nat := countLit b [31, 34, 36, 37]
def count491 (b : Nat → Bool) : Nat := countLit b [26, 28, 29, 31, 34, 36, 37]
def count498 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count500 (b : Nat → Bool) : Nat := countLit b [39, 42, 44]
def count503 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count505 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count507 (b : Nat → Bool) : Nat := countLit b [45, 47, 50, 52]
def count511 (b : Nat → Bool) : Nat := countLit b [39, 42, 44, 45, 47, 50, 52]
def count518 (b : Nat → Bool) : Nat := countLit b [26, 28, 29, 31, 34, 36, 37, 39, 42, 44, 45, 47, 50, 52]
def count532 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 11, 14, 16, 17, 18, 20, 22, 23, 26, 28, 29, 31, 34, 36, 37, 39, 42, 44, 45, 47, 50, 52]
def count559 (b : Nat → Bool) : Nat := countLit b [55, 58]
def count561 (b : Nat → Bool) : Nat := countLit b [53, 55, 58]
def count564 (b : Nat → Bool) : Nat := countLit b [60, 61]
def count566 (b : Nat → Bool) : Nat := countLit b [63, 67]
def count568 (b : Nat → Bool) : Nat := countLit b [60, 61, 63, 67]
def count572 (b : Nat → Bool) : Nat := countLit b [53, 55, 58, 60, 61, 63, 67]
def count579 (b : Nat → Bool) : Nat := countLit b [70, 73]
def count581 (b : Nat → Bool) : Nat := countLit b [68, 70, 73]
def count584 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count586 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count588 (b : Nat → Bool) : Nat := countLit b [75, 76, 77, 79]
def count592 (b : Nat → Bool) : Nat := countLit b [68, 70, 73, 75, 76, 77, 79]
def count599 (b : Nat → Bool) : Nat := countLit b [53, 55, 58, 60, 61, 63, 67, 68, 70, 73, 75, 76, 77, 79]
def count613 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count615 (b : Nat → Bool) : Nat := countLit b [83, 84, 86]
def count618 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count620 (b : Nat → Bool) : Nat := countLit b [91, 94]
def count622 (b : Nat → Bool) : Nat := countLit b [88, 90, 91, 94]
def count626 (b : Nat → Bool) : Nat := countLit b [83, 84, 86, 88, 90, 91, 94]
def count633 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count635 (b : Nat → Bool) : Nat := countLit b [95, 98, 100]
def count638 (b : Nat → Bool) : Nat := countLit b [101, 104]
def count640 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count642 (b : Nat → Bool) : Nat := countLit b [101, 104, 106, 107]
def count646 (b : Nat → Bool) : Nat := countLit b [95, 98, 100, 101, 104, 106, 107]
def count653 (b : Nat → Bool) : Nat := countLit b [83, 84, 86, 88, 90, 91, 94, 95, 98, 100, 101, 104, 106, 107]
def count667 (b : Nat → Bool) : Nat := countLit b [53, 55, 58, 60, 61, 63, 67, 68, 70, 73, 75, 76, 77, 79, 83, 84, 86, 88, 90, 91, 94, 95, 98, 100, 101, 104, 106, 107]
def count695 (b : Nat → Bool) : Nat := countLit b [1, 3, 6, 8, 9, 11, 14, 16, 17, 18, 20, 22, 23, 26, 28, 29, 31, 34, 36, 37, 39, 42, 44, 45, 47, 50, 52, 53, 55, 58, 60, 61, 63, 67, 68, 70, 73, 75, 76, 77, 79, 83, 84, 86, 88, 90, 91, 94, 95, 98, 100, 101, 104, 106, 107]
def count737 (b : Nat → Bool) : Nat := countLit b [-3, -6]
def count739 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6]
def count742 (b : Nat → Bool) : Nat := countLit b [-9, -11]
def count744 (b : Nat → Bool) : Nat := countLit b [-8, -9, -11]
def count747 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -11]
def count753 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count755 (b : Nat → Bool) : Nat := countLit b [-14, -16, -17]
def count758 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count760 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count762 (b : Nat → Bool) : Nat := countLit b [-18, -20, -22, -23]
def count766 (b : Nat → Bool) : Nat := countLit b [-14, -16, -17, -18, -20, -22, -23]
def count773 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -11, -14, -16, -17, -18, -20, -22, -23]
def count786 (b : Nat → Bool) : Nat := countLit b [-28, -29]
def count788 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29]
def count791 (b : Nat → Bool) : Nat := countLit b [-31, -34]
def count793 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count795 (b : Nat → Bool) : Nat := countLit b [-31, -34, -36, -37]
def count799 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29, -31, -34, -36, -37]
def count806 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count808 (b : Nat → Bool) : Nat := countLit b [-39, -42, -44]
def count811 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count813 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count815 (b : Nat → Bool) : Nat := countLit b [-45, -47, -50, -52]
def count819 (b : Nat → Bool) : Nat := countLit b [-39, -42, -44, -45, -47, -50, -52]
def count826 (b : Nat → Bool) : Nat := countLit b [-26, -28, -29, -31, -34, -36, -37, -39, -42, -44, -45, -47, -50, -52]
def count840 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -11, -14, -16, -17, -18, -20, -22, -23, -26, -28, -29, -31, -34, -36, -37, -39, -42, -44, -45, -47, -50, -52]
def count855 (b : Nat → Bool) : Nat := countLit b [-55, -58]
def count857 (b : Nat → Bool) : Nat := countLit b [-53, -55, -58]
def count860 (b : Nat → Bool) : Nat := countLit b [-60, -61]
def count862 (b : Nat → Bool) : Nat := countLit b [-63, -67]
def count864 (b : Nat → Bool) : Nat := countLit b [-60, -61, -63, -67]
def count868 (b : Nat → Bool) : Nat := countLit b [-53, -55, -58, -60, -61, -63, -67]
def count875 (b : Nat → Bool) : Nat := countLit b [-70, -73]
def count877 (b : Nat → Bool) : Nat := countLit b [-68, -70, -73]
def count880 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count882 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count884 (b : Nat → Bool) : Nat := countLit b [-75, -76, -77, -79]
def count888 (b : Nat → Bool) : Nat := countLit b [-68, -70, -73, -75, -76, -77, -79]
def count895 (b : Nat → Bool) : Nat := countLit b [-53, -55, -58, -60, -61, -63, -67, -68, -70, -73, -75, -76, -77, -79]
def count909 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count911 (b : Nat → Bool) : Nat := countLit b [-83, -84, -86]
def count914 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count916 (b : Nat → Bool) : Nat := countLit b [-91, -94]
def count918 (b : Nat → Bool) : Nat := countLit b [-88, -90, -91, -94]
def count922 (b : Nat → Bool) : Nat := countLit b [-83, -84, -86, -88, -90, -91, -94]
def count929 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count931 (b : Nat → Bool) : Nat := countLit b [-95, -98, -100]
def count934 (b : Nat → Bool) : Nat := countLit b [-101, -104]
def count936 (b : Nat → Bool) : Nat := countLit b [-106, -107]
def count938 (b : Nat → Bool) : Nat := countLit b [-101, -104, -106, -107]
def count942 (b : Nat → Bool) : Nat := countLit b [-95, -98, -100, -101, -104, -106, -107]
def count949 (b : Nat → Bool) : Nat := countLit b [-83, -84, -86, -88, -90, -91, -94, -95, -98, -100, -101, -104, -106, -107]
def count963 (b : Nat → Bool) : Nat := countLit b [-53, -55, -58, -60, -61, -63, -67, -68, -70, -73, -75, -76, -77, -79, -83, -84, -86, -88, -90, -91, -94, -95, -98, -100, -101, -104, -106, -107]
def count978 (b : Nat → Bool) : Nat := countLit b [-1, -3, -6, -8, -9, -11, -14, -16, -17, -18, -20, -22, -23, -26, -28, -29, -31, -34, -36, -37, -39, -42, -44, -45, -47, -50, -52, -53, -55, -58, -60, -61, -63, -67, -68, -70, -73, -75, -76, -77, -79, -83, -84, -86, -88, -90, -91, -94, -95, -98, -100, -101, -104, -106, -107]
def count993 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count995 (b : Nat → Bool) : Nat := countLit b [2, 4, 5]
def count998 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count1000 (b : Nat → Bool) : Nat := countLit b [7, 10, 12]
def count1003 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 10, 12]
def count1009 (b : Nat → Bool) : Nat := countLit b [15, 19]
def count1011 (b : Nat → Bool) : Nat := countLit b [13, 15, 19]
def count1014 (b : Nat → Bool) : Nat := countLit b [21, 24]
def count1016 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count1018 (b : Nat → Bool) : Nat := countLit b [21, 24, 25, 27]
def count1022 (b : Nat → Bool) : Nat := countLit b [13, 15, 19, 21, 24, 25, 27]
def count1029 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 10, 12, 13, 15, 19, 21, 24, 25, 27]
def count1042 (b : Nat → Bool) : Nat := countLit b [32, 33]
def count1044 (b : Nat → Bool) : Nat := countLit b [30, 32, 33]
def count1047 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count1049 (b : Nat → Bool) : Nat := countLit b [35, 38, 40]
def count1052 (b : Nat → Bool) : Nat := countLit b [30, 32, 33, 35, 38, 40]
def count1058 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count1060 (b : Nat → Bool) : Nat := countLit b [41, 43, 46]
def count1063 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count1065 (b : Nat → Bool) : Nat := countLit b [51, 54]
def count1067 (b : Nat → Bool) : Nat := countLit b [48, 49, 51, 54]
def count1071 (b : Nat → Bool) : Nat := countLit b [41, 43, 46, 48, 49, 51, 54]
def count1078 (b : Nat → Bool) : Nat := countLit b [30, 32, 33, 35, 38, 40, 41, 43, 46, 48, 49, 51, 54]
def count1091 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 10, 12, 13, 15, 19, 21, 24, 25, 27, 30, 32, 33, 35, 38, 40, 41, 43, 46, 48, 49, 51, 54]
def count1117 (b : Nat → Bool) : Nat := countLit b [57, 59]
def count1119 (b : Nat → Bool) : Nat := countLit b [56, 57, 59]
def count1122 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count1124 (b : Nat → Bool) : Nat := countLit b [62, 64, 65]
def count1127 (b : Nat → Bool) : Nat := countLit b [56, 57, 59, 62, 64, 65]
def count1133 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count1135 (b : Nat → Bool) : Nat := countLit b [66, 69, 71]
def count1138 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count1140 (b : Nat → Bool) : Nat := countLit b [78, 80]
def count1142 (b : Nat → Bool) : Nat := countLit b [72, 74, 78, 80]
def count1146 (b : Nat → Bool) : Nat := countLit b [66, 69, 71, 72, 74, 78, 80]
def count1153 (b : Nat → Bool) : Nat := countLit b [56, 57, 59, 62, 64, 65, 66, 69, 71, 72, 74, 78, 80]
def count1166 (b : Nat → Bool) : Nat := countLit b [82, 85]
def count1168 (b : Nat → Bool) : Nat := countLit b [81, 82, 85]
def count1171 (b : Nat → Bool) : Nat := countLit b [87, 89]
def count1173 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count1175 (b : Nat → Bool) : Nat := countLit b [87, 89, 92, 93]
def count1179 (b : Nat → Bool) : Nat := countLit b [81, 82, 85, 87, 89, 92, 93]
def count1186 (b : Nat → Bool) : Nat := countLit b [97, 99]
def count1188 (b : Nat → Bool) : Nat := countLit b [96, 97, 99]
def count1191 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count1193 (b : Nat → Bool) : Nat := countLit b [105, 108]
def count1195 (b : Nat → Bool) : Nat := countLit b [102, 103, 105, 108]
def count1199 (b : Nat → Bool) : Nat := countLit b [96, 97, 99, 102, 103, 105, 108]
def count1206 (b : Nat → Bool) : Nat := countLit b [81, 82, 85, 87, 89, 92, 93, 96, 97, 99, 102, 103, 105, 108]
def count1220 (b : Nat → Bool) : Nat := countLit b [56, 57, 59, 62, 64, 65, 66, 69, 71, 72, 74, 78, 80, 81, 82, 85, 87, 89, 92, 93, 96, 97, 99, 102, 103, 105, 108]
def count1247 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 7, 10, 12, 13, 15, 19, 21, 24, 25, 27, 30, 32, 33, 35, 38, 40, 41, 43, 46, 48, 49, 51, 54, 56, 57, 59, 62, 64, 65, 66, 69, 71, 72, 74, 78, 80, 81, 82, 85, 87, 89, 92, 93, 96, 97, 99, 102, 103, 105, 108]
def count1289 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1291 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5]
def count1294 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count1296 (b : Nat → Bool) : Nat := countLit b [-7, -10, -12]
def count1299 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -10, -12]
def count1305 (b : Nat → Bool) : Nat := countLit b [-15, -19]
def count1307 (b : Nat → Bool) : Nat := countLit b [-13, -15, -19]
def count1310 (b : Nat → Bool) : Nat := countLit b [-21, -24]
def count1312 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count1314 (b : Nat → Bool) : Nat := countLit b [-21, -24, -25, -27]
def count1318 (b : Nat → Bool) : Nat := countLit b [-13, -15, -19, -21, -24, -25, -27]
def count1325 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27]
def count1338 (b : Nat → Bool) : Nat := countLit b [-32, -33]
def count1340 (b : Nat → Bool) : Nat := countLit b [-30, -32, -33]
def count1343 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1345 (b : Nat → Bool) : Nat := countLit b [-35, -38, -40]
def count1348 (b : Nat → Bool) : Nat := countLit b [-30, -32, -33, -35, -38, -40]
def count1354 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count1356 (b : Nat → Bool) : Nat := countLit b [-41, -43, -46]
def count1359 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count1361 (b : Nat → Bool) : Nat := countLit b [-51, -54]
def count1363 (b : Nat → Bool) : Nat := countLit b [-48, -49, -51, -54]
def count1367 (b : Nat → Bool) : Nat := countLit b [-41, -43, -46, -48, -49, -51, -54]
def count1374 (b : Nat → Bool) : Nat := countLit b [-30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]
def count1387 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54]
def count1400 (b : Nat → Bool) : Nat := countLit b [-57, -59]
def count1402 (b : Nat → Bool) : Nat := countLit b [-56, -57, -59]
def count1405 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count1407 (b : Nat → Bool) : Nat := countLit b [-62, -64, -65]
def count1410 (b : Nat → Bool) : Nat := countLit b [-56, -57, -59, -62, -64, -65]
def count1416 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count1418 (b : Nat → Bool) : Nat := countLit b [-66, -69, -71]
def count1421 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count1423 (b : Nat → Bool) : Nat := countLit b [-78, -80]
def count1425 (b : Nat → Bool) : Nat := countLit b [-72, -74, -78, -80]
def count1429 (b : Nat → Bool) : Nat := countLit b [-66, -69, -71, -72, -74, -78, -80]
def count1436 (b : Nat → Bool) : Nat := countLit b [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80]
def count1449 (b : Nat → Bool) : Nat := countLit b [-82, -85]
def count1451 (b : Nat → Bool) : Nat := countLit b [-81, -82, -85]
def count1454 (b : Nat → Bool) : Nat := countLit b [-87, -89]
def count1456 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1458 (b : Nat → Bool) : Nat := countLit b [-87, -89, -92, -93]
def count1462 (b : Nat → Bool) : Nat := countLit b [-81, -82, -85, -87, -89, -92, -93]
def count1469 (b : Nat → Bool) : Nat := countLit b [-97, -99]
def count1471 (b : Nat → Bool) : Nat := countLit b [-96, -97, -99]
def count1474 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1476 (b : Nat → Bool) : Nat := countLit b [-105, -108]
def count1478 (b : Nat → Bool) : Nat := countLit b [-102, -103, -105, -108]
def count1482 (b : Nat → Bool) : Nat := countLit b [-96, -97, -99, -102, -103, -105, -108]
def count1489 (b : Nat → Bool) : Nat := countLit b [-81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]
def count1502 (b : Nat → Bool) : Nat := countLit b [-56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]
def count1515 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -7, -10, -12, -13, -15, -19, -21, -24, -25, -27, -30, -32, -33, -35, -38, -40, -41, -43, -46, -48, -49, -51, -54, -56, -57, -59, -62, -64, -65, -66, -69, -71, -72, -74, -78, -80, -81, -82, -85, -87, -89, -92, -93, -96, -97, -99, -102, -103, -105, -108]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 764 then (if i < 382 then (if i < 191 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 17 then (if i < 14 then (if i < 12 then b 11 else (if i < 13 then b 12 else b 13)) else (if i < 15 then b 14 else (if i < 16 then b 15 else b 16))) else (if i < 20 then (if i < 18 then b 17 else (if i < 19 then b 18 else b 19)) else (if i < 21 then b 20 else (if i < 22 then b 21 else b 22))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then b 23 else (if i < 25 then b 24 else b 25)) else (if i < 27 then b 26 else (if i < 28 then b 27 else b 28))) else (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)))) else (if i < 41 then (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 39 then b 38 else (if i < 40 then b 39 else b 40))) else (if i < 44 then (if i < 42 then b 41 else (if i < 43 then b 42 else b 43)) else (if i < 45 then b 44 else (if i < 46 then b 45 else b 46)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then b 47 else (if i < 49 then b 48 else b 49)) else (if i < 51 then b 50 else (if i < 52 then b 51 else b 52))) else (if i < 56 then (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)) else (if i < 57 then b 56 else (if i < 58 then b 57 else b 58)))) else (if i < 65 then (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 63 then b 62 else (if i < 64 then b 63 else b 64))) else (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 69 then b 68 else (if i < 70 then b 69 else b 70))))) else (if i < 83 then (if i < 77 then (if i < 74 then (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)) else (if i < 75 then b 74 else (if i < 76 then b 75 else b 76))) else (if i < 80 then (if i < 78 then b 77 else (if i < 79 then b 78 else b 79)) else (if i < 81 then b 80 else (if i < 82 then b 81 else b 82)))) else (if i < 89 then (if i < 86 then (if i < 84 then b 83 else (if i < 85 then b 84 else b 85)) else (if i < 87 then b 86 else (if i < 88 then b 87 else b 88))) else (if i < 92 then (if i < 90 then b 89 else (if i < 91 then b 90 else b 91)) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))))))) else (if i < 143 then (if i < 119 then (if i < 107 then (if i < 101 then (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 99 then b 98 else (if i < 100 then b 99 else b 100))) else (if i < 104 then (if i < 102 then b 101 else (if i < 103 then b 102 else b 103)) else (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)))) else (if i < 113 then (if i < 110 then (if i < 108 then b 107 else (if i < 109 then b 108 else b 109)) else (if i < 111 then b 110 else (if i < 112 then b 111 else b 112))) else (if i < 116 then (if i < 114 then b 113 else (if i < 115 then b 114 else b 115)) else (if i < 117 then b 116 else (if i < 118 then b 117 else b 118))))) else (if i < 131 then (if i < 125 then (if i < 122 then (if i < 120 then b 119 else (if i < 121 then b 120 else b 121)) else (if i < 123 then b 122 else (if i < 124 then b 123 else b 124))) else (if i < 128 then (if i < 126 then b 125 else (if i < 127 then b 126 else b 127)) else (if i < 129 then b 128 else (if i < 130 then b 129 else b 130)))) else (if i < 137 then (if i < 134 then (if i < 132 then b 131 else (if i < 133 then b 132 else b 133)) else (if i < 135 then b 134 else (if i < 136 then b 135 else b 136))) else (if i < 140 then (if i < 138 then b 137 else (if i < 139 then b 138 else b 139)) else (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)))))) else (if i < 167 then (if i < 155 then (if i < 149 then (if i < 146 then (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)) else (if i < 147 then b 146 else (if i < 148 then b 147 else b 148))) else (if i < 152 then (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)) else (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)))) else (if i < 161 then (if i < 158 then (if i < 156 then b 155 else (if i < 157 then b 156 else b 157)) else (if i < 159 then b 158 else (if i < 160 then b 159 else b 160))) else (if i < 164 then (if i < 162 then b 161 else (if i < 163 then b 162 else b 163)) else (if i < 165 then b 164 else (if i < 166 then b 165 else b 166))))) else (if i < 179 then (if i < 173 then (if i < 170 then (if i < 168 then b 167 else (if i < 169 then b 168 else b 169)) else (if i < 171 then b 170 else (if i < 172 then b 171 else b 172))) else (if i < 176 then (if i < 174 then b 173 else (if i < 175 then b 174 else b 175)) else (if i < 177 then b 176 else (if i < 178 then b 177 else b 178)))) else (if i < 185 then (if i < 182 then (if i < 180 then b 179 else (if i < 181 then b 180 else b 181)) else (if i < 183 then b 182 else (if i < 184 then b 183 else b 184))) else (if i < 188 then (if i < 186 then b 185 else (if i < 187 then b 186 else b 187)) else (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)))))))) else (if i < 286 then (if i < 238 then (if i < 214 then (if i < 202 then (if i < 196 then (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else (if i < 195 then b 194 else b 195))) else (if i < 199 then (if i < 197 then b 196 else (if i < 198 then b 197 else b 198)) else (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)))) else (if i < 208 then (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 206 then b 205 else (if i < 207 then b 206 else b 207))) else (if i < 211 then (if i < 209 then b 208 else (if i < 210 then b 209 else b 210)) else (if i < 212 then b 211 else (if i < 213 then b 212 else b 213))))) else (if i < 226 then (if i < 220 then (if i < 217 then (if i < 215 then b 214 else (if i < 216 then b 215 else b 216)) else (if i < 218 then decide (1 ≤ count217 b) else (if i < 219 then decide (2 ≤ count217 b) else decide (1 ≤ count219 b)))) else (if i < 223 then (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b))) else (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b))))) else (if i < 232 then (if i < 229 then (if i < 227 then decide (2 ≤ count225 b) else (if i < 228 then decide (1 ≤ count227 b) else decide (2 ≤ count227 b))) else (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b)))) else (if i < 235 then (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b))) else (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))))))) else (if i < 262 then (if i < 250 then (if i < 244 then (if i < 241 then (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b))) else (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b)))) else (if i < 247 then (if i < 245 then decide (2 ≤ count243 b) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b))) else (if i < 248 then decide (1 ≤ count247 b) else (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b))))) else (if i < 256 then (if i < 253 then (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b))) else (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b)))) else (if i < 259 then (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))) else (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))))) else (if i < 274 then (if i < 268 then (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)))) else (if i < 271 then (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b))) else (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))))) else (if i < 280 then (if i < 277 then (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))) else (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)))) else (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)))))))) else (if i < 334 then (if i < 310 then (if i < 298 then (if i < 292 then (if i < 289 then (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))) else (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)))) else (if i < 295 then (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))) else (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))))) else (if i < 304 then (if i < 301 then (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))) else (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)))) else (if i < 307 then (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))) else (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)))))) else (if i < 322 then (if i < 316 then (if i < 313 then (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))) else (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)))) else (if i < 319 then (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))) else (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))))) else (if i < 328 then (if i < 325 then (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))) else (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b)))) else (if i < 331 then (if i < 329 then decide (2 ≤ count327 b) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b))) else (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b))))))) else (if i < 358 then (if i < 346 then (if i < 340 then (if i < 337 then (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b))) else (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)))) else (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))))) else (if i < 352 then (if i < 349 then (if i < 347 then decide (2 ≤ count345 b) else (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b))) else (if i < 350 then decide (1 ≤ count349 b) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)))) else (if i < 355 then (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b))) else (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b)))))) else (if i < 370 then (if i < 364 then (if i < 361 then (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))) else (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)))) else (if i < 367 then (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))) else (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))))) else (if i < 376 then (if i < 373 then (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))) else (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)))) else (if i < 379 then (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b))) else (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b)))))))))) else (if i < 573 then (if i < 477 then (if i < 429 then (if i < 405 then (if i < 393 then (if i < 387 then (if i < 384 then (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)) else (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)))) else (if i < 390 then (if i < 388 then decide (1 ≤ count387 b) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b))) else (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))))) else (if i < 399 then (if i < 396 then (if i < 394 then decide (1 ≤ count393 b) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))) else (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b)))) else (if i < 402 then (if i < 400 then decide (1 ≤ count399 b) else (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b))) else (if i < 403 then decide (2 ≤ count401 b) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b)))))) else (if i < 417 then (if i < 411 then (if i < 408 then (if i < 406 then decide (1 ≤ count405 b) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))) else (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b)))) else (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 415 then decide (2 ≤ count413 b) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b))))) else (if i < 423 then (if i < 420 then (if i < 418 then decide (1 ≤ count417 b) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b))) else (if i < 421 then decide (2 ≤ count419 b) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b)))) else (if i < 426 then (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b))) else (if i < 427 then decide (2 ≤ count425 b) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b))))))) else (if i < 453 then (if i < 441 then (if i < 435 then (if i < 432 then (if i < 430 then decide (1 ≤ count429 b) else (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b))) else (if i < 433 then decide (2 ≤ count431 b) else (if i < 434 then decide (3 ≤ count431 b) else decide (1 ≤ count434 b)))) else (if i < 438 then (if i < 436 then decide (2 ≤ count434 b) else (if i < 437 then decide (1 ≤ count436 b) else decide (2 ≤ count436 b))) else (if i < 439 then decide (3 ≤ count436 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b))))) else (if i < 447 then (if i < 444 then (if i < 442 then decide (3 ≤ count439 b) else (if i < 443 then decide (4 ≤ count439 b) else decide (5 ≤ count439 b))) else (if i < 445 then decide (6 ≤ count439 b) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b)))) else (if i < 450 then (if i < 448 then decide (1 ≤ count447 b) else (if i < 449 then decide (2 ≤ count447 b) else decide (3 ≤ count447 b))) else (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (1 ≤ count452 b)))))) else (if i < 465 then (if i < 459 then (if i < 456 then (if i < 454 then decide (2 ≤ count452 b) else (if i < 455 then decide (1 ≤ count454 b) else decide (2 ≤ count454 b))) else (if i < 457 then decide (3 ≤ count454 b) else (if i < 458 then decide (4 ≤ count454 b) else decide (1 ≤ count458 b)))) else (if i < 462 then (if i < 460 then decide (2 ≤ count458 b) else (if i < 461 then decide (3 ≤ count458 b) else decide (4 ≤ count458 b))) else (if i < 463 then decide (5 ≤ count458 b) else (if i < 464 then decide (6 ≤ count458 b) else decide (7 ≤ count458 b))))) else (if i < 471 then (if i < 468 then (if i < 466 then decide (1 ≤ count465 b) else (if i < 467 then decide (2 ≤ count465 b) else decide (3 ≤ count465 b))) else (if i < 469 then decide (4 ≤ count465 b) else (if i < 470 then decide (5 ≤ count465 b) else decide (6 ≤ count465 b)))) else (if i < 474 then (if i < 472 then decide (7 ≤ count465 b) else (if i < 473 then decide (8 ≤ count465 b) else decide (9 ≤ count465 b))) else (if i < 475 then decide (10 ≤ count465 b) else (if i < 476 then decide (11 ≤ count465 b) else decide (12 ≤ count465 b)))))))) else (if i < 525 then (if i < 501 then (if i < 489 then (if i < 483 then (if i < 480 then (if i < 478 then decide (13 ≤ count465 b) else (if i < 479 then decide (1 ≤ count478 b) else decide (2 ≤ count478 b))) else (if i < 481 then decide (1 ≤ count480 b) else (if i < 482 then decide (2 ≤ count480 b) else decide (3 ≤ count480 b)))) else (if i < 486 then (if i < 484 then decide (1 ≤ count483 b) else (if i < 485 then decide (2 ≤ count483 b) else decide (1 ≤ count485 b))) else (if i < 487 then decide (2 ≤ count485 b) else (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b))))) else (if i < 495 then (if i < 492 then (if i < 490 then decide (3 ≤ count487 b) else (if i < 491 then decide (4 ≤ count487 b) else decide (1 ≤ count491 b))) else (if i < 493 then decide (2 ≤ count491 b) else (if i < 494 then decide (3 ≤ count491 b) else decide (4 ≤ count491 b)))) else (if i < 498 then (if i < 496 then decide (5 ≤ count491 b) else (if i < 497 then decide (6 ≤ count491 b) else decide (7 ≤ count491 b))) else (if i < 499 then decide (1 ≤ count498 b) else (if i < 500 then decide (2 ≤ count498 b) else decide (1 ≤ count500 b)))))) else (if i < 513 then (if i < 507 then (if i < 504 then (if i < 502 then decide (2 ≤ count500 b) else (if i < 503 then decide (3 ≤ count500 b) else decide (1 ≤ count503 b))) else (if i < 505 then decide (2 ≤ count503 b) else (if i < 506 then decide (1 ≤ count505 b) else decide (2 ≤ count505 b)))) else (if i < 510 then (if i < 508 then decide (1 ≤ count507 b) else (if i < 509 then decide (2 ≤ count507 b) else decide (3 ≤ count507 b))) else (if i < 511 then decide (4 ≤ count507 b) else (if i < 512 then decide (1 ≤ count511 b) else decide (2 ≤ count511 b))))) else (if i < 519 then (if i < 516 then (if i < 514 then decide (3 ≤ count511 b) else (if i < 515 then decide (4 ≤ count511 b) else decide (5 ≤ count511 b))) else (if i < 517 then decide (6 ≤ count511 b) else (if i < 518 then decide (7 ≤ count511 b) else decide (1 ≤ count518 b)))) else (if i < 522 then (if i < 520 then decide (2 ≤ count518 b) else (if i < 521 then decide (3 ≤ count518 b) else decide (4 ≤ count518 b))) else (if i < 523 then decide (5 ≤ count518 b) else (if i < 524 then decide (6 ≤ count518 b) else decide (7 ≤ count518 b))))))) else (if i < 549 then (if i < 537 then (if i < 531 then (if i < 528 then (if i < 526 then decide (8 ≤ count518 b) else (if i < 527 then decide (9 ≤ count518 b) else decide (10 ≤ count518 b))) else (if i < 529 then decide (11 ≤ count518 b) else (if i < 530 then decide (12 ≤ count518 b) else decide (13 ≤ count518 b)))) else (if i < 534 then (if i < 532 then decide (14 ≤ count518 b) else (if i < 533 then decide (1 ≤ count532 b) else decide (2 ≤ count532 b))) else (if i < 535 then decide (3 ≤ count532 b) else (if i < 536 then decide (4 ≤ count532 b) else decide (5 ≤ count532 b))))) else (if i < 543 then (if i < 540 then (if i < 538 then decide (6 ≤ count532 b) else (if i < 539 then decide (7 ≤ count532 b) else decide (8 ≤ count532 b))) else (if i < 541 then decide (9 ≤ count532 b) else (if i < 542 then decide (10 ≤ count532 b) else decide (11 ≤ count532 b)))) else (if i < 546 then (if i < 544 then decide (12 ≤ count532 b) else (if i < 545 then decide (13 ≤ count532 b) else decide (14 ≤ count532 b))) else (if i < 547 then decide (15 ≤ count532 b) else (if i < 548 then decide (16 ≤ count532 b) else decide (17 ≤ count532 b)))))) else (if i < 561 then (if i < 555 then (if i < 552 then (if i < 550 then decide (18 ≤ count532 b) else (if i < 551 then decide (19 ≤ count532 b) else decide (20 ≤ count532 b))) else (if i < 553 then decide (21 ≤ count532 b) else (if i < 554 then decide (22 ≤ count532 b) else decide (23 ≤ count532 b)))) else (if i < 558 then (if i < 556 then decide (24 ≤ count532 b) else (if i < 557 then decide (25 ≤ count532 b) else decide (26 ≤ count532 b))) else (if i < 559 then decide (27 ≤ count532 b) else (if i < 560 then decide (1 ≤ count559 b) else decide (2 ≤ count559 b))))) else (if i < 567 then (if i < 564 then (if i < 562 then decide (1 ≤ count561 b) else (if i < 563 then decide (2 ≤ count561 b) else decide (3 ≤ count561 b))) else (if i < 565 then decide (1 ≤ count564 b) else (if i < 566 then decide (2 ≤ count564 b) else decide (1 ≤ count566 b)))) else (if i < 570 then (if i < 568 then decide (2 ≤ count566 b) else (if i < 569 then decide (1 ≤ count568 b) else decide (2 ≤ count568 b))) else (if i < 571 then decide (3 ≤ count568 b) else (if i < 572 then decide (4 ≤ count568 b) else decide (1 ≤ count572 b))))))))) else (if i < 668 then (if i < 620 then (if i < 596 then (if i < 584 then (if i < 578 then (if i < 575 then (if i < 574 then decide (2 ≤ count572 b) else decide (3 ≤ count572 b)) else (if i < 576 then decide (4 ≤ count572 b) else (if i < 577 then decide (5 ≤ count572 b) else decide (6 ≤ count572 b)))) else (if i < 581 then (if i < 579 then decide (7 ≤ count572 b) else (if i < 580 then decide (1 ≤ count579 b) else decide (2 ≤ count579 b))) else (if i < 582 then decide (1 ≤ count581 b) else (if i < 583 then decide (2 ≤ count581 b) else decide (3 ≤ count581 b))))) else (if i < 590 then (if i < 587 then (if i < 585 then decide (1 ≤ count584 b) else (if i < 586 then decide (2 ≤ count584 b) else decide (1 ≤ count586 b))) else (if i < 588 then decide (2 ≤ count586 b) else (if i < 589 then decide (1 ≤ count588 b) else decide (2 ≤ count588 b)))) else (if i < 593 then (if i < 591 then decide (3 ≤ count588 b) else (if i < 592 then decide (4 ≤ count588 b) else decide (1 ≤ count592 b))) else (if i < 594 then decide (2 ≤ count592 b) else (if i < 595 then decide (3 ≤ count592 b) else decide (4 ≤ count592 b)))))) else (if i < 608 then (if i < 602 then (if i < 599 then (if i < 597 then decide (5 ≤ count592 b) else (if i < 598 then decide (6 ≤ count592 b) else decide (7 ≤ count592 b))) else (if i < 600 then decide (1 ≤ count599 b) else (if i < 601 then decide (2 ≤ count599 b) else decide (3 ≤ count599 b)))) else (if i < 605 then (if i < 603 then decide (4 ≤ count599 b) else (if i < 604 then decide (5 ≤ count599 b) else decide (6 ≤ count599 b))) else (if i < 606 then decide (7 ≤ count599 b) else (if i < 607 then decide (8 ≤ count599 b) else decide (9 ≤ count599 b))))) else (if i < 614 then (if i < 611 then (if i < 609 then decide (10 ≤ count599 b) else (if i < 610 then decide (11 ≤ count599 b) else decide (12 ≤ count599 b))) else (if i < 612 then decide (13 ≤ count599 b) else (if i < 613 then decide (14 ≤ count599 b) else decide (1 ≤ count613 b)))) else (if i < 617 then (if i < 615 then decide (2 ≤ count613 b) else (if i < 616 then decide (1 ≤ count615 b) else decide (2 ≤ count615 b))) else (if i < 618 then decide (3 ≤ count615 b) else (if i < 619 then decide (1 ≤ count618 b) else decide (2 ≤ count618 b))))))) else (if i < 644 then (if i < 632 then (if i < 626 then (if i < 623 then (if i < 621 then decide (1 ≤ count620 b) else (if i < 622 then decide (2 ≤ count620 b) else decide (1 ≤ count622 b))) else (if i < 624 then decide (2 ≤ count622 b) else (if i < 625 then decide (3 ≤ count622 b) else decide (4 ≤ count622 b)))) else (if i < 629 then (if i < 627 then decide (1 ≤ count626 b) else (if i < 628 then decide (2 ≤ count626 b) else decide (3 ≤ count626 b))) else (if i < 630 then decide (4 ≤ count626 b) else (if i < 631 then decide (5 ≤ count626 b) else decide (6 ≤ count626 b))))) else (if i < 638 then (if i < 635 then (if i < 633 then decide (7 ≤ count626 b) else (if i < 634 then decide (1 ≤ count633 b) else decide (2 ≤ count633 b))) else (if i < 636 then decide (1 ≤ count635 b) else (if i < 637 then decide (2 ≤ count635 b) else decide (3 ≤ count635 b)))) else (if i < 641 then (if i < 639 then decide (1 ≤ count638 b) else (if i < 640 then decide (2 ≤ count638 b) else decide (1 ≤ count640 b))) else (if i < 642 then decide (2 ≤ count640 b) else (if i < 643 then decide (1 ≤ count642 b) else decide (2 ≤ count642 b)))))) else (if i < 656 then (if i < 650 then (if i < 647 then (if i < 645 then decide (3 ≤ count642 b) else (if i < 646 then decide (4 ≤ count642 b) else decide (1 ≤ count646 b))) else (if i < 648 then decide (2 ≤ count646 b) else (if i < 649 then decide (3 ≤ count646 b) else decide (4 ≤ count646 b)))) else (if i < 653 then (if i < 651 then decide (5 ≤ count646 b) else (if i < 652 then decide (6 ≤ count646 b) else decide (7 ≤ count646 b))) else (if i < 654 then decide (1 ≤ count653 b) else (if i < 655 then decide (2 ≤ count653 b) else decide (3 ≤ count653 b))))) else (if i < 662 then (if i < 659 then (if i < 657 then decide (4 ≤ count653 b) else (if i < 658 then decide (5 ≤ count653 b) else decide (6 ≤ count653 b))) else (if i < 660 then decide (7 ≤ count653 b) else (if i < 661 then decide (8 ≤ count653 b) else decide (9 ≤ count653 b)))) else (if i < 665 then (if i < 663 then decide (10 ≤ count653 b) else (if i < 664 then decide (11 ≤ count653 b) else decide (12 ≤ count653 b))) else (if i < 666 then decide (13 ≤ count653 b) else (if i < 667 then decide (14 ≤ count653 b) else decide (1 ≤ count667 b)))))))) else (if i < 716 then (if i < 692 then (if i < 680 then (if i < 674 then (if i < 671 then (if i < 669 then decide (2 ≤ count667 b) else (if i < 670 then decide (3 ≤ count667 b) else decide (4 ≤ count667 b))) else (if i < 672 then decide (5 ≤ count667 b) else (if i < 673 then decide (6 ≤ count667 b) else decide (7 ≤ count667 b)))) else (if i < 677 then (if i < 675 then decide (8 ≤ count667 b) else (if i < 676 then decide (9 ≤ count667 b) else decide (10 ≤ count667 b))) else (if i < 678 then decide (11 ≤ count667 b) else (if i < 679 then decide (12 ≤ count667 b) else decide (13 ≤ count667 b))))) else (if i < 686 then (if i < 683 then (if i < 681 then decide (14 ≤ count667 b) else (if i < 682 then decide (15 ≤ count667 b) else decide (16 ≤ count667 b))) else (if i < 684 then decide (17 ≤ count667 b) else (if i < 685 then decide (18 ≤ count667 b) else decide (19 ≤ count667 b)))) else (if i < 689 then (if i < 687 then decide (20 ≤ count667 b) else (if i < 688 then decide (21 ≤ count667 b) else decide (22 ≤ count667 b))) else (if i < 690 then decide (23 ≤ count667 b) else (if i < 691 then decide (24 ≤ count667 b) else decide (25 ≤ count667 b)))))) else (if i < 704 then (if i < 698 then (if i < 695 then (if i < 693 then decide (26 ≤ count667 b) else (if i < 694 then decide (27 ≤ count667 b) else decide (28 ≤ count667 b))) else (if i < 696 then decide (1 ≤ count695 b) else (if i < 697 then decide (2 ≤ count695 b) else decide (3 ≤ count695 b)))) else (if i < 701 then (if i < 699 then decide (4 ≤ count695 b) else (if i < 700 then decide (5 ≤ count695 b) else decide (6 ≤ count695 b))) else (if i < 702 then decide (7 ≤ count695 b) else (if i < 703 then decide (8 ≤ count695 b) else decide (9 ≤ count695 b))))) else (if i < 710 then (if i < 707 then (if i < 705 then decide (10 ≤ count695 b) else (if i < 706 then decide (11 ≤ count695 b) else decide (12 ≤ count695 b))) else (if i < 708 then decide (13 ≤ count695 b) else (if i < 709 then decide (14 ≤ count695 b) else decide (15 ≤ count695 b)))) else (if i < 713 then (if i < 711 then decide (16 ≤ count695 b) else (if i < 712 then decide (17 ≤ count695 b) else decide (18 ≤ count695 b))) else (if i < 714 then decide (19 ≤ count695 b) else (if i < 715 then decide (20 ≤ count695 b) else decide (21 ≤ count695 b))))))) else (if i < 740 then (if i < 728 then (if i < 722 then (if i < 719 then (if i < 717 then decide (22 ≤ count695 b) else (if i < 718 then decide (23 ≤ count695 b) else decide (24 ≤ count695 b))) else (if i < 720 then decide (25 ≤ count695 b) else (if i < 721 then decide (26 ≤ count695 b) else decide (27 ≤ count695 b)))) else (if i < 725 then (if i < 723 then decide (28 ≤ count695 b) else (if i < 724 then decide (29 ≤ count695 b) else decide (30 ≤ count695 b))) else (if i < 726 then decide (31 ≤ count695 b) else (if i < 727 then decide (32 ≤ count695 b) else decide (33 ≤ count695 b))))) else (if i < 734 then (if i < 731 then (if i < 729 then decide (34 ≤ count695 b) else (if i < 730 then decide (35 ≤ count695 b) else decide (36 ≤ count695 b))) else (if i < 732 then decide (37 ≤ count695 b) else (if i < 733 then decide (38 ≤ count695 b) else decide (39 ≤ count695 b)))) else (if i < 737 then (if i < 735 then decide (40 ≤ count695 b) else (if i < 736 then decide (41 ≤ count695 b) else decide (42 ≤ count695 b))) else (if i < 738 then decide (1 ≤ count737 b) else (if i < 739 then decide (2 ≤ count737 b) else decide (1 ≤ count739 b)))))) else (if i < 752 then (if i < 746 then (if i < 743 then (if i < 741 then decide (2 ≤ count739 b) else (if i < 742 then decide (3 ≤ count739 b) else decide (1 ≤ count742 b))) else (if i < 744 then decide (2 ≤ count742 b) else (if i < 745 then decide (1 ≤ count744 b) else decide (2 ≤ count744 b)))) else (if i < 749 then (if i < 747 then decide (3 ≤ count744 b) else (if i < 748 then decide (1 ≤ count747 b) else decide (2 ≤ count747 b))) else (if i < 750 then decide (3 ≤ count747 b) else (if i < 751 then decide (4 ≤ count747 b) else decide (5 ≤ count747 b))))) else (if i < 758 then (if i < 755 then (if i < 753 then decide (6 ≤ count747 b) else (if i < 754 then decide (1 ≤ count753 b) else decide (2 ≤ count753 b))) else (if i < 756 then decide (1 ≤ count755 b) else (if i < 757 then decide (2 ≤ count755 b) else decide (3 ≤ count755 b)))) else (if i < 761 then (if i < 759 then decide (1 ≤ count758 b) else (if i < 760 then decide (2 ≤ count758 b) else decide (1 ≤ count760 b))) else (if i < 762 then decide (2 ≤ count760 b) else (if i < 763 then decide (1 ≤ count762 b) else decide (2 ≤ count762 b))))))))))) else (if i < 1146 then (if i < 955 then (if i < 859 then (if i < 811 then (if i < 787 then (if i < 775 then (if i < 769 then (if i < 766 then (if i < 765 then decide (3 ≤ count762 b) else decide (4 ≤ count762 b)) else (if i < 767 then decide (1 ≤ count766 b) else (if i < 768 then decide (2 ≤ count766 b) else decide (3 ≤ count766 b)))) else (if i < 772 then (if i < 770 then decide (4 ≤ count766 b) else (if i < 771 then decide (5 ≤ count766 b) else decide (6 ≤ count766 b))) else (if i < 773 then decide (7 ≤ count766 b) else (if i < 774 then decide (1 ≤ count773 b) else decide (2 ≤ count773 b))))) else (if i < 781 then (if i < 778 then (if i < 776 then decide (3 ≤ count773 b) else (if i < 777 then decide (4 ≤ count773 b) else decide (5 ≤ count773 b))) else (if i < 779 then decide (6 ≤ count773 b) else (if i < 780 then decide (7 ≤ count773 b) else decide (8 ≤ count773 b)))) else (if i < 784 then (if i < 782 then decide (9 ≤ count773 b) else (if i < 783 then decide (10 ≤ count773 b) else decide (11 ≤ count773 b))) else (if i < 785 then decide (12 ≤ count773 b) else (if i < 786 then decide (13 ≤ count773 b) else decide (1 ≤ count786 b)))))) else (if i < 799 then (if i < 793 then (if i < 790 then (if i < 788 then decide (2 ≤ count786 b) else (if i < 789 then decide (1 ≤ count788 b) else decide (2 ≤ count788 b))) else (if i < 791 then decide (3 ≤ count788 b) else (if i < 792 then decide (1 ≤ count791 b) else decide (2 ≤ count791 b)))) else (if i < 796 then (if i < 794 then decide (1 ≤ count793 b) else (if i < 795 then decide (2 ≤ count793 b) else decide (1 ≤ count795 b))) else (if i < 797 then decide (2 ≤ count795 b) else (if i < 798 then decide (3 ≤ count795 b) else decide (4 ≤ count795 b))))) else (if i < 805 then (if i < 802 then (if i < 800 then decide (1 ≤ count799 b) else (if i < 801 then decide (2 ≤ count799 b) else decide (3 ≤ count799 b))) else (if i < 803 then decide (4 ≤ count799 b) else (if i < 804 then decide (5 ≤ count799 b) else decide (6 ≤ count799 b)))) else (if i < 808 then (if i < 806 then decide (7 ≤ count799 b) else (if i < 807 then decide (1 ≤ count806 b) else decide (2 ≤ count806 b))) else (if i < 809 then decide (1 ≤ count808 b) else (if i < 810 then decide (2 ≤ count808 b) else decide (3 ≤ count808 b))))))) else (if i < 835 then (if i < 823 then (if i < 817 then (if i < 814 then (if i < 812 then decide (1 ≤ count811 b) else (if i < 813 then decide (2 ≤ count811 b) else decide (1 ≤ count813 b))) else (if i < 815 then decide (2 ≤ count813 b) else (if i < 816 then decide (1 ≤ count815 b) else decide (2 ≤ count815 b)))) else (if i < 820 then (if i < 818 then decide (3 ≤ count815 b) else (if i < 819 then decide (4 ≤ count815 b) else decide (1 ≤ count819 b))) else (if i < 821 then decide (2 ≤ count819 b) else (if i < 822 then decide (3 ≤ count819 b) else decide (4 ≤ count819 b))))) else (if i < 829 then (if i < 826 then (if i < 824 then decide (5 ≤ count819 b) else (if i < 825 then decide (6 ≤ count819 b) else decide (7 ≤ count819 b))) else (if i < 827 then decide (1 ≤ count826 b) else (if i < 828 then decide (2 ≤ count826 b) else decide (3 ≤ count826 b)))) else (if i < 832 then (if i < 830 then decide (4 ≤ count826 b) else (if i < 831 then decide (5 ≤ count826 b) else decide (6 ≤ count826 b))) else (if i < 833 then decide (7 ≤ count826 b) else (if i < 834 then decide (8 ≤ count826 b) else decide (9 ≤ count826 b)))))) else (if i < 847 then (if i < 841 then (if i < 838 then (if i < 836 then decide (10 ≤ count826 b) else (if i < 837 then decide (11 ≤ count826 b) else decide (12 ≤ count826 b))) else (if i < 839 then decide (13 ≤ count826 b) else (if i < 840 then decide (14 ≤ count826 b) else decide (1 ≤ count840 b)))) else (if i < 844 then (if i < 842 then decide (2 ≤ count840 b) else (if i < 843 then decide (3 ≤ count840 b) else decide (4 ≤ count840 b))) else (if i < 845 then decide (5 ≤ count840 b) else (if i < 846 then decide (6 ≤ count840 b) else decide (7 ≤ count840 b))))) else (if i < 853 then (if i < 850 then (if i < 848 then decide (8 ≤ count840 b) else (if i < 849 then decide (9 ≤ count840 b) else decide (10 ≤ count840 b))) else (if i < 851 then decide (11 ≤ count840 b) else (if i < 852 then decide (12 ≤ count840 b) else decide (13 ≤ count840 b)))) else (if i < 856 then (if i < 854 then decide (14 ≤ count840 b) else (if i < 855 then decide (15 ≤ count840 b) else decide (1 ≤ count855 b))) else (if i < 857 then decide (2 ≤ count855 b) else (if i < 858 then decide (1 ≤ count857 b) else decide (2 ≤ count857 b)))))))) else (if i < 907 then (if i < 883 then (if i < 871 then (if i < 865 then (if i < 862 then (if i < 860 then decide (3 ≤ count857 b) else (if i < 861 then decide (1 ≤ count860 b) else decide (2 ≤ count860 b))) else (if i < 863 then decide (1 ≤ count862 b) else (if i < 864 then decide (2 ≤ count862 b) else decide (1 ≤ count864 b)))) else (if i < 868 then (if i < 866 then decide (2 ≤ count864 b) else (if i < 867 then decide (3 ≤ count864 b) else decide (4 ≤ count864 b))) else (if i < 869 then decide (1 ≤ count868 b) else (if i < 870 then decide (2 ≤ count868 b) else decide (3 ≤ count868 b))))) else (if i < 877 then (if i < 874 then (if i < 872 then decide (4 ≤ count868 b) else (if i < 873 then decide (5 ≤ count868 b) else decide (6 ≤ count868 b))) else (if i < 875 then decide (7 ≤ count868 b) else (if i < 876 then decide (1 ≤ count875 b) else decide (2 ≤ count875 b)))) else (if i < 880 then (if i < 878 then decide (1 ≤ count877 b) else (if i < 879 then decide (2 ≤ count877 b) else decide (3 ≤ count877 b))) else (if i < 881 then decide (1 ≤ count880 b) else (if i < 882 then decide (2 ≤ count880 b) else decide (1 ≤ count882 b)))))) else (if i < 895 then (if i < 889 then (if i < 886 then (if i < 884 then decide (2 ≤ count882 b) else (if i < 885 then decide (1 ≤ count884 b) else decide (2 ≤ count884 b))) else (if i < 887 then decide (3 ≤ count884 b) else (if i < 888 then decide (4 ≤ count884 b) else decide (1 ≤ count888 b)))) else (if i < 892 then (if i < 890 then decide (2 ≤ count888 b) else (if i < 891 then decide (3 ≤ count888 b) else decide (4 ≤ count888 b))) else (if i < 893 then decide (5 ≤ count888 b) else (if i < 894 then decide (6 ≤ count888 b) else decide (7 ≤ count888 b))))) else (if i < 901 then (if i < 898 then (if i < 896 then decide (1 ≤ count895 b) else (if i < 897 then decide (2 ≤ count895 b) else decide (3 ≤ count895 b))) else (if i < 899 then decide (4 ≤ count895 b) else (if i < 900 then decide (5 ≤ count895 b) else decide (6 ≤ count895 b)))) else (if i < 904 then (if i < 902 then decide (7 ≤ count895 b) else (if i < 903 then decide (8 ≤ count895 b) else decide (9 ≤ count895 b))) else (if i < 905 then decide (10 ≤ count895 b) else (if i < 906 then decide (11 ≤ count895 b) else decide (12 ≤ count895 b))))))) else (if i < 931 then (if i < 919 then (if i < 913 then (if i < 910 then (if i < 908 then decide (13 ≤ count895 b) else (if i < 909 then decide (14 ≤ count895 b) else decide (1 ≤ count909 b))) else (if i < 911 then decide (2 ≤ count909 b) else (if i < 912 then decide (1 ≤ count911 b) else decide (2 ≤ count911 b)))) else (if i < 916 then (if i < 914 then decide (3 ≤ count911 b) else (if i < 915 then decide (1 ≤ count914 b) else decide (2 ≤ count914 b))) else (if i < 917 then decide (1 ≤ count916 b) else (if i < 918 then decide (2 ≤ count916 b) else decide (1 ≤ count918 b))))) else (if i < 925 then (if i < 922 then (if i < 920 then decide (2 ≤ count918 b) else (if i < 921 then decide (3 ≤ count918 b) else decide (4 ≤ count918 b))) else (if i < 923 then decide (1 ≤ count922 b) else (if i < 924 then decide (2 ≤ count922 b) else decide (3 ≤ count922 b)))) else (if i < 928 then (if i < 926 then decide (4 ≤ count922 b) else (if i < 927 then decide (5 ≤ count922 b) else decide (6 ≤ count922 b))) else (if i < 929 then decide (7 ≤ count922 b) else (if i < 930 then decide (1 ≤ count929 b) else decide (2 ≤ count929 b)))))) else (if i < 943 then (if i < 937 then (if i < 934 then (if i < 932 then decide (1 ≤ count931 b) else (if i < 933 then decide (2 ≤ count931 b) else decide (3 ≤ count931 b))) else (if i < 935 then decide (1 ≤ count934 b) else (if i < 936 then decide (2 ≤ count934 b) else decide (1 ≤ count936 b)))) else (if i < 940 then (if i < 938 then decide (2 ≤ count936 b) else (if i < 939 then decide (1 ≤ count938 b) else decide (2 ≤ count938 b))) else (if i < 941 then decide (3 ≤ count938 b) else (if i < 942 then decide (4 ≤ count938 b) else decide (1 ≤ count942 b))))) else (if i < 949 then (if i < 946 then (if i < 944 then decide (2 ≤ count942 b) else (if i < 945 then decide (3 ≤ count942 b) else decide (4 ≤ count942 b))) else (if i < 947 then decide (5 ≤ count942 b) else (if i < 948 then decide (6 ≤ count942 b) else decide (7 ≤ count942 b)))) else (if i < 952 then (if i < 950 then decide (1 ≤ count949 b) else (if i < 951 then decide (2 ≤ count949 b) else decide (3 ≤ count949 b))) else (if i < 953 then decide (4 ≤ count949 b) else (if i < 954 then decide (5 ≤ count949 b) else decide (6 ≤ count949 b))))))))) else (if i < 1050 then (if i < 1002 then (if i < 978 then (if i < 966 then (if i < 960 then (if i < 957 then (if i < 956 then decide (7 ≤ count949 b) else decide (8 ≤ count949 b)) else (if i < 958 then decide (9 ≤ count949 b) else (if i < 959 then decide (10 ≤ count949 b) else decide (11 ≤ count949 b)))) else (if i < 963 then (if i < 961 then decide (12 ≤ count949 b) else (if i < 962 then decide (13 ≤ count949 b) else decide (14 ≤ count949 b))) else (if i < 964 then decide (1 ≤ count963 b) else (if i < 965 then decide (2 ≤ count963 b) else decide (3 ≤ count963 b))))) else (if i < 972 then (if i < 969 then (if i < 967 then decide (4 ≤ count963 b) else (if i < 968 then decide (5 ≤ count963 b) else decide (6 ≤ count963 b))) else (if i < 970 then decide (7 ≤ count963 b) else (if i < 971 then decide (8 ≤ count963 b) else decide (9 ≤ count963 b)))) else (if i < 975 then (if i < 973 then decide (10 ≤ count963 b) else (if i < 974 then decide (11 ≤ count963 b) else decide (12 ≤ count963 b))) else (if i < 976 then decide (13 ≤ count963 b) else (if i < 977 then decide (14 ≤ count963 b) else decide (15 ≤ count963 b)))))) else (if i < 990 then (if i < 984 then (if i < 981 then (if i < 979 then decide (1 ≤ count978 b) else (if i < 980 then decide (2 ≤ count978 b) else decide (3 ≤ count978 b))) else (if i < 982 then decide (4 ≤ count978 b) else (if i < 983 then decide (5 ≤ count978 b) else decide (6 ≤ count978 b)))) else (if i < 987 then (if i < 985 then decide (7 ≤ count978 b) else (if i < 986 then decide (8 ≤ count978 b) else decide (9 ≤ count978 b))) else (if i < 988 then decide (10 ≤ count978 b) else (if i < 989 then decide (11 ≤ count978 b) else decide (12 ≤ count978 b))))) else (if i < 996 then (if i < 993 then (if i < 991 then decide (13 ≤ count978 b) else (if i < 992 then decide (14 ≤ count978 b) else decide (15 ≤ count978 b))) else (if i < 994 then decide (1 ≤ count993 b) else (if i < 995 then decide (2 ≤ count993 b) else decide (1 ≤ count995 b)))) else (if i < 999 then (if i < 997 then decide (2 ≤ count995 b) else (if i < 998 then decide (3 ≤ count995 b) else decide (1 ≤ count998 b))) else (if i < 1000 then decide (2 ≤ count998 b) else (if i < 1001 then decide (1 ≤ count1000 b) else decide (2 ≤ count1000 b))))))) else (if i < 1026 then (if i < 1014 then (if i < 1008 then (if i < 1005 then (if i < 1003 then decide (3 ≤ count1000 b) else (if i < 1004 then decide (1 ≤ count1003 b) else decide (2 ≤ count1003 b))) else (if i < 1006 then decide (3 ≤ count1003 b) else (if i < 1007 then decide (4 ≤ count1003 b) else decide (5 ≤ count1003 b)))) else (if i < 1011 then (if i < 1009 then decide (6 ≤ count1003 b) else (if i < 1010 then decide (1 ≤ count1009 b) else decide (2 ≤ count1009 b))) else (if i < 1012 then decide (1 ≤ count1011 b) else (if i < 1013 then decide (2 ≤ count1011 b) else decide (3 ≤ count1011 b))))) else (if i < 1020 then (if i < 1017 then (if i < 1015 then decide (1 ≤ count1014 b) else (if i < 1016 then decide (2 ≤ count1014 b) else decide (1 ≤ count1016 b))) else (if i < 1018 then decide (2 ≤ count1016 b) else (if i < 1019 then decide (1 ≤ count1018 b) else decide (2 ≤ count1018 b)))) else (if i < 1023 then (if i < 1021 then decide (3 ≤ count1018 b) else (if i < 1022 then decide (4 ≤ count1018 b) else decide (1 ≤ count1022 b))) else (if i < 1024 then decide (2 ≤ count1022 b) else (if i < 1025 then decide (3 ≤ count1022 b) else decide (4 ≤ count1022 b)))))) else (if i < 1038 then (if i < 1032 then (if i < 1029 then (if i < 1027 then decide (5 ≤ count1022 b) else (if i < 1028 then decide (6 ≤ count1022 b) else decide (7 ≤ count1022 b))) else (if i < 1030 then decide (1 ≤ count1029 b) else (if i < 1031 then decide (2 ≤ count1029 b) else decide (3 ≤ count1029 b)))) else (if i < 1035 then (if i < 1033 then decide (4 ≤ count1029 b) else (if i < 1034 then decide (5 ≤ count1029 b) else decide (6 ≤ count1029 b))) else (if i < 1036 then decide (7 ≤ count1029 b) else (if i < 1037 then decide (8 ≤ count1029 b) else decide (9 ≤ count1029 b))))) else (if i < 1044 then (if i < 1041 then (if i < 1039 then decide (10 ≤ count1029 b) else (if i < 1040 then decide (11 ≤ count1029 b) else decide (12 ≤ count1029 b))) else (if i < 1042 then decide (13 ≤ count1029 b) else (if i < 1043 then decide (1 ≤ count1042 b) else decide (2 ≤ count1042 b)))) else (if i < 1047 then (if i < 1045 then decide (1 ≤ count1044 b) else (if i < 1046 then decide (2 ≤ count1044 b) else decide (3 ≤ count1044 b))) else (if i < 1048 then decide (1 ≤ count1047 b) else (if i < 1049 then decide (2 ≤ count1047 b) else decide (1 ≤ count1049 b)))))))) else (if i < 1098 then (if i < 1074 then (if i < 1062 then (if i < 1056 then (if i < 1053 then (if i < 1051 then decide (2 ≤ count1049 b) else (if i < 1052 then decide (3 ≤ count1049 b) else decide (1 ≤ count1052 b))) else (if i < 1054 then decide (2 ≤ count1052 b) else (if i < 1055 then decide (3 ≤ count1052 b) else decide (4 ≤ count1052 b)))) else (if i < 1059 then (if i < 1057 then decide (5 ≤ count1052 b) else (if i < 1058 then decide (6 ≤ count1052 b) else decide (1 ≤ count1058 b))) else (if i < 1060 then decide (2 ≤ count1058 b) else (if i < 1061 then decide (1 ≤ count1060 b) else decide (2 ≤ count1060 b))))) else (if i < 1068 then (if i < 1065 then (if i < 1063 then decide (3 ≤ count1060 b) else (if i < 1064 then decide (1 ≤ count1063 b) else decide (2 ≤ count1063 b))) else (if i < 1066 then decide (1 ≤ count1065 b) else (if i < 1067 then decide (2 ≤ count1065 b) else decide (1 ≤ count1067 b)))) else (if i < 1071 then (if i < 1069 then decide (2 ≤ count1067 b) else (if i < 1070 then decide (3 ≤ count1067 b) else decide (4 ≤ count1067 b))) else (if i < 1072 then decide (1 ≤ count1071 b) else (if i < 1073 then decide (2 ≤ count1071 b) else decide (3 ≤ count1071 b)))))) else (if i < 1086 then (if i < 1080 then (if i < 1077 then (if i < 1075 then decide (4 ≤ count1071 b) else (if i < 1076 then decide (5 ≤ count1071 b) else decide (6 ≤ count1071 b))) else (if i < 1078 then decide (7 ≤ count1071 b) else (if i < 1079 then decide (1 ≤ count1078 b) else decide (2 ≤ count1078 b)))) else (if i < 1083 then (if i < 1081 then decide (3 ≤ count1078 b) else (if i < 1082 then decide (4 ≤ count1078 b) else decide (5 ≤ count1078 b))) else (if i < 1084 then decide (6 ≤ count1078 b) else (if i < 1085 then decide (7 ≤ count1078 b) else decide (8 ≤ count1078 b))))) else (if i < 1092 then (if i < 1089 then (if i < 1087 then decide (9 ≤ count1078 b) else (if i < 1088 then decide (10 ≤ count1078 b) else decide (11 ≤ count1078 b))) else (if i < 1090 then decide (12 ≤ count1078 b) else (if i < 1091 then decide (13 ≤ count1078 b) else decide (1 ≤ count1091 b)))) else (if i < 1095 then (if i < 1093 then decide (2 ≤ count1091 b) else (if i < 1094 then decide (3 ≤ count1091 b) else decide (4 ≤ count1091 b))) else (if i < 1096 then decide (5 ≤ count1091 b) else (if i < 1097 then decide (6 ≤ count1091 b) else decide (7 ≤ count1091 b))))))) else (if i < 1122 then (if i < 1110 then (if i < 1104 then (if i < 1101 then (if i < 1099 then decide (8 ≤ count1091 b) else (if i < 1100 then decide (9 ≤ count1091 b) else decide (10 ≤ count1091 b))) else (if i < 1102 then decide (11 ≤ count1091 b) else (if i < 1103 then decide (12 ≤ count1091 b) else decide (13 ≤ count1091 b)))) else (if i < 1107 then (if i < 1105 then decide (14 ≤ count1091 b) else (if i < 1106 then decide (15 ≤ count1091 b) else decide (16 ≤ count1091 b))) else (if i < 1108 then decide (17 ≤ count1091 b) else (if i < 1109 then decide (18 ≤ count1091 b) else decide (19 ≤ count1091 b))))) else (if i < 1116 then (if i < 1113 then (if i < 1111 then decide (20 ≤ count1091 b) else (if i < 1112 then decide (21 ≤ count1091 b) else decide (22 ≤ count1091 b))) else (if i < 1114 then decide (23 ≤ count1091 b) else (if i < 1115 then decide (24 ≤ count1091 b) else decide (25 ≤ count1091 b)))) else (if i < 1119 then (if i < 1117 then decide (26 ≤ count1091 b) else (if i < 1118 then decide (1 ≤ count1117 b) else decide (2 ≤ count1117 b))) else (if i < 1120 then decide (1 ≤ count1119 b) else (if i < 1121 then decide (2 ≤ count1119 b) else decide (3 ≤ count1119 b)))))) else (if i < 1134 then (if i < 1128 then (if i < 1125 then (if i < 1123 then decide (1 ≤ count1122 b) else (if i < 1124 then decide (2 ≤ count1122 b) else decide (1 ≤ count1124 b))) else (if i < 1126 then decide (2 ≤ count1124 b) else (if i < 1127 then decide (3 ≤ count1124 b) else decide (1 ≤ count1127 b)))) else (if i < 1131 then (if i < 1129 then decide (2 ≤ count1127 b) else (if i < 1130 then decide (3 ≤ count1127 b) else decide (4 ≤ count1127 b))) else (if i < 1132 then decide (5 ≤ count1127 b) else (if i < 1133 then decide (6 ≤ count1127 b) else decide (1 ≤ count1133 b))))) else (if i < 1140 then (if i < 1137 then (if i < 1135 then decide (2 ≤ count1133 b) else (if i < 1136 then decide (1 ≤ count1135 b) else decide (2 ≤ count1135 b))) else (if i < 1138 then decide (3 ≤ count1135 b) else (if i < 1139 then decide (1 ≤ count1138 b) else decide (2 ≤ count1138 b)))) else (if i < 1143 then (if i < 1141 then decide (1 ≤ count1140 b) else (if i < 1142 then decide (2 ≤ count1140 b) else decide (1 ≤ count1142 b))) else (if i < 1144 then decide (2 ≤ count1142 b) else (if i < 1145 then decide (3 ≤ count1142 b) else decide (4 ≤ count1142 b)))))))))) else (if i < 1337 then (if i < 1241 then (if i < 1193 then (if i < 1169 then (if i < 1157 then (if i < 1151 then (if i < 1148 then (if i < 1147 then decide (1 ≤ count1146 b) else decide (2 ≤ count1146 b)) else (if i < 1149 then decide (3 ≤ count1146 b) else (if i < 1150 then decide (4 ≤ count1146 b) else decide (5 ≤ count1146 b)))) else (if i < 1154 then (if i < 1152 then decide (6 ≤ count1146 b) else (if i < 1153 then decide (7 ≤ count1146 b) else decide (1 ≤ count1153 b))) else (if i < 1155 then decide (2 ≤ count1153 b) else (if i < 1156 then decide (3 ≤ count1153 b) else decide (4 ≤ count1153 b))))) else (if i < 1163 then (if i < 1160 then (if i < 1158 then decide (5 ≤ count1153 b) else (if i < 1159 then decide (6 ≤ count1153 b) else decide (7 ≤ count1153 b))) else (if i < 1161 then decide (8 ≤ count1153 b) else (if i < 1162 then decide (9 ≤ count1153 b) else decide (10 ≤ count1153 b)))) else (if i < 1166 then (if i < 1164 then decide (11 ≤ count1153 b) else (if i < 1165 then decide (12 ≤ count1153 b) else decide (13 ≤ count1153 b))) else (if i < 1167 then decide (1 ≤ count1166 b) else (if i < 1168 then decide (2 ≤ count1166 b) else decide (1 ≤ count1168 b)))))) else (if i < 1181 then (if i < 1175 then (if i < 1172 then (if i < 1170 then decide (2 ≤ count1168 b) else (if i < 1171 then decide (3 ≤ count1168 b) else decide (1 ≤ count1171 b))) else (if i < 1173 then decide (2 ≤ count1171 b) else (if i < 1174 then decide (1 ≤ count1173 b) else decide (2 ≤ count1173 b)))) else (if i < 1178 then (if i < 1176 then decide (1 ≤ count1175 b) else (if i < 1177 then decide (2 ≤ count1175 b) else decide (3 ≤ count1175 b))) else (if i < 1179 then decide (4 ≤ count1175 b) else (if i < 1180 then decide (1 ≤ count1179 b) else decide (2 ≤ count1179 b))))) else (if i < 1187 then (if i < 1184 then (if i < 1182 then decide (3 ≤ count1179 b) else (if i < 1183 then decide (4 ≤ count1179 b) else decide (5 ≤ count1179 b))) else (if i < 1185 then decide (6 ≤ count1179 b) else (if i < 1186 then decide (7 ≤ count1179 b) else decide (1 ≤ count1186 b)))) else (if i < 1190 then (if i < 1188 then decide (2 ≤ count1186 b) else (if i < 1189 then decide (1 ≤ count1188 b) else decide (2 ≤ count1188 b))) else (if i < 1191 then decide (3 ≤ count1188 b) else (if i < 1192 then decide (1 ≤ count1191 b) else decide (2 ≤ count1191 b))))))) else (if i < 1217 then (if i < 1205 then (if i < 1199 then (if i < 1196 then (if i < 1194 then decide (1 ≤ count1193 b) else (if i < 1195 then decide (2 ≤ count1193 b) else decide (1 ≤ count1195 b))) else (if i < 1197 then decide (2 ≤ count1195 b) else (if i < 1198 then decide (3 ≤ count1195 b) else decide (4 ≤ count1195 b)))) else (if i < 1202 then (if i < 1200 then decide (1 ≤ count1199 b) else (if i < 1201 then decide (2 ≤ count1199 b) else decide (3 ≤ count1199 b))) else (if i < 1203 then decide (4 ≤ count1199 b) else (if i < 1204 then decide (5 ≤ count1199 b) else decide (6 ≤ count1199 b))))) else (if i < 1211 then (if i < 1208 then (if i < 1206 then decide (7 ≤ count1199 b) else (if i < 1207 then decide (1 ≤ count1206 b) else decide (2 ≤ count1206 b))) else (if i < 1209 then decide (3 ≤ count1206 b) else (if i < 1210 then decide (4 ≤ count1206 b) else decide (5 ≤ count1206 b)))) else (if i < 1214 then (if i < 1212 then decide (6 ≤ count1206 b) else (if i < 1213 then decide (7 ≤ count1206 b) else decide (8 ≤ count1206 b))) else (if i < 1215 then decide (9 ≤ count1206 b) else (if i < 1216 then decide (10 ≤ count1206 b) else decide (11 ≤ count1206 b)))))) else (if i < 1229 then (if i < 1223 then (if i < 1220 then (if i < 1218 then decide (12 ≤ count1206 b) else (if i < 1219 then decide (13 ≤ count1206 b) else decide (14 ≤ count1206 b))) else (if i < 1221 then decide (1 ≤ count1220 b) else (if i < 1222 then decide (2 ≤ count1220 b) else decide (3 ≤ count1220 b)))) else (if i < 1226 then (if i < 1224 then decide (4 ≤ count1220 b) else (if i < 1225 then decide (5 ≤ count1220 b) else decide (6 ≤ count1220 b))) else (if i < 1227 then decide (7 ≤ count1220 b) else (if i < 1228 then decide (8 ≤ count1220 b) else decide (9 ≤ count1220 b))))) else (if i < 1235 then (if i < 1232 then (if i < 1230 then decide (10 ≤ count1220 b) else (if i < 1231 then decide (11 ≤ count1220 b) else decide (12 ≤ count1220 b))) else (if i < 1233 then decide (13 ≤ count1220 b) else (if i < 1234 then decide (14 ≤ count1220 b) else decide (15 ≤ count1220 b)))) else (if i < 1238 then (if i < 1236 then decide (16 ≤ count1220 b) else (if i < 1237 then decide (17 ≤ count1220 b) else decide (18 ≤ count1220 b))) else (if i < 1239 then decide (19 ≤ count1220 b) else (if i < 1240 then decide (20 ≤ count1220 b) else decide (21 ≤ count1220 b)))))))) else (if i < 1289 then (if i < 1265 then (if i < 1253 then (if i < 1247 then (if i < 1244 then (if i < 1242 then decide (22 ≤ count1220 b) else (if i < 1243 then decide (23 ≤ count1220 b) else decide (24 ≤ count1220 b))) else (if i < 1245 then decide (25 ≤ count1220 b) else (if i < 1246 then decide (26 ≤ count1220 b) else decide (27 ≤ count1220 b)))) else (if i < 1250 then (if i < 1248 then decide (1 ≤ count1247 b) else (if i < 1249 then decide (2 ≤ count1247 b) else decide (3 ≤ count1247 b))) else (if i < 1251 then decide (4 ≤ count1247 b) else (if i < 1252 then decide (5 ≤ count1247 b) else decide (6 ≤ count1247 b))))) else (if i < 1259 then (if i < 1256 then (if i < 1254 then decide (7 ≤ count1247 b) else (if i < 1255 then decide (8 ≤ count1247 b) else decide (9 ≤ count1247 b))) else (if i < 1257 then decide (10 ≤ count1247 b) else (if i < 1258 then decide (11 ≤ count1247 b) else decide (12 ≤ count1247 b)))) else (if i < 1262 then (if i < 1260 then decide (13 ≤ count1247 b) else (if i < 1261 then decide (14 ≤ count1247 b) else decide (15 ≤ count1247 b))) else (if i < 1263 then decide (16 ≤ count1247 b) else (if i < 1264 then decide (17 ≤ count1247 b) else decide (18 ≤ count1247 b)))))) else (if i < 1277 then (if i < 1271 then (if i < 1268 then (if i < 1266 then decide (19 ≤ count1247 b) else (if i < 1267 then decide (20 ≤ count1247 b) else decide (21 ≤ count1247 b))) else (if i < 1269 then decide (22 ≤ count1247 b) else (if i < 1270 then decide (23 ≤ count1247 b) else decide (24 ≤ count1247 b)))) else (if i < 1274 then (if i < 1272 then decide (25 ≤ count1247 b) else (if i < 1273 then decide (26 ≤ count1247 b) else decide (27 ≤ count1247 b))) else (if i < 1275 then decide (28 ≤ count1247 b) else (if i < 1276 then decide (29 ≤ count1247 b) else decide (30 ≤ count1247 b))))) else (if i < 1283 then (if i < 1280 then (if i < 1278 then decide (31 ≤ count1247 b) else (if i < 1279 then decide (32 ≤ count1247 b) else decide (33 ≤ count1247 b))) else (if i < 1281 then decide (34 ≤ count1247 b) else (if i < 1282 then decide (35 ≤ count1247 b) else decide (36 ≤ count1247 b)))) else (if i < 1286 then (if i < 1284 then decide (37 ≤ count1247 b) else (if i < 1285 then decide (38 ≤ count1247 b) else decide (39 ≤ count1247 b))) else (if i < 1287 then decide (40 ≤ count1247 b) else (if i < 1288 then decide (41 ≤ count1247 b) else decide (42 ≤ count1247 b))))))) else (if i < 1313 then (if i < 1301 then (if i < 1295 then (if i < 1292 then (if i < 1290 then decide (1 ≤ count1289 b) else (if i < 1291 then decide (2 ≤ count1289 b) else decide (1 ≤ count1291 b))) else (if i < 1293 then decide (2 ≤ count1291 b) else (if i < 1294 then decide (3 ≤ count1291 b) else decide (1 ≤ count1294 b)))) else (if i < 1298 then (if i < 1296 then decide (2 ≤ count1294 b) else (if i < 1297 then decide (1 ≤ count1296 b) else decide (2 ≤ count1296 b))) else (if i < 1299 then decide (3 ≤ count1296 b) else (if i < 1300 then decide (1 ≤ count1299 b) else decide (2 ≤ count1299 b))))) else (if i < 1307 then (if i < 1304 then (if i < 1302 then decide (3 ≤ count1299 b) else (if i < 1303 then decide (4 ≤ count1299 b) else decide (5 ≤ count1299 b))) else (if i < 1305 then decide (6 ≤ count1299 b) else (if i < 1306 then decide (1 ≤ count1305 b) else decide (2 ≤ count1305 b)))) else (if i < 1310 then (if i < 1308 then decide (1 ≤ count1307 b) else (if i < 1309 then decide (2 ≤ count1307 b) else decide (3 ≤ count1307 b))) else (if i < 1311 then decide (1 ≤ count1310 b) else (if i < 1312 then decide (2 ≤ count1310 b) else decide (1 ≤ count1312 b)))))) else (if i < 1325 then (if i < 1319 then (if i < 1316 then (if i < 1314 then decide (2 ≤ count1312 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))) else (if i < 1317 then decide (3 ≤ count1314 b) else (if i < 1318 then decide (4 ≤ count1314 b) else decide (1 ≤ count1318 b)))) else (if i < 1322 then (if i < 1320 then decide (2 ≤ count1318 b) else (if i < 1321 then decide (3 ≤ count1318 b) else decide (4 ≤ count1318 b))) else (if i < 1323 then decide (5 ≤ count1318 b) else (if i < 1324 then decide (6 ≤ count1318 b) else decide (7 ≤ count1318 b))))) else (if i < 1331 then (if i < 1328 then (if i < 1326 then decide (1 ≤ count1325 b) else (if i < 1327 then decide (2 ≤ count1325 b) else decide (3 ≤ count1325 b))) else (if i < 1329 then decide (4 ≤ count1325 b) else (if i < 1330 then decide (5 ≤ count1325 b) else decide (6 ≤ count1325 b)))) else (if i < 1334 then (if i < 1332 then decide (7 ≤ count1325 b) else (if i < 1333 then decide (8 ≤ count1325 b) else decide (9 ≤ count1325 b))) else (if i < 1335 then decide (10 ≤ count1325 b) else (if i < 1336 then decide (11 ≤ count1325 b) else decide (12 ≤ count1325 b))))))))) else (if i < 1432 then (if i < 1384 then (if i < 1360 then (if i < 1348 then (if i < 1342 then (if i < 1339 then (if i < 1338 then decide (13 ≤ count1325 b) else decide (1 ≤ count1338 b)) else (if i < 1340 then decide (2 ≤ count1338 b) else (if i < 1341 then decide (1 ≤ count1340 b) else decide (2 ≤ count1340 b)))) else (if i < 1345 then (if i < 1343 then decide (3 ≤ count1340 b) else (if i < 1344 then decide (1 ≤ count1343 b) else decide (2 ≤ count1343 b))) else (if i < 1346 then decide (1 ≤ count1345 b) else (if i < 1347 then decide (2 ≤ count1345 b) else decide (3 ≤ count1345 b))))) else (if i < 1354 then (if i < 1351 then (if i < 1349 then decide (1 ≤ count1348 b) else (if i < 1350 then decide (2 ≤ count1348 b) else decide (3 ≤ count1348 b))) else (if i < 1352 then decide (4 ≤ count1348 b) else (if i < 1353 then decide (5 ≤ count1348 b) else decide (6 ≤ count1348 b)))) else (if i < 1357 then (if i < 1355 then decide (1 ≤ count1354 b) else (if i < 1356 then decide (2 ≤ count1354 b) else decide (1 ≤ count1356 b))) else (if i < 1358 then decide (2 ≤ count1356 b) else (if i < 1359 then decide (3 ≤ count1356 b) else decide (1 ≤ count1359 b)))))) else (if i < 1372 then (if i < 1366 then (if i < 1363 then (if i < 1361 then decide (2 ≤ count1359 b) else (if i < 1362 then decide (1 ≤ count1361 b) else decide (2 ≤ count1361 b))) else (if i < 1364 then decide (1 ≤ count1363 b) else (if i < 1365 then decide (2 ≤ count1363 b) else decide (3 ≤ count1363 b)))) else (if i < 1369 then (if i < 1367 then decide (4 ≤ count1363 b) else (if i < 1368 then decide (1 ≤ count1367 b) else decide (2 ≤ count1367 b))) else (if i < 1370 then decide (3 ≤ count1367 b) else (if i < 1371 then decide (4 ≤ count1367 b) else decide (5 ≤ count1367 b))))) else (if i < 1378 then (if i < 1375 then (if i < 1373 then decide (6 ≤ count1367 b) else (if i < 1374 then decide (7 ≤ count1367 b) else decide (1 ≤ count1374 b))) else (if i < 1376 then decide (2 ≤ count1374 b) else (if i < 1377 then decide (3 ≤ count1374 b) else decide (4 ≤ count1374 b)))) else (if i < 1381 then (if i < 1379 then decide (5 ≤ count1374 b) else (if i < 1380 then decide (6 ≤ count1374 b) else decide (7 ≤ count1374 b))) else (if i < 1382 then decide (8 ≤ count1374 b) else (if i < 1383 then decide (9 ≤ count1374 b) else decide (10 ≤ count1374 b))))))) else (if i < 1408 then (if i < 1396 then (if i < 1390 then (if i < 1387 then (if i < 1385 then decide (11 ≤ count1374 b) else (if i < 1386 then decide (12 ≤ count1374 b) else decide (13 ≤ count1374 b))) else (if i < 1388 then decide (1 ≤ count1387 b) else (if i < 1389 then decide (2 ≤ count1387 b) else decide (3 ≤ count1387 b)))) else (if i < 1393 then (if i < 1391 then decide (4 ≤ count1387 b) else (if i < 1392 then decide (5 ≤ count1387 b) else decide (6 ≤ count1387 b))) else (if i < 1394 then decide (7 ≤ count1387 b) else (if i < 1395 then decide (8 ≤ count1387 b) else decide (9 ≤ count1387 b))))) else (if i < 1402 then (if i < 1399 then (if i < 1397 then decide (10 ≤ count1387 b) else (if i < 1398 then decide (11 ≤ count1387 b) else decide (12 ≤ count1387 b))) else (if i < 1400 then decide (13 ≤ count1387 b) else (if i < 1401 then decide (1 ≤ count1400 b) else decide (2 ≤ count1400 b)))) else (if i < 1405 then (if i < 1403 then decide (1 ≤ count1402 b) else (if i < 1404 then decide (2 ≤ count1402 b) else decide (3 ≤ count1402 b))) else (if i < 1406 then decide (1 ≤ count1405 b) else (if i < 1407 then decide (2 ≤ count1405 b) else decide (1 ≤ count1407 b)))))) else (if i < 1420 then (if i < 1414 then (if i < 1411 then (if i < 1409 then decide (2 ≤ count1407 b) else (if i < 1410 then decide (3 ≤ count1407 b) else decide (1 ≤ count1410 b))) else (if i < 1412 then decide (2 ≤ count1410 b) else (if i < 1413 then decide (3 ≤ count1410 b) else decide (4 ≤ count1410 b)))) else (if i < 1417 then (if i < 1415 then decide (5 ≤ count1410 b) else (if i < 1416 then decide (6 ≤ count1410 b) else decide (1 ≤ count1416 b))) else (if i < 1418 then decide (2 ≤ count1416 b) else (if i < 1419 then decide (1 ≤ count1418 b) else decide (2 ≤ count1418 b))))) else (if i < 1426 then (if i < 1423 then (if i < 1421 then decide (3 ≤ count1418 b) else (if i < 1422 then decide (1 ≤ count1421 b) else decide (2 ≤ count1421 b))) else (if i < 1424 then decide (1 ≤ count1423 b) else (if i < 1425 then decide (2 ≤ count1423 b) else decide (1 ≤ count1425 b)))) else (if i < 1429 then (if i < 1427 then decide (2 ≤ count1425 b) else (if i < 1428 then decide (3 ≤ count1425 b) else decide (4 ≤ count1425 b))) else (if i < 1430 then decide (1 ≤ count1429 b) else (if i < 1431 then decide (2 ≤ count1429 b) else decide (3 ≤ count1429 b)))))))) else (if i < 1480 then (if i < 1456 then (if i < 1444 then (if i < 1438 then (if i < 1435 then (if i < 1433 then decide (4 ≤ count1429 b) else (if i < 1434 then decide (5 ≤ count1429 b) else decide (6 ≤ count1429 b))) else (if i < 1436 then decide (7 ≤ count1429 b) else (if i < 1437 then decide (1 ≤ count1436 b) else decide (2 ≤ count1436 b)))) else (if i < 1441 then (if i < 1439 then decide (3 ≤ count1436 b) else (if i < 1440 then decide (4 ≤ count1436 b) else decide (5 ≤ count1436 b))) else (if i < 1442 then decide (6 ≤ count1436 b) else (if i < 1443 then decide (7 ≤ count1436 b) else decide (8 ≤ count1436 b))))) else (if i < 1450 then (if i < 1447 then (if i < 1445 then decide (9 ≤ count1436 b) else (if i < 1446 then decide (10 ≤ count1436 b) else decide (11 ≤ count1436 b))) else (if i < 1448 then decide (12 ≤ count1436 b) else (if i < 1449 then decide (13 ≤ count1436 b) else decide (1 ≤ count1449 b)))) else (if i < 1453 then (if i < 1451 then decide (2 ≤ count1449 b) else (if i < 1452 then decide (1 ≤ count1451 b) else decide (2 ≤ count1451 b))) else (if i < 1454 then decide (3 ≤ count1451 b) else (if i < 1455 then decide (1 ≤ count1454 b) else decide (2 ≤ count1454 b)))))) else (if i < 1468 then (if i < 1462 then (if i < 1459 then (if i < 1457 then decide (1 ≤ count1456 b) else (if i < 1458 then decide (2 ≤ count1456 b) else decide (1 ≤ count1458 b))) else (if i < 1460 then decide (2 ≤ count1458 b) else (if i < 1461 then decide (3 ≤ count1458 b) else decide (4 ≤ count1458 b)))) else (if i < 1465 then (if i < 1463 then decide (1 ≤ count1462 b) else (if i < 1464 then decide (2 ≤ count1462 b) else decide (3 ≤ count1462 b))) else (if i < 1466 then decide (4 ≤ count1462 b) else (if i < 1467 then decide (5 ≤ count1462 b) else decide (6 ≤ count1462 b))))) else (if i < 1474 then (if i < 1471 then (if i < 1469 then decide (7 ≤ count1462 b) else (if i < 1470 then decide (1 ≤ count1469 b) else decide (2 ≤ count1469 b))) else (if i < 1472 then decide (1 ≤ count1471 b) else (if i < 1473 then decide (2 ≤ count1471 b) else decide (3 ≤ count1471 b)))) else (if i < 1477 then (if i < 1475 then decide (1 ≤ count1474 b) else (if i < 1476 then decide (2 ≤ count1474 b) else decide (1 ≤ count1476 b))) else (if i < 1478 then decide (2 ≤ count1476 b) else (if i < 1479 then decide (1 ≤ count1478 b) else decide (2 ≤ count1478 b))))))) else (if i < 1504 then (if i < 1492 then (if i < 1486 then (if i < 1483 then (if i < 1481 then decide (3 ≤ count1478 b) else (if i < 1482 then decide (4 ≤ count1478 b) else decide (1 ≤ count1482 b))) else (if i < 1484 then decide (2 ≤ count1482 b) else (if i < 1485 then decide (3 ≤ count1482 b) else decide (4 ≤ count1482 b)))) else (if i < 1489 then (if i < 1487 then decide (5 ≤ count1482 b) else (if i < 1488 then decide (6 ≤ count1482 b) else decide (7 ≤ count1482 b))) else (if i < 1490 then decide (1 ≤ count1489 b) else (if i < 1491 then decide (2 ≤ count1489 b) else decide (3 ≤ count1489 b))))) else (if i < 1498 then (if i < 1495 then (if i < 1493 then decide (4 ≤ count1489 b) else (if i < 1494 then decide (5 ≤ count1489 b) else decide (6 ≤ count1489 b))) else (if i < 1496 then decide (7 ≤ count1489 b) else (if i < 1497 then decide (8 ≤ count1489 b) else decide (9 ≤ count1489 b)))) else (if i < 1501 then (if i < 1499 then decide (10 ≤ count1489 b) else (if i < 1500 then decide (11 ≤ count1489 b) else decide (12 ≤ count1489 b))) else (if i < 1502 then decide (13 ≤ count1489 b) else (if i < 1503 then decide (1 ≤ count1502 b) else decide (2 ≤ count1502 b)))))) else (if i < 1516 then (if i < 1510 then (if i < 1507 then (if i < 1505 then decide (3 ≤ count1502 b) else (if i < 1506 then decide (4 ≤ count1502 b) else decide (5 ≤ count1502 b))) else (if i < 1508 then decide (6 ≤ count1502 b) else (if i < 1509 then decide (7 ≤ count1502 b) else decide (8 ≤ count1502 b)))) else (if i < 1513 then (if i < 1511 then decide (9 ≤ count1502 b) else (if i < 1512 then decide (10 ≤ count1502 b) else decide (11 ≤ count1502 b))) else (if i < 1514 then decide (12 ≤ count1502 b) else (if i < 1515 then decide (13 ≤ count1502 b) else decide (1 ≤ count1515 b))))) else (if i < 1522 then (if i < 1519 then (if i < 1517 then decide (2 ≤ count1515 b) else (if i < 1518 then decide (3 ≤ count1515 b) else decide (4 ≤ count1515 b))) else (if i < 1520 then decide (5 ≤ count1515 b) else (if i < 1521 then decide (6 ≤ count1515 b) else decide (7 ≤ count1515 b)))) else (if i < 1525 then (if i < 1523 then decide (8 ≤ count1515 b) else (if i < 1524 then decide (9 ≤ count1515 b) else decide (10 ≤ count1515 b))) else (if i < 1526 then decide (11 ≤ count1515 b) else (if i < 1527 then decide (12 ≤ count1515 b) else decide (13 ≤ count1515 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (35 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (36 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (37 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (44 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (48 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (52 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (53 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (55 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (56 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (98 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (99 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (112 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (113 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (114 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (115 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (118 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (120 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (124 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (126 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (131 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (132 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (133 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (140 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (144 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (148 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (149 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (151 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (152 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (226 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (227 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (228 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (229 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (234 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (235 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (236 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (238 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (240 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (244 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (245 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (247 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (248 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (249 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (251 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (255 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (258 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (259 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (260 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (261 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (266 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (268 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (270 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (272 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (276 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (277 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (279 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (280 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (281 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (283 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (387 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (400 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (401 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (403 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (419 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (421 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (427 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (432 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (436 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (437 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (439 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (441 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (443 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (447 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (480 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (481 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (482 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (483 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (485 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (491 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (493 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (495 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (496 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (497 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (498 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (499 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (502 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (504 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (508 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (509 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (510 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (511 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (44 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (55 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (56 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (115 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (118 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (126 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (234 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (235 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (236 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (270 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value320 (q : Snake 81) : valuation q 320 = decide (2 ≤ count319 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value426 (q : Snake 81) : valuation q 426 = decide (2 ≤ count425 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value1289 (q : Snake 81) : valuation q 1289 = decide (1 ≤ count1289 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (1 ≤ count1291 (baseVal q)) := rfl
theorem value1294 (q : Snake 81) : valuation q 1294 = decide (1 ≤ count1294 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (1 ≤ count1296 (baseVal q)) := rfl
theorem value1299 (q : Snake 81) : valuation q 1299 = decide (1 ≤ count1299 (baseVal q)) := rfl
theorem value1300 (q : Snake 81) : valuation q 1300 = decide (2 ≤ count1299 (baseVal q)) := rfl
theorem value1305 (q : Snake 81) : valuation q 1305 = decide (1 ≤ count1305 (baseVal q)) := rfl
theorem value1307 (q : Snake 81) : valuation q 1307 = decide (1 ≤ count1307 (baseVal q)) := rfl
theorem value1310 (q : Snake 81) : valuation q 1310 = decide (1 ≤ count1310 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (2 ≤ count1310 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (1 ≤ count1312 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (1 ≤ count1314 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (2 ≤ count1314 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (1 ≤ count1318 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (2 ≤ count1318 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (3 ≤ count1325 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (1 ≤ count1338 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (2 ≤ count1340 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (1 ≤ count1343 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (1 ≤ count1345 (baseVal q)) := rfl
theorem value1348 (q : Snake 81) : valuation q 1348 = decide (1 ≤ count1348 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (2 ≤ count1348 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (1 ≤ count1354 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (1 ≤ count1356 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (2 ≤ count1356 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (1 ≤ count1359 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (2 ≤ count1359 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (1 ≤ count1361 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (2 ≤ count1361 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (1 ≤ count1363 (baseVal q)) := rfl
theorem value1364 (q : Snake 81) : valuation q 1364 = decide (2 ≤ count1363 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (3 ≤ count1363 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (1 ≤ count1367 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (2 ≤ count1367 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (3 ≤ count1367 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (4 ≤ count1367 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (5 ≤ count1367 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (2 ≤ count1374 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (3 ≤ count1374 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (4 ≤ count1374 (baseVal q)) := rfl
theorem value1378 (q : Snake 81) : valuation q 1378 = decide (5 ≤ count1374 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (6 ≤ count1374 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (5 ≤ count1387 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (6 ≤ count1387 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (7 ≤ count1387 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (8 ≤ count1387 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (9 ≤ count1387 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (1 ≤ count1400 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (1 ≤ count1402 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (1 ≤ count1405 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (1 ≤ count1407 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (2 ≤ count1407 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (1 ≤ count1410 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (2 ≤ count1410 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (3 ≤ count1410 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (1 ≤ count1416 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (1 ≤ count1418 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (1 ≤ count1421 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (2 ≤ count1421 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (1 ≤ count1423 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (2 ≤ count1423 (baseVal q)) := rfl
theorem value1425 (q : Snake 81) : valuation q 1425 = decide (1 ≤ count1425 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (2 ≤ count1425 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (1 ≤ count1429 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (2 ≤ count1429 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (3 ≤ count1429 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (1 ≤ count1436 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (2 ≤ count1436 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (3 ≤ count1436 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (4 ≤ count1436 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (1 ≤ count1449 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (2 ≤ count1449 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (1 ≤ count1451 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (2 ≤ count1451 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (3 ≤ count1451 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (1 ≤ count1454 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (2 ≤ count1454 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (1 ≤ count1456 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (2 ≤ count1456 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (1 ≤ count1458 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (2 ≤ count1458 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (3 ≤ count1458 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (1 ≤ count1462 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (2 ≤ count1462 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (3 ≤ count1462 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (4 ≤ count1462 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (1 ≤ count1469 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (2 ≤ count1469 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (1 ≤ count1471 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (2 ≤ count1471 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (3 ≤ count1471 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (1 ≤ count1474 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (2 ≤ count1474 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (1 ≤ count1476 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (2 ≤ count1476 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (1 ≤ count1478 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (2 ≤ count1478 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (3 ≤ count1478 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (1 ≤ count1482 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (2 ≤ count1482 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (3 ≤ count1482 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (4 ≤ count1482 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (3 ≤ count1489 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (4 ≤ count1489 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (5 ≤ count1489 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (6 ≤ count1489 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (4 ≤ count1502 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (5 ≤ count1502 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (6 ≤ count1502 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (7 ≤ count1502 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (8 ≤ count1502 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (13 ≤ count1515 (baseVal q)) := rfl
theorem meaningNeg108 (b : Nat → Bool) : literal (valuationOf b) (-108) = decide (1 ≤ countLit b [-108]) := by
  change literal b (-108) = decide (1 ≤ countLit b [-108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-108) <;> decide
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
theorem meaningNeg96 (b : Nat → Bool) : literal (valuationOf b) (-96) = decide (1 ≤ countLit b [-96]) := by
  change literal b (-96) = decide (1 ≤ countLit b [-96])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-96) <;> decide
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
theorem meaningNeg89 (b : Nat → Bool) : literal (valuationOf b) (-89) = decide (1 ≤ countLit b [-89]) := by
  change literal b (-89) = decide (1 ≤ countLit b [-89])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-89) <;> decide
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
theorem meaningNeg78 (b : Nat → Bool) : literal (valuationOf b) (-78) = decide (1 ≤ countLit b [-78]) := by
  change literal b (-78) = decide (1 ≤ countLit b [-78])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-78) <;> decide
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
theorem meaningNeg54 (b : Nat → Bool) : literal (valuationOf b) (-54) = decide (1 ≤ countLit b [-54]) := by
  change literal b (-54) = decide (1 ≤ countLit b [-54])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-54) <;> decide
theorem meaningNeg51 (b : Nat → Bool) : literal (valuationOf b) (-51) = decide (1 ≤ countLit b [-51]) := by
  change literal b (-51) = decide (1 ≤ countLit b [-51])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-51) <;> decide
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
theorem meaningNeg46 (b : Nat → Bool) : literal (valuationOf b) (-46) = decide (1 ≤ countLit b [-46]) := by
  change literal b (-46) = decide (1 ≤ countLit b [-46])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-46) <;> decide
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
theorem meaningNeg35 (b : Nat → Bool) : literal (valuationOf b) (-35) = decide (1 ≤ countLit b [-35]) := by
  change literal b (-35) = decide (1 ≤ countLit b [-35])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-35) <;> decide
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
theorem meaning136 (b : Nat → Bool) : literal (valuationOf b) (136) = decide (1 ≤ countLit b [136]) := by
  change literal b (136) = decide (1 ≤ countLit b [136])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (136) <;> decide
theorem meaning155 (b : Nat → Bool) : literal (valuationOf b) (155) = decide (1 ≤ countLit b [155]) := by
  change literal b (155) = decide (1 ≤ countLit b [155])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (155) <;> decide
theorem meaning158 (b : Nat → Bool) : literal (valuationOf b) (158) = decide (1 ≤ countLit b [158]) := by
  change literal b (158) = decide (1 ≤ countLit b [158])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (158) <;> decide
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
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
theorem meaning169 (b : Nat → Bool) : literal (valuationOf b) (169) = decide (1 ≤ countLit b [169]) := by
  change literal b (169) = decide (1 ≤ countLit b [169])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (169) <;> decide
theorem meaning175 (b : Nat → Bool) : literal (valuationOf b) (175) = decide (1 ≤ countLit b [175]) := by
  change literal b (175) = decide (1 ≤ countLit b [175])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (175) <;> decide
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
theorem meaning191 (b : Nat → Bool) : literal (valuationOf b) (191) = decide (1 ≤ countLit b [191]) := by
  change literal b (191) = decide (1 ≤ countLit b [191])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (191) <;> decide
theorem meaning196 (b : Nat → Bool) : literal (valuationOf b) (196) = decide (1 ≤ countLit b [196]) := by
  change literal b (196) = decide (1 ≤ countLit b [196])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (196) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning320 (b : Nat → Bool) : literal (valuationOf b) 320 = decide (2 ≤ count319 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning426 (b : Nat → Bool) : literal (valuationOf b) 426 = decide (2 ≤ count425 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning1289 (b : Nat → Bool) : literal (valuationOf b) 1289 = decide (1 ≤ count1289 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (1 ≤ count1291 b) := rfl
theorem meaning1294 (b : Nat → Bool) : literal (valuationOf b) 1294 = decide (1 ≤ count1294 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (1 ≤ count1296 b) := rfl
theorem meaning1299 (b : Nat → Bool) : literal (valuationOf b) 1299 = decide (1 ≤ count1299 b) := rfl
theorem meaning1300 (b : Nat → Bool) : literal (valuationOf b) 1300 = decide (2 ≤ count1299 b) := rfl
theorem meaning1305 (b : Nat → Bool) : literal (valuationOf b) 1305 = decide (1 ≤ count1305 b) := rfl
theorem meaning1307 (b : Nat → Bool) : literal (valuationOf b) 1307 = decide (1 ≤ count1307 b) := rfl
theorem meaning1310 (b : Nat → Bool) : literal (valuationOf b) 1310 = decide (1 ≤ count1310 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (2 ≤ count1310 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (1 ≤ count1312 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (1 ≤ count1314 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (2 ≤ count1314 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (1 ≤ count1318 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (2 ≤ count1318 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (3 ≤ count1325 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (1 ≤ count1338 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (2 ≤ count1340 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (1 ≤ count1343 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (1 ≤ count1345 b) := rfl
theorem meaning1348 (b : Nat → Bool) : literal (valuationOf b) 1348 = decide (1 ≤ count1348 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (2 ≤ count1348 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (1 ≤ count1354 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (1 ≤ count1356 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (2 ≤ count1356 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (1 ≤ count1359 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (2 ≤ count1359 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (1 ≤ count1361 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (2 ≤ count1361 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (1 ≤ count1363 b) := rfl
theorem meaning1364 (b : Nat → Bool) : literal (valuationOf b) 1364 = decide (2 ≤ count1363 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (3 ≤ count1363 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (1 ≤ count1367 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (2 ≤ count1367 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (3 ≤ count1367 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (4 ≤ count1367 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (5 ≤ count1367 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (2 ≤ count1374 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (3 ≤ count1374 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (4 ≤ count1374 b) := rfl
theorem meaning1378 (b : Nat → Bool) : literal (valuationOf b) 1378 = decide (5 ≤ count1374 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (6 ≤ count1374 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (5 ≤ count1387 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (6 ≤ count1387 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (7 ≤ count1387 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (8 ≤ count1387 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (9 ≤ count1387 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (1 ≤ count1400 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (1 ≤ count1402 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (1 ≤ count1405 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (1 ≤ count1407 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (2 ≤ count1407 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (1 ≤ count1410 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (2 ≤ count1410 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (3 ≤ count1410 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (1 ≤ count1416 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (1 ≤ count1418 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (1 ≤ count1421 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (2 ≤ count1421 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (1 ≤ count1423 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (2 ≤ count1423 b) := rfl
theorem meaning1425 (b : Nat → Bool) : literal (valuationOf b) 1425 = decide (1 ≤ count1425 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (2 ≤ count1425 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (1 ≤ count1429 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (2 ≤ count1429 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (3 ≤ count1429 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (1 ≤ count1436 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (2 ≤ count1436 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (3 ≤ count1436 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (4 ≤ count1436 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (1 ≤ count1449 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (2 ≤ count1449 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (1 ≤ count1451 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (2 ≤ count1451 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (3 ≤ count1451 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (1 ≤ count1454 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (2 ≤ count1454 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (1 ≤ count1456 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (2 ≤ count1456 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (1 ≤ count1458 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (2 ≤ count1458 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (3 ≤ count1458 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (1 ≤ count1462 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (2 ≤ count1462 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (3 ≤ count1462 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (4 ≤ count1462 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (1 ≤ count1469 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (2 ≤ count1469 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (1 ≤ count1471 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (2 ≤ count1471 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (3 ≤ count1471 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (1 ≤ count1474 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (2 ≤ count1474 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (1 ≤ count1476 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (2 ≤ count1476 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (1 ≤ count1478 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (2 ≤ count1478 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (3 ≤ count1478 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (1 ≤ count1482 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (2 ≤ count1482 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (3 ≤ count1482 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (4 ≤ count1482 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (3 ≤ count1489 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (4 ≤ count1489 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (5 ≤ count1489 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (6 ≤ count1489 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (4 ≤ count1502 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (5 ≤ count1502 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (6 ≤ count1502 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (7 ≤ count1502 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (8 ≤ count1502 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (13 ≤ count1515 b) := rfl
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
end Snake9.Regrowth.E112190
