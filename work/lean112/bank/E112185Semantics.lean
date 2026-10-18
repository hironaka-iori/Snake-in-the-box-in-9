import E112185Data
namespace Snake9.Regrowth.E112185
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 108 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 4 then decide (InPath q (2 : Vertex)) else (if i < 5 then decide (InPath q (3 : Vertex)) else decide (InPath q (5 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (6 : Vertex)) else (if i < 8 then decide (InPath q (11 : Vertex)) else decide (InPath q (13 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (15 : Vertex)) else decide (InPath q (16 : Vertex))) else (if i < 12 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (19 : Vertex)) else (if i < 15 then decide (InPath q (22 : Vertex)) else decide (InPath q (24 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex))) else (if i < 19 then decide (InPath q (30 : Vertex)) else decide (InPath q (31 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (66 : Vertex)) else (if i < 22 then decide (InPath q (68 : Vertex)) else decide (InPath q (69 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (70 : Vertex)) else decide (InPath q (75 : Vertex))) else (if i < 26 then decide (InPath q (78 : Vertex)) else decide (InPath q (84 : Vertex))))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then decide (InPath q (85 : Vertex)) else (if i < 29 then decide (InPath q (87 : Vertex)) else decide (InPath q (89 : Vertex)))) else (if i < 31 then decide (InPath q (91 : Vertex)) else (if i < 32 then decide (InPath q (95 : Vertex)) else decide (InPath q (160 : Vertex))))) else (if i < 36 then (if i < 34 then decide (InPath q (161 : Vertex)) else (if i < 35 then decide (InPath q (165 : Vertex)) else decide (InPath q (171 : Vertex)))) else (if i < 38 then (if i < 37 then decide (InPath q (173 : Vertex)) else decide (InPath q (175 : Vertex))) else (if i < 39 then decide (InPath q (176 : Vertex)) else decide (InPath q (177 : Vertex)))))) else (if i < 47 then (if i < 43 then (if i < 41 then decide (InPath q (178 : Vertex)) else (if i < 42 then decide (InPath q (179 : Vertex)) else decide (InPath q (182 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (184 : Vertex)) else decide (InPath q (188 : Vertex))) else (if i < 46 then decide (InPath q (189 : Vertex)) else decide (InPath q (190 : Vertex))))) else (if i < 50 then (if i < 48 then decide (InPath q (191 : Vertex)) else (if i < 49 then decide (InPath q (245 : Vertex)) else decide (InPath q (247 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (248 : Vertex)) else decide (InPath q (249 : Vertex))) else (if i < 53 then decide (InPath q (251 : Vertex)) else decide (InPath q (255 : Vertex)))))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then decide (InPath q (258 : Vertex)) else (if i < 56 then decide (InPath q (259 : Vertex)) else decide (InPath q (260 : Vertex)))) else (if i < 58 then decide (InPath q (261 : Vertex)) else (if i < 59 then decide (InPath q (266 : Vertex)) else decide (InPath q (267 : Vertex))))) else (if i < 63 then (if i < 61 then decide (InPath q (268 : Vertex)) else (if i < 62 then decide (InPath q (270 : Vertex)) else decide (InPath q (272 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (276 : Vertex)) else decide (InPath q (277 : Vertex))) else (if i < 66 then decide (InPath q (279 : Vertex)) else decide (InPath q (280 : Vertex)))))) else (if i < 74 then (if i < 70 then (if i < 68 then decide (InPath q (281 : Vertex)) else (if i < 69 then decide (InPath q (283 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 72 then (if i < 71 then decide (InPath q (326 : Vertex)) else decide (InPath q (327 : Vertex))) else (if i < 73 then decide (InPath q (331 : Vertex)) else decide (InPath q (333 : Vertex))))) else (if i < 77 then (if i < 75 then decide (InPath q (335 : Vertex)) else (if i < 76 then decide (InPath q (340 : Vertex)) else decide (InPath q (348 : Vertex)))) else (if i < 79 then (if i < 78 then decide (InPath q (349 : Vertex)) else decide (InPath q (384 : Vertex))) else (if i < 80 then decide (InPath q (387 : Vertex)) else decide (InPath q (400 : Vertex))))))) else (if i < 94 then (if i < 87 then (if i < 84 then (if i < 82 then decide (InPath q (401 : Vertex)) else (if i < 83 then decide (InPath q (403 : Vertex)) else decide (InPath q (419 : Vertex)))) else (if i < 85 then decide (InPath q (421 : Vertex)) else (if i < 86 then decide (InPath q (427 : Vertex)) else decide (InPath q (432 : Vertex))))) else (if i < 90 then (if i < 88 then decide (InPath q (436 : Vertex)) else (if i < 89 then decide (InPath q (437 : Vertex)) else decide (InPath q (439 : Vertex)))) else (if i < 92 then (if i < 91 then decide (InPath q (441 : Vertex)) else decide (InPath q (443 : Vertex))) else (if i < 93 then decide (InPath q (447 : Vertex)) else decide (InPath q (450 : Vertex)))))) else (if i < 101 then (if i < 97 then (if i < 95 then decide (InPath q (451 : Vertex)) else (if i < 96 then decide (InPath q (452 : Vertex)) else decide (InPath q (453 : Vertex)))) else (if i < 99 then (if i < 98 then decide (InPath q (458 : Vertex)) else decide (InPath q (459 : Vertex))) else (if i < 100 then decide (InPath q (460 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 104 then (if i < 102 then decide (InPath q (464 : Vertex)) else (if i < 103 then decide (InPath q (468 : Vertex)) else decide (InPath q (469 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (471 : Vertex)) else decide (InPath q (472 : Vertex))) else (if i < 107 then decide (InPath q (473 : Vertex)) else decide (InPath q (475 : Vertex))))))))) else (if i < 162 then (if i < 135 then (if i < 121 then (if i < 114 then (if i < 111 then (if i < 109 then decide (InPath q (479 : Vertex)) else (if i < 110 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 112 then decide (BallClauseLogic.Endpoint q (2 : Vertex)) else (if i < 113 then decide (BallClauseLogic.Endpoint q (3 : Vertex)) else decide (BallClauseLogic.Endpoint q (5 : Vertex))))) else (if i < 117 then (if i < 115 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else (if i < 116 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else decide (BallClauseLogic.Endpoint q (13 : Vertex)))) else (if i < 119 then (if i < 118 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else decide (BallClauseLogic.Endpoint q (16 : Vertex))) else (if i < 120 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex)))))) else (if i < 128 then (if i < 124 then (if i < 122 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else (if i < 123 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (24 : Vertex)))) else (if i < 126 then (if i < 125 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex))) else (if i < 127 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else decide (BallClauseLogic.Endpoint q (31 : Vertex))))) else (if i < 131 then (if i < 129 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else (if i < 130 then decide (BallClauseLogic.Endpoint q (68 : Vertex)) else decide (BallClauseLogic.Endpoint q (69 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (75 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (78 : Vertex)) else decide (BallClauseLogic.Endpoint q (84 : Vertex))))))) else (if i < 148 then (if i < 141 then (if i < 138 then (if i < 136 then decide (BallClauseLogic.Endpoint q (85 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (87 : Vertex)) else decide (BallClauseLogic.Endpoint q (89 : Vertex)))) else (if i < 139 then decide (BallClauseLogic.Endpoint q (91 : Vertex)) else (if i < 140 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex))))) else (if i < 144 then (if i < 142 then decide (BallClauseLogic.Endpoint q (161 : Vertex)) else (if i < 143 then decide (BallClauseLogic.Endpoint q (165 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex)))) else (if i < 146 then (if i < 145 then decide (BallClauseLogic.Endpoint q (173 : Vertex)) else decide (BallClauseLogic.Endpoint q (175 : Vertex))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (176 : Vertex)) else decide (BallClauseLogic.Endpoint q (177 : Vertex)))))) else (if i < 155 then (if i < 151 then (if i < 149 then decide (BallClauseLogic.Endpoint q (178 : Vertex)) else (if i < 150 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex)))) else (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (184 : Vertex)) else decide (BallClauseLogic.Endpoint q (188 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (190 : Vertex))))) else (if i < 158 then (if i < 156 then decide (BallClauseLogic.Endpoint q (191 : Vertex)) else (if i < 157 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else decide (BallClauseLogic.Endpoint q (247 : Vertex)))) else (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (248 : Vertex)) else decide (BallClauseLogic.Endpoint q (249 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex)))))))) else (if i < 189 then (if i < 175 then (if i < 168 then (if i < 165 then (if i < 163 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex)))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex))))) else (if i < 171 then (if i < 169 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else (if i < 170 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else decide (BallClauseLogic.Endpoint q (272 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (277 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (280 : Vertex)))))) else (if i < 182 then (if i < 178 then (if i < 176 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else (if i < 177 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (326 : Vertex)) else decide (BallClauseLogic.Endpoint q (327 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (331 : Vertex)) else decide (BallClauseLogic.Endpoint q (333 : Vertex))))) else (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (335 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (340 : Vertex)) else decide (BallClauseLogic.Endpoint q (348 : Vertex)))) else (if i < 187 then (if i < 186 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 188 then decide (BallClauseLogic.Endpoint q (387 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex))))))) else (if i < 203 then (if i < 196 then (if i < 192 then (if i < 190 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else (if i < 191 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (419 : Vertex)))) else (if i < 194 then (if i < 193 then decide (BallClauseLogic.Endpoint q (421 : Vertex)) else decide (BallClauseLogic.Endpoint q (427 : Vertex))) else (if i < 195 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else decide (BallClauseLogic.Endpoint q (436 : Vertex))))) else (if i < 199 then (if i < 197 then decide (BallClauseLogic.Endpoint q (437 : Vertex)) else (if i < 198 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else decide (BallClauseLogic.Endpoint q (441 : Vertex)))) else (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (450 : Vertex)) else decide (BallClauseLogic.Endpoint q (451 : Vertex)))))) else (if i < 210 then (if i < 206 then (if i < 204 then decide (BallClauseLogic.Endpoint q (452 : Vertex)) else (if i < 205 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else decide (BallClauseLogic.Endpoint q (458 : Vertex)))) else (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (459 : Vertex)) else decide (BallClauseLogic.Endpoint q (460 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 213 then (if i < 211 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else (if i < 212 then decide (BallClauseLogic.Endpoint q (469 : Vertex)) else decide (BallClauseLogic.Endpoint q (471 : Vertex)))) else (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
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
def count267 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count299 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count305 (b : Nat → Bool) : Nat := countLit b [155, 157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count309 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162]
def count313 (b : Nat → Bool) : Nat := countLit b [155, 157, 158, 159, 160, 161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162]
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
def count427 (b : Nat → Bool) : Nat := countLit b [109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216]
def count429 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count431 (b : Nat → Bool) : Nat := countLit b [1, 4, 5]
def count434 (b : Nat → Bool) : Nat := countLit b [6, 9]
def count436 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count438 (b : Nat → Bool) : Nat := countLit b [6, 9, 11, 12]
def count442 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12]
def count449 (b : Nat → Bool) : Nat := countLit b [17, 18]
def count451 (b : Nat → Bool) : Nat := countLit b [15, 17, 18]
def count454 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count456 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count458 (b : Nat → Bool) : Nat := countLit b [20, 21, 24, 25]
def count462 (b : Nat → Bool) : Nat := countLit b [15, 17, 18, 20, 21, 24, 25]
def count469 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12, 15, 17, 18, 20, 21, 24, 25]
def count483 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count485 (b : Nat → Bool) : Nat := countLit b [27, 29, 31]
def count488 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count490 (b : Nat → Bool) : Nat := countLit b [37, 39]
def count492 (b : Nat → Bool) : Nat := countLit b [32, 34, 37, 39]
def count496 (b : Nat → Bool) : Nat := countLit b [27, 29, 31, 32, 34, 37, 39]
def count503 (b : Nat → Bool) : Nat := countLit b [43, 45]
def count505 (b : Nat → Bool) : Nat := countLit b [40, 43, 45]
def count508 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count510 (b : Nat → Bool) : Nat := countLit b [51, 53]
def count512 (b : Nat → Bool) : Nat := countLit b [46, 48, 51, 53]
def count516 (b : Nat → Bool) : Nat := countLit b [40, 43, 45, 46, 48, 51, 53]
def count523 (b : Nat → Bool) : Nat := countLit b [27, 29, 31, 32, 34, 37, 39, 40, 43, 45, 46, 48, 51, 53]
def count537 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12, 15, 17, 18, 20, 21, 24, 25, 27, 29, 31, 32, 34, 37, 39, 40, 43, 45, 46, 48, 51, 53]
def count565 (b : Nat → Bool) : Nat := countLit b [56, 59]
def count567 (b : Nat → Bool) : Nat := countLit b [54, 56, 59]
def count570 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count572 (b : Nat → Bool) : Nat := countLit b [64, 67]
def count574 (b : Nat → Bool) : Nat := countLit b [61, 62, 64, 67]
def count578 (b : Nat → Bool) : Nat := countLit b [54, 56, 59, 61, 62, 64, 67]
def count585 (b : Nat → Bool) : Nat := countLit b [70, 74]
def count587 (b : Nat → Bool) : Nat := countLit b [69, 70, 74]
def count590 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count592 (b : Nat → Bool) : Nat := countLit b [78, 79]
def count594 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 79]
def count598 (b : Nat → Bool) : Nat := countLit b [69, 70, 74, 75, 77, 78, 79]
def count605 (b : Nat → Bool) : Nat := countLit b [54, 56, 59, 61, 62, 64, 67, 69, 70, 74, 75, 77, 78, 79]
def count619 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count621 (b : Nat → Bool) : Nat := countLit b [81, 85, 86]
def count624 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count626 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count628 (b : Nat → Bool) : Nat := countLit b [88, 90, 92, 93]
def count632 (b : Nat → Bool) : Nat := countLit b [81, 85, 86, 88, 90, 92, 93]
def count639 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count641 (b : Nat → Bool) : Nat := countLit b [95, 98, 100]
def count644 (b : Nat → Bool) : Nat := countLit b [101, 103]
def count646 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count648 (b : Nat → Bool) : Nat := countLit b [101, 103, 106, 108]
def count652 (b : Nat → Bool) : Nat := countLit b [95, 98, 100, 101, 103, 106, 108]
def count659 (b : Nat → Bool) : Nat := countLit b [81, 85, 86, 88, 90, 92, 93, 95, 98, 100, 101, 103, 106, 108]
def count673 (b : Nat → Bool) : Nat := countLit b [54, 56, 59, 61, 62, 64, 67, 69, 70, 74, 75, 77, 78, 79, 81, 85, 86, 88, 90, 92, 93, 95, 98, 100, 101, 103, 106, 108]
def count701 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12, 15, 17, 18, 20, 21, 24, 25, 27, 29, 31, 32, 34, 37, 39, 40, 43, 45, 46, 48, 51, 53, 54, 56, 59, 61, 62, 64, 67, 69, 70, 74, 75, 77, 78, 79, 81, 85, 86, 88, 90, 92, 93, 95, 98, 100, 101, 103, 106, 108]
def count743 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count745 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5]
def count748 (b : Nat → Bool) : Nat := countLit b [-6, -9]
def count750 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count752 (b : Nat → Bool) : Nat := countLit b [-6, -9, -11, -12]
def count756 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12]
def count763 (b : Nat → Bool) : Nat := countLit b [-17, -18]
def count765 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18]
def count768 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count770 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count772 (b : Nat → Bool) : Nat := countLit b [-20, -21, -24, -25]
def count776 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18, -20, -21, -24, -25]
def count783 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]
def count797 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count799 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31]
def count802 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count804 (b : Nat → Bool) : Nat := countLit b [-37, -39]
def count806 (b : Nat → Bool) : Nat := countLit b [-32, -34, -37, -39]
def count810 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31, -32, -34, -37, -39]
def count817 (b : Nat → Bool) : Nat := countLit b [-43, -45]
def count819 (b : Nat → Bool) : Nat := countLit b [-40, -43, -45]
def count822 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count824 (b : Nat → Bool) : Nat := countLit b [-51, -53]
def count826 (b : Nat → Bool) : Nat := countLit b [-46, -48, -51, -53]
def count830 (b : Nat → Bool) : Nat := countLit b [-40, -43, -45, -46, -48, -51, -53]
def count837 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]
def count851 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]
def count867 (b : Nat → Bool) : Nat := countLit b [-56, -59]
def count869 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59]
def count872 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count874 (b : Nat → Bool) : Nat := countLit b [-64, -67]
def count876 (b : Nat → Bool) : Nat := countLit b [-61, -62, -64, -67]
def count880 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59, -61, -62, -64, -67]
def count887 (b : Nat → Bool) : Nat := countLit b [-70, -74]
def count889 (b : Nat → Bool) : Nat := countLit b [-69, -70, -74]
def count892 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count894 (b : Nat → Bool) : Nat := countLit b [-78, -79]
def count896 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -79]
def count900 (b : Nat → Bool) : Nat := countLit b [-69, -70, -74, -75, -77, -78, -79]
def count907 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79]
def count921 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count923 (b : Nat → Bool) : Nat := countLit b [-81, -85, -86]
def count926 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count928 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count930 (b : Nat → Bool) : Nat := countLit b [-88, -90, -92, -93]
def count934 (b : Nat → Bool) : Nat := countLit b [-81, -85, -86, -88, -90, -92, -93]
def count941 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count943 (b : Nat → Bool) : Nat := countLit b [-95, -98, -100]
def count946 (b : Nat → Bool) : Nat := countLit b [-101, -103]
def count948 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count950 (b : Nat → Bool) : Nat := countLit b [-101, -103, -106, -108]
def count954 (b : Nat → Bool) : Nat := countLit b [-95, -98, -100, -101, -103, -106, -108]
def count961 (b : Nat → Bool) : Nat := countLit b [-81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]
def count975 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]
def count991 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25, -27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53, -54, -56, -59, -61, -62, -64, -67, -69, -70, -74, -75, -77, -78, -79, -81, -85, -86, -88, -90, -92, -93, -95, -98, -100, -101, -103, -106, -108]
def count1007 (b : Nat → Bool) : Nat := countLit b [3, 7]
def count1009 (b : Nat → Bool) : Nat := countLit b [2, 3, 7]
def count1012 (b : Nat → Bool) : Nat := countLit b [10, 13]
def count1014 (b : Nat → Bool) : Nat := countLit b [8, 10, 13]
def count1017 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13]
def count1023 (b : Nat → Bool) : Nat := countLit b [16, 19]
def count1025 (b : Nat → Bool) : Nat := countLit b [14, 16, 19]
def count1028 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count1030 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count1032 (b : Nat → Bool) : Nat := countLit b [22, 23, 26, 28]
def count1036 (b : Nat → Bool) : Nat := countLit b [14, 16, 19, 22, 23, 26, 28]
def count1043 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13, 14, 16, 19, 22, 23, 26, 28]
def count1056 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count1058 (b : Nat → Bool) : Nat := countLit b [30, 33, 35]
def count1061 (b : Nat → Bool) : Nat := countLit b [38, 41]
def count1063 (b : Nat → Bool) : Nat := countLit b [36, 38, 41]
def count1066 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 36, 38, 41]
def count1072 (b : Nat → Bool) : Nat := countLit b [44, 47]
def count1074 (b : Nat → Bool) : Nat := countLit b [42, 44, 47]
def count1077 (b : Nat → Bool) : Nat := countLit b [49, 50]
def count1079 (b : Nat → Bool) : Nat := countLit b [52, 55]
def count1081 (b : Nat → Bool) : Nat := countLit b [49, 50, 52, 55]
def count1085 (b : Nat → Bool) : Nat := countLit b [42, 44, 47, 49, 50, 52, 55]
def count1092 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 36, 38, 41, 42, 44, 47, 49, 50, 52, 55]
def count1105 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13, 14, 16, 19, 22, 23, 26, 28, 30, 33, 35, 36, 38, 41, 42, 44, 47, 49, 50, 52, 55]
def count1131 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count1133 (b : Nat → Bool) : Nat := countLit b [57, 58, 60]
def count1136 (b : Nat → Bool) : Nat := countLit b [65, 66]
def count1138 (b : Nat → Bool) : Nat := countLit b [63, 65, 66]
def count1141 (b : Nat → Bool) : Nat := countLit b [57, 58, 60, 63, 65, 66]
def count1147 (b : Nat → Bool) : Nat := countLit b [71, 72]
def count1149 (b : Nat → Bool) : Nat := countLit b [68, 71, 72]
def count1152 (b : Nat → Bool) : Nat := countLit b [73, 76]
def count1154 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count1156 (b : Nat → Bool) : Nat := countLit b [73, 76, 80, 82]
def count1160 (b : Nat → Bool) : Nat := countLit b [68, 71, 72, 73, 76, 80, 82]
def count1167 (b : Nat → Bool) : Nat := countLit b [57, 58, 60, 63, 65, 66, 68, 71, 72, 73, 76, 80, 82]
def count1180 (b : Nat → Bool) : Nat := countLit b [84, 87]
def count1182 (b : Nat → Bool) : Nat := countLit b [83, 84, 87]
def count1185 (b : Nat → Bool) : Nat := countLit b [91, 94]
def count1187 (b : Nat → Bool) : Nat := countLit b [89, 91, 94]
def count1190 (b : Nat → Bool) : Nat := countLit b [83, 84, 87, 89, 91, 94]
def count1196 (b : Nat → Bool) : Nat := countLit b [97, 99]
def count1198 (b : Nat → Bool) : Nat := countLit b [96, 97, 99]
def count1201 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count1203 (b : Nat → Bool) : Nat := countLit b [105, 107]
def count1205 (b : Nat → Bool) : Nat := countLit b [102, 104, 105, 107]
def count1209 (b : Nat → Bool) : Nat := countLit b [96, 97, 99, 102, 104, 105, 107]
def count1216 (b : Nat → Bool) : Nat := countLit b [83, 84, 87, 89, 91, 94, 96, 97, 99, 102, 104, 105, 107]
def count1229 (b : Nat → Bool) : Nat := countLit b [57, 58, 60, 63, 65, 66, 68, 71, 72, 73, 76, 80, 82, 83, 84, 87, 89, 91, 94, 96, 97, 99, 102, 104, 105, 107]
def count1255 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13, 14, 16, 19, 22, 23, 26, 28, 30, 33, 35, 36, 38, 41, 42, 44, 47, 49, 50, 52, 55, 57, 58, 60, 63, 65, 66, 68, 71, 72, 73, 76, 80, 82, 83, 84, 87, 89, 91, 94, 96, 97, 99, 102, 104, 105, 107]
def count1297 (b : Nat → Bool) : Nat := countLit b [-3, -7]
def count1299 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7]
def count1302 (b : Nat → Bool) : Nat := countLit b [-10, -13]
def count1304 (b : Nat → Bool) : Nat := countLit b [-8, -10, -13]
def count1307 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13]
def count1313 (b : Nat → Bool) : Nat := countLit b [-16, -19]
def count1315 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19]
def count1318 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count1320 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count1322 (b : Nat → Bool) : Nat := countLit b [-22, -23, -26, -28]
def count1326 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19, -22, -23, -26, -28]
def count1333 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28]
def count1345 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count1347 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35]
def count1350 (b : Nat → Bool) : Nat := countLit b [-38, -41]
def count1352 (b : Nat → Bool) : Nat := countLit b [-36, -38, -41]
def count1355 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -36, -38, -41]
def count1361 (b : Nat → Bool) : Nat := countLit b [-44, -47]
def count1363 (b : Nat → Bool) : Nat := countLit b [-42, -44, -47]
def count1366 (b : Nat → Bool) : Nat := countLit b [-49, -50]
def count1368 (b : Nat → Bool) : Nat := countLit b [-52, -55]
def count1370 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52, -55]
def count1374 (b : Nat → Bool) : Nat := countLit b [-42, -44, -47, -49, -50, -52, -55]
def count1381 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55]
def count1393 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55]
def count1405 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count1407 (b : Nat → Bool) : Nat := countLit b [-57, -58, -60]
def count1410 (b : Nat → Bool) : Nat := countLit b [-65, -66]
def count1412 (b : Nat → Bool) : Nat := countLit b [-63, -65, -66]
def count1415 (b : Nat → Bool) : Nat := countLit b [-57, -58, -60, -63, -65, -66]
def count1421 (b : Nat → Bool) : Nat := countLit b [-71, -72]
def count1423 (b : Nat → Bool) : Nat := countLit b [-68, -71, -72]
def count1426 (b : Nat → Bool) : Nat := countLit b [-73, -76]
def count1428 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count1430 (b : Nat → Bool) : Nat := countLit b [-73, -76, -80, -82]
def count1434 (b : Nat → Bool) : Nat := countLit b [-68, -71, -72, -73, -76, -80, -82]
def count1441 (b : Nat → Bool) : Nat := countLit b [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82]
def count1453 (b : Nat → Bool) : Nat := countLit b [-84, -87]
def count1455 (b : Nat → Bool) : Nat := countLit b [-83, -84, -87]
def count1458 (b : Nat → Bool) : Nat := countLit b [-91, -94]
def count1460 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94]
def count1463 (b : Nat → Bool) : Nat := countLit b [-83, -84, -87, -89, -91, -94]
def count1469 (b : Nat → Bool) : Nat := countLit b [-97, -99]
def count1471 (b : Nat → Bool) : Nat := countLit b [-96, -97, -99]
def count1474 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count1476 (b : Nat → Bool) : Nat := countLit b [-105, -107]
def count1478 (b : Nat → Bool) : Nat := countLit b [-102, -104, -105, -107]
def count1482 (b : Nat → Bool) : Nat := countLit b [-96, -97, -99, -102, -104, -105, -107]
def count1489 (b : Nat → Bool) : Nat := countLit b [-83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107]
def count1501 (b : Nat → Bool) : Nat := countLit b [-57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82, -83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107]
def count1513 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -30, -33, -35, -36, -38, -41, -42, -44, -47, -49, -50, -52, -55, -57, -58, -60, -63, -65, -66, -68, -71, -72, -73, -76, -80, -82, -83, -84, -87, -89, -91, -94, -96, -97, -99, -102, -104, -105, -107]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 762 then (if i < 381 then (if i < 190 then (if i < 95 then (if i < 47 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 17 then (if i < 14 then (if i < 12 then b 11 else (if i < 13 then b 12 else b 13)) else (if i < 15 then b 14 else (if i < 16 then b 15 else b 16))) else (if i < 20 then (if i < 18 then b 17 else (if i < 19 then b 18 else b 19)) else (if i < 21 then b 20 else (if i < 22 then b 21 else b 22))))) else (if i < 35 then (if i < 29 then (if i < 26 then (if i < 24 then b 23 else (if i < 25 then b 24 else b 25)) else (if i < 27 then b 26 else (if i < 28 then b 27 else b 28))) else (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)))) else (if i < 41 then (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 39 then b 38 else (if i < 40 then b 39 else b 40))) else (if i < 44 then (if i < 42 then b 41 else (if i < 43 then b 42 else b 43)) else (if i < 45 then b 44 else (if i < 46 then b 45 else b 46)))))) else (if i < 71 then (if i < 59 then (if i < 53 then (if i < 50 then (if i < 48 then b 47 else (if i < 49 then b 48 else b 49)) else (if i < 51 then b 50 else (if i < 52 then b 51 else b 52))) else (if i < 56 then (if i < 54 then b 53 else (if i < 55 then b 54 else b 55)) else (if i < 57 then b 56 else (if i < 58 then b 57 else b 58)))) else (if i < 65 then (if i < 62 then (if i < 60 then b 59 else (if i < 61 then b 60 else b 61)) else (if i < 63 then b 62 else (if i < 64 then b 63 else b 64))) else (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 69 then b 68 else (if i < 70 then b 69 else b 70))))) else (if i < 83 then (if i < 77 then (if i < 74 then (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)) else (if i < 75 then b 74 else (if i < 76 then b 75 else b 76))) else (if i < 80 then (if i < 78 then b 77 else (if i < 79 then b 78 else b 79)) else (if i < 81 then b 80 else (if i < 82 then b 81 else b 82)))) else (if i < 89 then (if i < 86 then (if i < 84 then b 83 else (if i < 85 then b 84 else b 85)) else (if i < 87 then b 86 else (if i < 88 then b 87 else b 88))) else (if i < 92 then (if i < 90 then b 89 else (if i < 91 then b 90 else b 91)) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))))))) else (if i < 142 then (if i < 118 then (if i < 106 then (if i < 100 then (if i < 97 then (if i < 96 then b 95 else b 96) else (if i < 98 then b 97 else (if i < 99 then b 98 else b 99))) else (if i < 103 then (if i < 101 then b 100 else (if i < 102 then b 101 else b 102)) else (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)))) else (if i < 112 then (if i < 109 then (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)) else (if i < 110 then b 109 else (if i < 111 then b 110 else b 111))) else (if i < 115 then (if i < 113 then b 112 else (if i < 114 then b 113 else b 114)) else (if i < 116 then b 115 else (if i < 117 then b 116 else b 117))))) else (if i < 130 then (if i < 124 then (if i < 121 then (if i < 119 then b 118 else (if i < 120 then b 119 else b 120)) else (if i < 122 then b 121 else (if i < 123 then b 122 else b 123))) else (if i < 127 then (if i < 125 then b 124 else (if i < 126 then b 125 else b 126)) else (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)))) else (if i < 136 then (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 134 then b 133 else (if i < 135 then b 134 else b 135))) else (if i < 139 then (if i < 137 then b 136 else (if i < 138 then b 137 else b 138)) else (if i < 140 then b 139 else (if i < 141 then b 140 else b 141)))))) else (if i < 166 then (if i < 154 then (if i < 148 then (if i < 145 then (if i < 143 then b 142 else (if i < 144 then b 143 else b 144)) else (if i < 146 then b 145 else (if i < 147 then b 146 else b 147))) else (if i < 151 then (if i < 149 then b 148 else (if i < 150 then b 149 else b 150)) else (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)))) else (if i < 160 then (if i < 157 then (if i < 155 then b 154 else (if i < 156 then b 155 else b 156)) else (if i < 158 then b 157 else (if i < 159 then b 158 else b 159))) else (if i < 163 then (if i < 161 then b 160 else (if i < 162 then b 161 else b 162)) else (if i < 164 then b 163 else (if i < 165 then b 164 else b 165))))) else (if i < 178 then (if i < 172 then (if i < 169 then (if i < 167 then b 166 else (if i < 168 then b 167 else b 168)) else (if i < 170 then b 169 else (if i < 171 then b 170 else b 171))) else (if i < 175 then (if i < 173 then b 172 else (if i < 174 then b 173 else b 174)) else (if i < 176 then b 175 else (if i < 177 then b 176 else b 177)))) else (if i < 184 then (if i < 181 then (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)) else (if i < 182 then b 181 else (if i < 183 then b 182 else b 183))) else (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 188 then b 187 else (if i < 189 then b 188 else b 189)))))))) else (if i < 285 then (if i < 237 then (if i < 213 then (if i < 201 then (if i < 195 then (if i < 192 then (if i < 191 then b 190 else b 191) else (if i < 193 then b 192 else (if i < 194 then b 193 else b 194))) else (if i < 198 then (if i < 196 then b 195 else (if i < 197 then b 196 else b 197)) else (if i < 199 then b 198 else (if i < 200 then b 199 else b 200)))) else (if i < 207 then (if i < 204 then (if i < 202 then b 201 else (if i < 203 then b 202 else b 203)) else (if i < 205 then b 204 else (if i < 206 then b 205 else b 206))) else (if i < 210 then (if i < 208 then b 207 else (if i < 209 then b 208 else b 209)) else (if i < 211 then b 210 else (if i < 212 then b 211 else b 212))))) else (if i < 225 then (if i < 219 then (if i < 216 then (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)) else (if i < 217 then b 216 else (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b)))) else (if i < 222 then (if i < 220 then decide (1 ≤ count219 b) else (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b))) else (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b))))) else (if i < 231 then (if i < 228 then (if i < 226 then decide (1 ≤ count225 b) else (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b))) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b)))) else (if i < 234 then (if i < 232 then decide (1 ≤ count231 b) else (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b))) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b))))))) else (if i < 261 then (if i < 249 then (if i < 243 then (if i < 240 then (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b))) else (if i < 241 then decide (2 ≤ count239 b) else (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b)))) else (if i < 246 then (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b))) else (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b))))) else (if i < 255 then (if i < 252 then (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))) else (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b)))) else (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)))))) else (if i < 273 then (if i < 267 then (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))) else (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b))))) else (if i < 279 then (if i < 276 then (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)))) else (if i < 282 then (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))) else (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)))))))) else (if i < 333 then (if i < 309 then (if i < 297 then (if i < 291 then (if i < 288 then (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))) else (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b)))) else (if i < 294 then (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b))) else (if i < 295 then decide (2 ≤ count293 b) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b))))) else (if i < 303 then (if i < 300 then (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))) else (if i < 301 then decide (2 ≤ count299 b) else (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b)))) else (if i < 306 then (if i < 304 then decide (1 ≤ count303 b) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b))) else (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))))) else (if i < 321 then (if i < 315 then (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b)))) else (if i < 318 then (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b))) else (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))))) else (if i < 327 then (if i < 324 then (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b))) else (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)))) else (if i < 330 then (if i < 328 then decide (1 ≤ count327 b) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b))) else (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))))))) else (if i < 357 then (if i < 345 then (if i < 339 then (if i < 336 then (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)))) else (if i < 342 then (if i < 340 then decide (1 ≤ count339 b) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))) else (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b))))) else (if i < 351 then (if i < 348 then (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))) else (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b)))) else (if i < 354 then (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))) else (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)))))) else (if i < 369 then (if i < 363 then (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)))) else (if i < 366 then (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b))) else (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))))) else (if i < 375 then (if i < 372 then (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b))) else (if i < 373 then decide (2 ≤ count371 b) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 378 then (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))) else (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b)))))))))) else (if i < 571 then (if i < 476 then (if i < 428 then (if i < 404 then (if i < 392 then (if i < 386 then (if i < 383 then (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)) else (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)))) else (if i < 389 then (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))) else (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))))) else (if i < 398 then (if i < 395 then (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b))) else (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b)))) else (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))))) else (if i < 416 then (if i < 410 then (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 408 then decide (1 ≤ count407 b) else (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)))) else (if i < 413 then (if i < 411 then decide (2 ≤ count409 b) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))) else (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b))))) else (if i < 422 then (if i < 419 then (if i < 417 then decide (2 ≤ count415 b) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b))) else (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b)))) else (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b))))))) else (if i < 452 then (if i < 440 then (if i < 434 then (if i < 431 then (if i < 429 then decide (2 ≤ count427 b) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))) else (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (3 ≤ count431 b)))) else (if i < 437 then (if i < 435 then decide (1 ≤ count434 b) else (if i < 436 then decide (2 ≤ count434 b) else decide (1 ≤ count436 b))) else (if i < 438 then decide (2 ≤ count436 b) else (if i < 439 then decide (1 ≤ count438 b) else decide (2 ≤ count438 b))))) else (if i < 446 then (if i < 443 then (if i < 441 then decide (3 ≤ count438 b) else (if i < 442 then decide (4 ≤ count438 b) else decide (1 ≤ count442 b))) else (if i < 444 then decide (2 ≤ count442 b) else (if i < 445 then decide (3 ≤ count442 b) else decide (4 ≤ count442 b)))) else (if i < 449 then (if i < 447 then decide (5 ≤ count442 b) else (if i < 448 then decide (6 ≤ count442 b) else decide (7 ≤ count442 b))) else (if i < 450 then decide (1 ≤ count449 b) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)))))) else (if i < 464 then (if i < 458 then (if i < 455 then (if i < 453 then decide (2 ≤ count451 b) else (if i < 454 then decide (3 ≤ count451 b) else decide (1 ≤ count454 b))) else (if i < 456 then decide (2 ≤ count454 b) else (if i < 457 then decide (1 ≤ count456 b) else decide (2 ≤ count456 b)))) else (if i < 461 then (if i < 459 then decide (1 ≤ count458 b) else (if i < 460 then decide (2 ≤ count458 b) else decide (3 ≤ count458 b))) else (if i < 462 then decide (4 ≤ count458 b) else (if i < 463 then decide (1 ≤ count462 b) else decide (2 ≤ count462 b))))) else (if i < 470 then (if i < 467 then (if i < 465 then decide (3 ≤ count462 b) else (if i < 466 then decide (4 ≤ count462 b) else decide (5 ≤ count462 b))) else (if i < 468 then decide (6 ≤ count462 b) else (if i < 469 then decide (7 ≤ count462 b) else decide (1 ≤ count469 b)))) else (if i < 473 then (if i < 471 then decide (2 ≤ count469 b) else (if i < 472 then decide (3 ≤ count469 b) else decide (4 ≤ count469 b))) else (if i < 474 then decide (5 ≤ count469 b) else (if i < 475 then decide (6 ≤ count469 b) else decide (7 ≤ count469 b)))))))) else (if i < 523 then (if i < 499 then (if i < 487 then (if i < 481 then (if i < 478 then (if i < 477 then decide (8 ≤ count469 b) else decide (9 ≤ count469 b)) else (if i < 479 then decide (10 ≤ count469 b) else (if i < 480 then decide (11 ≤ count469 b) else decide (12 ≤ count469 b)))) else (if i < 484 then (if i < 482 then decide (13 ≤ count469 b) else (if i < 483 then decide (14 ≤ count469 b) else decide (1 ≤ count483 b))) else (if i < 485 then decide (2 ≤ count483 b) else (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b))))) else (if i < 493 then (if i < 490 then (if i < 488 then decide (3 ≤ count485 b) else (if i < 489 then decide (1 ≤ count488 b) else decide (2 ≤ count488 b))) else (if i < 491 then decide (1 ≤ count490 b) else (if i < 492 then decide (2 ≤ count490 b) else decide (1 ≤ count492 b)))) else (if i < 496 then (if i < 494 then decide (2 ≤ count492 b) else (if i < 495 then decide (3 ≤ count492 b) else decide (4 ≤ count492 b))) else (if i < 497 then decide (1 ≤ count496 b) else (if i < 498 then decide (2 ≤ count496 b) else decide (3 ≤ count496 b)))))) else (if i < 511 then (if i < 505 then (if i < 502 then (if i < 500 then decide (4 ≤ count496 b) else (if i < 501 then decide (5 ≤ count496 b) else decide (6 ≤ count496 b))) else (if i < 503 then decide (7 ≤ count496 b) else (if i < 504 then decide (1 ≤ count503 b) else decide (2 ≤ count503 b)))) else (if i < 508 then (if i < 506 then decide (1 ≤ count505 b) else (if i < 507 then decide (2 ≤ count505 b) else decide (3 ≤ count505 b))) else (if i < 509 then decide (1 ≤ count508 b) else (if i < 510 then decide (2 ≤ count508 b) else decide (1 ≤ count510 b))))) else (if i < 517 then (if i < 514 then (if i < 512 then decide (2 ≤ count510 b) else (if i < 513 then decide (1 ≤ count512 b) else decide (2 ≤ count512 b))) else (if i < 515 then decide (3 ≤ count512 b) else (if i < 516 then decide (4 ≤ count512 b) else decide (1 ≤ count516 b)))) else (if i < 520 then (if i < 518 then decide (2 ≤ count516 b) else (if i < 519 then decide (3 ≤ count516 b) else decide (4 ≤ count516 b))) else (if i < 521 then decide (5 ≤ count516 b) else (if i < 522 then decide (6 ≤ count516 b) else decide (7 ≤ count516 b))))))) else (if i < 547 then (if i < 535 then (if i < 529 then (if i < 526 then (if i < 524 then decide (1 ≤ count523 b) else (if i < 525 then decide (2 ≤ count523 b) else decide (3 ≤ count523 b))) else (if i < 527 then decide (4 ≤ count523 b) else (if i < 528 then decide (5 ≤ count523 b) else decide (6 ≤ count523 b)))) else (if i < 532 then (if i < 530 then decide (7 ≤ count523 b) else (if i < 531 then decide (8 ≤ count523 b) else decide (9 ≤ count523 b))) else (if i < 533 then decide (10 ≤ count523 b) else (if i < 534 then decide (11 ≤ count523 b) else decide (12 ≤ count523 b))))) else (if i < 541 then (if i < 538 then (if i < 536 then decide (13 ≤ count523 b) else (if i < 537 then decide (14 ≤ count523 b) else decide (1 ≤ count537 b))) else (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (3 ≤ count537 b) else decide (4 ≤ count537 b)))) else (if i < 544 then (if i < 542 then decide (5 ≤ count537 b) else (if i < 543 then decide (6 ≤ count537 b) else decide (7 ≤ count537 b))) else (if i < 545 then decide (8 ≤ count537 b) else (if i < 546 then decide (9 ≤ count537 b) else decide (10 ≤ count537 b)))))) else (if i < 559 then (if i < 553 then (if i < 550 then (if i < 548 then decide (11 ≤ count537 b) else (if i < 549 then decide (12 ≤ count537 b) else decide (13 ≤ count537 b))) else (if i < 551 then decide (14 ≤ count537 b) else (if i < 552 then decide (15 ≤ count537 b) else decide (16 ≤ count537 b)))) else (if i < 556 then (if i < 554 then decide (17 ≤ count537 b) else (if i < 555 then decide (18 ≤ count537 b) else decide (19 ≤ count537 b))) else (if i < 557 then decide (20 ≤ count537 b) else (if i < 558 then decide (21 ≤ count537 b) else decide (22 ≤ count537 b))))) else (if i < 565 then (if i < 562 then (if i < 560 then decide (23 ≤ count537 b) else (if i < 561 then decide (24 ≤ count537 b) else decide (25 ≤ count537 b))) else (if i < 563 then decide (26 ≤ count537 b) else (if i < 564 then decide (27 ≤ count537 b) else decide (28 ≤ count537 b)))) else (if i < 568 then (if i < 566 then decide (1 ≤ count565 b) else (if i < 567 then decide (2 ≤ count565 b) else decide (1 ≤ count567 b))) else (if i < 569 then decide (2 ≤ count567 b) else (if i < 570 then decide (3 ≤ count567 b) else decide (1 ≤ count570 b))))))))) else (if i < 666 then (if i < 618 then (if i < 594 then (if i < 582 then (if i < 576 then (if i < 573 then (if i < 572 then decide (2 ≤ count570 b) else decide (1 ≤ count572 b)) else (if i < 574 then decide (2 ≤ count572 b) else (if i < 575 then decide (1 ≤ count574 b) else decide (2 ≤ count574 b)))) else (if i < 579 then (if i < 577 then decide (3 ≤ count574 b) else (if i < 578 then decide (4 ≤ count574 b) else decide (1 ≤ count578 b))) else (if i < 580 then decide (2 ≤ count578 b) else (if i < 581 then decide (3 ≤ count578 b) else decide (4 ≤ count578 b))))) else (if i < 588 then (if i < 585 then (if i < 583 then decide (5 ≤ count578 b) else (if i < 584 then decide (6 ≤ count578 b) else decide (7 ≤ count578 b))) else (if i < 586 then decide (1 ≤ count585 b) else (if i < 587 then decide (2 ≤ count585 b) else decide (1 ≤ count587 b)))) else (if i < 591 then (if i < 589 then decide (2 ≤ count587 b) else (if i < 590 then decide (3 ≤ count587 b) else decide (1 ≤ count590 b))) else (if i < 592 then decide (2 ≤ count590 b) else (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b)))))) else (if i < 606 then (if i < 600 then (if i < 597 then (if i < 595 then decide (1 ≤ count594 b) else (if i < 596 then decide (2 ≤ count594 b) else decide (3 ≤ count594 b))) else (if i < 598 then decide (4 ≤ count594 b) else (if i < 599 then decide (1 ≤ count598 b) else decide (2 ≤ count598 b)))) else (if i < 603 then (if i < 601 then decide (3 ≤ count598 b) else (if i < 602 then decide (4 ≤ count598 b) else decide (5 ≤ count598 b))) else (if i < 604 then decide (6 ≤ count598 b) else (if i < 605 then decide (7 ≤ count598 b) else decide (1 ≤ count605 b))))) else (if i < 612 then (if i < 609 then (if i < 607 then decide (2 ≤ count605 b) else (if i < 608 then decide (3 ≤ count605 b) else decide (4 ≤ count605 b))) else (if i < 610 then decide (5 ≤ count605 b) else (if i < 611 then decide (6 ≤ count605 b) else decide (7 ≤ count605 b)))) else (if i < 615 then (if i < 613 then decide (8 ≤ count605 b) else (if i < 614 then decide (9 ≤ count605 b) else decide (10 ≤ count605 b))) else (if i < 616 then decide (11 ≤ count605 b) else (if i < 617 then decide (12 ≤ count605 b) else decide (13 ≤ count605 b))))))) else (if i < 642 then (if i < 630 then (if i < 624 then (if i < 621 then (if i < 619 then decide (14 ≤ count605 b) else (if i < 620 then decide (1 ≤ count619 b) else decide (2 ≤ count619 b))) else (if i < 622 then decide (1 ≤ count621 b) else (if i < 623 then decide (2 ≤ count621 b) else decide (3 ≤ count621 b)))) else (if i < 627 then (if i < 625 then decide (1 ≤ count624 b) else (if i < 626 then decide (2 ≤ count624 b) else decide (1 ≤ count626 b))) else (if i < 628 then decide (2 ≤ count626 b) else (if i < 629 then decide (1 ≤ count628 b) else decide (2 ≤ count628 b))))) else (if i < 636 then (if i < 633 then (if i < 631 then decide (3 ≤ count628 b) else (if i < 632 then decide (4 ≤ count628 b) else decide (1 ≤ count632 b))) else (if i < 634 then decide (2 ≤ count632 b) else (if i < 635 then decide (3 ≤ count632 b) else decide (4 ≤ count632 b)))) else (if i < 639 then (if i < 637 then decide (5 ≤ count632 b) else (if i < 638 then decide (6 ≤ count632 b) else decide (7 ≤ count632 b))) else (if i < 640 then decide (1 ≤ count639 b) else (if i < 641 then decide (2 ≤ count639 b) else decide (1 ≤ count641 b)))))) else (if i < 654 then (if i < 648 then (if i < 645 then (if i < 643 then decide (2 ≤ count641 b) else (if i < 644 then decide (3 ≤ count641 b) else decide (1 ≤ count644 b))) else (if i < 646 then decide (2 ≤ count644 b) else (if i < 647 then decide (1 ≤ count646 b) else decide (2 ≤ count646 b)))) else (if i < 651 then (if i < 649 then decide (1 ≤ count648 b) else (if i < 650 then decide (2 ≤ count648 b) else decide (3 ≤ count648 b))) else (if i < 652 then decide (4 ≤ count648 b) else (if i < 653 then decide (1 ≤ count652 b) else decide (2 ≤ count652 b))))) else (if i < 660 then (if i < 657 then (if i < 655 then decide (3 ≤ count652 b) else (if i < 656 then decide (4 ≤ count652 b) else decide (5 ≤ count652 b))) else (if i < 658 then decide (6 ≤ count652 b) else (if i < 659 then decide (7 ≤ count652 b) else decide (1 ≤ count659 b)))) else (if i < 663 then (if i < 661 then decide (2 ≤ count659 b) else (if i < 662 then decide (3 ≤ count659 b) else decide (4 ≤ count659 b))) else (if i < 664 then decide (5 ≤ count659 b) else (if i < 665 then decide (6 ≤ count659 b) else decide (7 ≤ count659 b)))))))) else (if i < 714 then (if i < 690 then (if i < 678 then (if i < 672 then (if i < 669 then (if i < 667 then decide (8 ≤ count659 b) else (if i < 668 then decide (9 ≤ count659 b) else decide (10 ≤ count659 b))) else (if i < 670 then decide (11 ≤ count659 b) else (if i < 671 then decide (12 ≤ count659 b) else decide (13 ≤ count659 b)))) else (if i < 675 then (if i < 673 then decide (14 ≤ count659 b) else (if i < 674 then decide (1 ≤ count673 b) else decide (2 ≤ count673 b))) else (if i < 676 then decide (3 ≤ count673 b) else (if i < 677 then decide (4 ≤ count673 b) else decide (5 ≤ count673 b))))) else (if i < 684 then (if i < 681 then (if i < 679 then decide (6 ≤ count673 b) else (if i < 680 then decide (7 ≤ count673 b) else decide (8 ≤ count673 b))) else (if i < 682 then decide (9 ≤ count673 b) else (if i < 683 then decide (10 ≤ count673 b) else decide (11 ≤ count673 b)))) else (if i < 687 then (if i < 685 then decide (12 ≤ count673 b) else (if i < 686 then decide (13 ≤ count673 b) else decide (14 ≤ count673 b))) else (if i < 688 then decide (15 ≤ count673 b) else (if i < 689 then decide (16 ≤ count673 b) else decide (17 ≤ count673 b)))))) else (if i < 702 then (if i < 696 then (if i < 693 then (if i < 691 then decide (18 ≤ count673 b) else (if i < 692 then decide (19 ≤ count673 b) else decide (20 ≤ count673 b))) else (if i < 694 then decide (21 ≤ count673 b) else (if i < 695 then decide (22 ≤ count673 b) else decide (23 ≤ count673 b)))) else (if i < 699 then (if i < 697 then decide (24 ≤ count673 b) else (if i < 698 then decide (25 ≤ count673 b) else decide (26 ≤ count673 b))) else (if i < 700 then decide (27 ≤ count673 b) else (if i < 701 then decide (28 ≤ count673 b) else decide (1 ≤ count701 b))))) else (if i < 708 then (if i < 705 then (if i < 703 then decide (2 ≤ count701 b) else (if i < 704 then decide (3 ≤ count701 b) else decide (4 ≤ count701 b))) else (if i < 706 then decide (5 ≤ count701 b) else (if i < 707 then decide (6 ≤ count701 b) else decide (7 ≤ count701 b)))) else (if i < 711 then (if i < 709 then decide (8 ≤ count701 b) else (if i < 710 then decide (9 ≤ count701 b) else decide (10 ≤ count701 b))) else (if i < 712 then decide (11 ≤ count701 b) else (if i < 713 then decide (12 ≤ count701 b) else decide (13 ≤ count701 b))))))) else (if i < 738 then (if i < 726 then (if i < 720 then (if i < 717 then (if i < 715 then decide (14 ≤ count701 b) else (if i < 716 then decide (15 ≤ count701 b) else decide (16 ≤ count701 b))) else (if i < 718 then decide (17 ≤ count701 b) else (if i < 719 then decide (18 ≤ count701 b) else decide (19 ≤ count701 b)))) else (if i < 723 then (if i < 721 then decide (20 ≤ count701 b) else (if i < 722 then decide (21 ≤ count701 b) else decide (22 ≤ count701 b))) else (if i < 724 then decide (23 ≤ count701 b) else (if i < 725 then decide (24 ≤ count701 b) else decide (25 ≤ count701 b))))) else (if i < 732 then (if i < 729 then (if i < 727 then decide (26 ≤ count701 b) else (if i < 728 then decide (27 ≤ count701 b) else decide (28 ≤ count701 b))) else (if i < 730 then decide (29 ≤ count701 b) else (if i < 731 then decide (30 ≤ count701 b) else decide (31 ≤ count701 b)))) else (if i < 735 then (if i < 733 then decide (32 ≤ count701 b) else (if i < 734 then decide (33 ≤ count701 b) else decide (34 ≤ count701 b))) else (if i < 736 then decide (35 ≤ count701 b) else (if i < 737 then decide (36 ≤ count701 b) else decide (37 ≤ count701 b)))))) else (if i < 750 then (if i < 744 then (if i < 741 then (if i < 739 then decide (38 ≤ count701 b) else (if i < 740 then decide (39 ≤ count701 b) else decide (40 ≤ count701 b))) else (if i < 742 then decide (41 ≤ count701 b) else (if i < 743 then decide (42 ≤ count701 b) else decide (1 ≤ count743 b)))) else (if i < 747 then (if i < 745 then decide (2 ≤ count743 b) else (if i < 746 then decide (1 ≤ count745 b) else decide (2 ≤ count745 b))) else (if i < 748 then decide (3 ≤ count745 b) else (if i < 749 then decide (1 ≤ count748 b) else decide (2 ≤ count748 b))))) else (if i < 756 then (if i < 753 then (if i < 751 then decide (1 ≤ count750 b) else (if i < 752 then decide (2 ≤ count750 b) else decide (1 ≤ count752 b))) else (if i < 754 then decide (2 ≤ count752 b) else (if i < 755 then decide (3 ≤ count752 b) else decide (4 ≤ count752 b)))) else (if i < 759 then (if i < 757 then decide (1 ≤ count756 b) else (if i < 758 then decide (2 ≤ count756 b) else decide (3 ≤ count756 b))) else (if i < 760 then decide (4 ≤ count756 b) else (if i < 761 then decide (5 ≤ count756 b) else decide (6 ≤ count756 b))))))))))) else (if i < 1143 then (if i < 952 then (if i < 857 then (if i < 809 then (if i < 785 then (if i < 773 then (if i < 767 then (if i < 764 then (if i < 763 then decide (7 ≤ count756 b) else decide (1 ≤ count763 b)) else (if i < 765 then decide (2 ≤ count763 b) else (if i < 766 then decide (1 ≤ count765 b) else decide (2 ≤ count765 b)))) else (if i < 770 then (if i < 768 then decide (3 ≤ count765 b) else (if i < 769 then decide (1 ≤ count768 b) else decide (2 ≤ count768 b))) else (if i < 771 then decide (1 ≤ count770 b) else (if i < 772 then decide (2 ≤ count770 b) else decide (1 ≤ count772 b))))) else (if i < 779 then (if i < 776 then (if i < 774 then decide (2 ≤ count772 b) else (if i < 775 then decide (3 ≤ count772 b) else decide (4 ≤ count772 b))) else (if i < 777 then decide (1 ≤ count776 b) else (if i < 778 then decide (2 ≤ count776 b) else decide (3 ≤ count776 b)))) else (if i < 782 then (if i < 780 then decide (4 ≤ count776 b) else (if i < 781 then decide (5 ≤ count776 b) else decide (6 ≤ count776 b))) else (if i < 783 then decide (7 ≤ count776 b) else (if i < 784 then decide (1 ≤ count783 b) else decide (2 ≤ count783 b)))))) else (if i < 797 then (if i < 791 then (if i < 788 then (if i < 786 then decide (3 ≤ count783 b) else (if i < 787 then decide (4 ≤ count783 b) else decide (5 ≤ count783 b))) else (if i < 789 then decide (6 ≤ count783 b) else (if i < 790 then decide (7 ≤ count783 b) else decide (8 ≤ count783 b)))) else (if i < 794 then (if i < 792 then decide (9 ≤ count783 b) else (if i < 793 then decide (10 ≤ count783 b) else decide (11 ≤ count783 b))) else (if i < 795 then decide (12 ≤ count783 b) else (if i < 796 then decide (13 ≤ count783 b) else decide (14 ≤ count783 b))))) else (if i < 803 then (if i < 800 then (if i < 798 then decide (1 ≤ count797 b) else (if i < 799 then decide (2 ≤ count797 b) else decide (1 ≤ count799 b))) else (if i < 801 then decide (2 ≤ count799 b) else (if i < 802 then decide (3 ≤ count799 b) else decide (1 ≤ count802 b)))) else (if i < 806 then (if i < 804 then decide (2 ≤ count802 b) else (if i < 805 then decide (1 ≤ count804 b) else decide (2 ≤ count804 b))) else (if i < 807 then decide (1 ≤ count806 b) else (if i < 808 then decide (2 ≤ count806 b) else decide (3 ≤ count806 b))))))) else (if i < 833 then (if i < 821 then (if i < 815 then (if i < 812 then (if i < 810 then decide (4 ≤ count806 b) else (if i < 811 then decide (1 ≤ count810 b) else decide (2 ≤ count810 b))) else (if i < 813 then decide (3 ≤ count810 b) else (if i < 814 then decide (4 ≤ count810 b) else decide (5 ≤ count810 b)))) else (if i < 818 then (if i < 816 then decide (6 ≤ count810 b) else (if i < 817 then decide (7 ≤ count810 b) else decide (1 ≤ count817 b))) else (if i < 819 then decide (2 ≤ count817 b) else (if i < 820 then decide (1 ≤ count819 b) else decide (2 ≤ count819 b))))) else (if i < 827 then (if i < 824 then (if i < 822 then decide (3 ≤ count819 b) else (if i < 823 then decide (1 ≤ count822 b) else decide (2 ≤ count822 b))) else (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (1 ≤ count826 b)))) else (if i < 830 then (if i < 828 then decide (2 ≤ count826 b) else (if i < 829 then decide (3 ≤ count826 b) else decide (4 ≤ count826 b))) else (if i < 831 then decide (1 ≤ count830 b) else (if i < 832 then decide (2 ≤ count830 b) else decide (3 ≤ count830 b)))))) else (if i < 845 then (if i < 839 then (if i < 836 then (if i < 834 then decide (4 ≤ count830 b) else (if i < 835 then decide (5 ≤ count830 b) else decide (6 ≤ count830 b))) else (if i < 837 then decide (7 ≤ count830 b) else (if i < 838 then decide (1 ≤ count837 b) else decide (2 ≤ count837 b)))) else (if i < 842 then (if i < 840 then decide (3 ≤ count837 b) else (if i < 841 then decide (4 ≤ count837 b) else decide (5 ≤ count837 b))) else (if i < 843 then decide (6 ≤ count837 b) else (if i < 844 then decide (7 ≤ count837 b) else decide (8 ≤ count837 b))))) else (if i < 851 then (if i < 848 then (if i < 846 then decide (9 ≤ count837 b) else (if i < 847 then decide (10 ≤ count837 b) else decide (11 ≤ count837 b))) else (if i < 849 then decide (12 ≤ count837 b) else (if i < 850 then decide (13 ≤ count837 b) else decide (14 ≤ count837 b)))) else (if i < 854 then (if i < 852 then decide (1 ≤ count851 b) else (if i < 853 then decide (2 ≤ count851 b) else decide (3 ≤ count851 b))) else (if i < 855 then decide (4 ≤ count851 b) else (if i < 856 then decide (5 ≤ count851 b) else decide (6 ≤ count851 b)))))))) else (if i < 904 then (if i < 880 then (if i < 868 then (if i < 862 then (if i < 859 then (if i < 858 then decide (7 ≤ count851 b) else decide (8 ≤ count851 b)) else (if i < 860 then decide (9 ≤ count851 b) else (if i < 861 then decide (10 ≤ count851 b) else decide (11 ≤ count851 b)))) else (if i < 865 then (if i < 863 then decide (12 ≤ count851 b) else (if i < 864 then decide (13 ≤ count851 b) else decide (14 ≤ count851 b))) else (if i < 866 then decide (15 ≤ count851 b) else (if i < 867 then decide (16 ≤ count851 b) else decide (1 ≤ count867 b))))) else (if i < 874 then (if i < 871 then (if i < 869 then decide (2 ≤ count867 b) else (if i < 870 then decide (1 ≤ count869 b) else decide (2 ≤ count869 b))) else (if i < 872 then decide (3 ≤ count869 b) else (if i < 873 then decide (1 ≤ count872 b) else decide (2 ≤ count872 b)))) else (if i < 877 then (if i < 875 then decide (1 ≤ count874 b) else (if i < 876 then decide (2 ≤ count874 b) else decide (1 ≤ count876 b))) else (if i < 878 then decide (2 ≤ count876 b) else (if i < 879 then decide (3 ≤ count876 b) else decide (4 ≤ count876 b)))))) else (if i < 892 then (if i < 886 then (if i < 883 then (if i < 881 then decide (1 ≤ count880 b) else (if i < 882 then decide (2 ≤ count880 b) else decide (3 ≤ count880 b))) else (if i < 884 then decide (4 ≤ count880 b) else (if i < 885 then decide (5 ≤ count880 b) else decide (6 ≤ count880 b)))) else (if i < 889 then (if i < 887 then decide (7 ≤ count880 b) else (if i < 888 then decide (1 ≤ count887 b) else decide (2 ≤ count887 b))) else (if i < 890 then decide (1 ≤ count889 b) else (if i < 891 then decide (2 ≤ count889 b) else decide (3 ≤ count889 b))))) else (if i < 898 then (if i < 895 then (if i < 893 then decide (1 ≤ count892 b) else (if i < 894 then decide (2 ≤ count892 b) else decide (1 ≤ count894 b))) else (if i < 896 then decide (2 ≤ count894 b) else (if i < 897 then decide (1 ≤ count896 b) else decide (2 ≤ count896 b)))) else (if i < 901 then (if i < 899 then decide (3 ≤ count896 b) else (if i < 900 then decide (4 ≤ count896 b) else decide (1 ≤ count900 b))) else (if i < 902 then decide (2 ≤ count900 b) else (if i < 903 then decide (3 ≤ count900 b) else decide (4 ≤ count900 b))))))) else (if i < 928 then (if i < 916 then (if i < 910 then (if i < 907 then (if i < 905 then decide (5 ≤ count900 b) else (if i < 906 then decide (6 ≤ count900 b) else decide (7 ≤ count900 b))) else (if i < 908 then decide (1 ≤ count907 b) else (if i < 909 then decide (2 ≤ count907 b) else decide (3 ≤ count907 b)))) else (if i < 913 then (if i < 911 then decide (4 ≤ count907 b) else (if i < 912 then decide (5 ≤ count907 b) else decide (6 ≤ count907 b))) else (if i < 914 then decide (7 ≤ count907 b) else (if i < 915 then decide (8 ≤ count907 b) else decide (9 ≤ count907 b))))) else (if i < 922 then (if i < 919 then (if i < 917 then decide (10 ≤ count907 b) else (if i < 918 then decide (11 ≤ count907 b) else decide (12 ≤ count907 b))) else (if i < 920 then decide (13 ≤ count907 b) else (if i < 921 then decide (14 ≤ count907 b) else decide (1 ≤ count921 b)))) else (if i < 925 then (if i < 923 then decide (2 ≤ count921 b) else (if i < 924 then decide (1 ≤ count923 b) else decide (2 ≤ count923 b))) else (if i < 926 then decide (3 ≤ count923 b) else (if i < 927 then decide (1 ≤ count926 b) else decide (2 ≤ count926 b)))))) else (if i < 940 then (if i < 934 then (if i < 931 then (if i < 929 then decide (1 ≤ count928 b) else (if i < 930 then decide (2 ≤ count928 b) else decide (1 ≤ count930 b))) else (if i < 932 then decide (2 ≤ count930 b) else (if i < 933 then decide (3 ≤ count930 b) else decide (4 ≤ count930 b)))) else (if i < 937 then (if i < 935 then decide (1 ≤ count934 b) else (if i < 936 then decide (2 ≤ count934 b) else decide (3 ≤ count934 b))) else (if i < 938 then decide (4 ≤ count934 b) else (if i < 939 then decide (5 ≤ count934 b) else decide (6 ≤ count934 b))))) else (if i < 946 then (if i < 943 then (if i < 941 then decide (7 ≤ count934 b) else (if i < 942 then decide (1 ≤ count941 b) else decide (2 ≤ count941 b))) else (if i < 944 then decide (1 ≤ count943 b) else (if i < 945 then decide (2 ≤ count943 b) else decide (3 ≤ count943 b)))) else (if i < 949 then (if i < 947 then decide (1 ≤ count946 b) else (if i < 948 then decide (2 ≤ count946 b) else decide (1 ≤ count948 b))) else (if i < 950 then decide (2 ≤ count948 b) else (if i < 951 then decide (1 ≤ count950 b) else decide (2 ≤ count950 b))))))))) else (if i < 1047 then (if i < 999 then (if i < 975 then (if i < 963 then (if i < 957 then (if i < 954 then (if i < 953 then decide (3 ≤ count950 b) else decide (4 ≤ count950 b)) else (if i < 955 then decide (1 ≤ count954 b) else (if i < 956 then decide (2 ≤ count954 b) else decide (3 ≤ count954 b)))) else (if i < 960 then (if i < 958 then decide (4 ≤ count954 b) else (if i < 959 then decide (5 ≤ count954 b) else decide (6 ≤ count954 b))) else (if i < 961 then decide (7 ≤ count954 b) else (if i < 962 then decide (1 ≤ count961 b) else decide (2 ≤ count961 b))))) else (if i < 969 then (if i < 966 then (if i < 964 then decide (3 ≤ count961 b) else (if i < 965 then decide (4 ≤ count961 b) else decide (5 ≤ count961 b))) else (if i < 967 then decide (6 ≤ count961 b) else (if i < 968 then decide (7 ≤ count961 b) else decide (8 ≤ count961 b)))) else (if i < 972 then (if i < 970 then decide (9 ≤ count961 b) else (if i < 971 then decide (10 ≤ count961 b) else decide (11 ≤ count961 b))) else (if i < 973 then decide (12 ≤ count961 b) else (if i < 974 then decide (13 ≤ count961 b) else decide (14 ≤ count961 b)))))) else (if i < 987 then (if i < 981 then (if i < 978 then (if i < 976 then decide (1 ≤ count975 b) else (if i < 977 then decide (2 ≤ count975 b) else decide (3 ≤ count975 b))) else (if i < 979 then decide (4 ≤ count975 b) else (if i < 980 then decide (5 ≤ count975 b) else decide (6 ≤ count975 b)))) else (if i < 984 then (if i < 982 then decide (7 ≤ count975 b) else (if i < 983 then decide (8 ≤ count975 b) else decide (9 ≤ count975 b))) else (if i < 985 then decide (10 ≤ count975 b) else (if i < 986 then decide (11 ≤ count975 b) else decide (12 ≤ count975 b))))) else (if i < 993 then (if i < 990 then (if i < 988 then decide (13 ≤ count975 b) else (if i < 989 then decide (14 ≤ count975 b) else decide (15 ≤ count975 b))) else (if i < 991 then decide (16 ≤ count975 b) else (if i < 992 then decide (1 ≤ count991 b) else decide (2 ≤ count991 b)))) else (if i < 996 then (if i < 994 then decide (3 ≤ count991 b) else (if i < 995 then decide (4 ≤ count991 b) else decide (5 ≤ count991 b))) else (if i < 997 then decide (6 ≤ count991 b) else (if i < 998 then decide (7 ≤ count991 b) else decide (8 ≤ count991 b))))))) else (if i < 1023 then (if i < 1011 then (if i < 1005 then (if i < 1002 then (if i < 1000 then decide (9 ≤ count991 b) else (if i < 1001 then decide (10 ≤ count991 b) else decide (11 ≤ count991 b))) else (if i < 1003 then decide (12 ≤ count991 b) else (if i < 1004 then decide (13 ≤ count991 b) else decide (14 ≤ count991 b)))) else (if i < 1008 then (if i < 1006 then decide (15 ≤ count991 b) else (if i < 1007 then decide (16 ≤ count991 b) else decide (1 ≤ count1007 b))) else (if i < 1009 then decide (2 ≤ count1007 b) else (if i < 1010 then decide (1 ≤ count1009 b) else decide (2 ≤ count1009 b))))) else (if i < 1017 then (if i < 1014 then (if i < 1012 then decide (3 ≤ count1009 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b))) else (if i < 1015 then decide (1 ≤ count1014 b) else (if i < 1016 then decide (2 ≤ count1014 b) else decide (3 ≤ count1014 b)))) else (if i < 1020 then (if i < 1018 then decide (1 ≤ count1017 b) else (if i < 1019 then decide (2 ≤ count1017 b) else decide (3 ≤ count1017 b))) else (if i < 1021 then decide (4 ≤ count1017 b) else (if i < 1022 then decide (5 ≤ count1017 b) else decide (6 ≤ count1017 b)))))) else (if i < 1035 then (if i < 1029 then (if i < 1026 then (if i < 1024 then decide (1 ≤ count1023 b) else (if i < 1025 then decide (2 ≤ count1023 b) else decide (1 ≤ count1025 b))) else (if i < 1027 then decide (2 ≤ count1025 b) else (if i < 1028 then decide (3 ≤ count1025 b) else decide (1 ≤ count1028 b)))) else (if i < 1032 then (if i < 1030 then decide (2 ≤ count1028 b) else (if i < 1031 then decide (1 ≤ count1030 b) else decide (2 ≤ count1030 b))) else (if i < 1033 then decide (1 ≤ count1032 b) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (3 ≤ count1032 b))))) else (if i < 1041 then (if i < 1038 then (if i < 1036 then decide (4 ≤ count1032 b) else (if i < 1037 then decide (1 ≤ count1036 b) else decide (2 ≤ count1036 b))) else (if i < 1039 then decide (3 ≤ count1036 b) else (if i < 1040 then decide (4 ≤ count1036 b) else decide (5 ≤ count1036 b)))) else (if i < 1044 then (if i < 1042 then decide (6 ≤ count1036 b) else (if i < 1043 then decide (7 ≤ count1036 b) else decide (1 ≤ count1043 b))) else (if i < 1045 then decide (2 ≤ count1043 b) else (if i < 1046 then decide (3 ≤ count1043 b) else decide (4 ≤ count1043 b)))))))) else (if i < 1095 then (if i < 1071 then (if i < 1059 then (if i < 1053 then (if i < 1050 then (if i < 1048 then decide (5 ≤ count1043 b) else (if i < 1049 then decide (6 ≤ count1043 b) else decide (7 ≤ count1043 b))) else (if i < 1051 then decide (8 ≤ count1043 b) else (if i < 1052 then decide (9 ≤ count1043 b) else decide (10 ≤ count1043 b)))) else (if i < 1056 then (if i < 1054 then decide (11 ≤ count1043 b) else (if i < 1055 then decide (12 ≤ count1043 b) else decide (13 ≤ count1043 b))) else (if i < 1057 then decide (1 ≤ count1056 b) else (if i < 1058 then decide (2 ≤ count1056 b) else decide (1 ≤ count1058 b))))) else (if i < 1065 then (if i < 1062 then (if i < 1060 then decide (2 ≤ count1058 b) else (if i < 1061 then decide (3 ≤ count1058 b) else decide (1 ≤ count1061 b))) else (if i < 1063 then decide (2 ≤ count1061 b) else (if i < 1064 then decide (1 ≤ count1063 b) else decide (2 ≤ count1063 b)))) else (if i < 1068 then (if i < 1066 then decide (3 ≤ count1063 b) else (if i < 1067 then decide (1 ≤ count1066 b) else decide (2 ≤ count1066 b))) else (if i < 1069 then decide (3 ≤ count1066 b) else (if i < 1070 then decide (4 ≤ count1066 b) else decide (5 ≤ count1066 b)))))) else (if i < 1083 then (if i < 1077 then (if i < 1074 then (if i < 1072 then decide (6 ≤ count1066 b) else (if i < 1073 then decide (1 ≤ count1072 b) else decide (2 ≤ count1072 b))) else (if i < 1075 then decide (1 ≤ count1074 b) else (if i < 1076 then decide (2 ≤ count1074 b) else decide (3 ≤ count1074 b)))) else (if i < 1080 then (if i < 1078 then decide (1 ≤ count1077 b) else (if i < 1079 then decide (2 ≤ count1077 b) else decide (1 ≤ count1079 b))) else (if i < 1081 then decide (2 ≤ count1079 b) else (if i < 1082 then decide (1 ≤ count1081 b) else decide (2 ≤ count1081 b))))) else (if i < 1089 then (if i < 1086 then (if i < 1084 then decide (3 ≤ count1081 b) else (if i < 1085 then decide (4 ≤ count1081 b) else decide (1 ≤ count1085 b))) else (if i < 1087 then decide (2 ≤ count1085 b) else (if i < 1088 then decide (3 ≤ count1085 b) else decide (4 ≤ count1085 b)))) else (if i < 1092 then (if i < 1090 then decide (5 ≤ count1085 b) else (if i < 1091 then decide (6 ≤ count1085 b) else decide (7 ≤ count1085 b))) else (if i < 1093 then decide (1 ≤ count1092 b) else (if i < 1094 then decide (2 ≤ count1092 b) else decide (3 ≤ count1092 b))))))) else (if i < 1119 then (if i < 1107 then (if i < 1101 then (if i < 1098 then (if i < 1096 then decide (4 ≤ count1092 b) else (if i < 1097 then decide (5 ≤ count1092 b) else decide (6 ≤ count1092 b))) else (if i < 1099 then decide (7 ≤ count1092 b) else (if i < 1100 then decide (8 ≤ count1092 b) else decide (9 ≤ count1092 b)))) else (if i < 1104 then (if i < 1102 then decide (10 ≤ count1092 b) else (if i < 1103 then decide (11 ≤ count1092 b) else decide (12 ≤ count1092 b))) else (if i < 1105 then decide (13 ≤ count1092 b) else (if i < 1106 then decide (1 ≤ count1105 b) else decide (2 ≤ count1105 b))))) else (if i < 1113 then (if i < 1110 then (if i < 1108 then decide (3 ≤ count1105 b) else (if i < 1109 then decide (4 ≤ count1105 b) else decide (5 ≤ count1105 b))) else (if i < 1111 then decide (6 ≤ count1105 b) else (if i < 1112 then decide (7 ≤ count1105 b) else decide (8 ≤ count1105 b)))) else (if i < 1116 then (if i < 1114 then decide (9 ≤ count1105 b) else (if i < 1115 then decide (10 ≤ count1105 b) else decide (11 ≤ count1105 b))) else (if i < 1117 then decide (12 ≤ count1105 b) else (if i < 1118 then decide (13 ≤ count1105 b) else decide (14 ≤ count1105 b)))))) else (if i < 1131 then (if i < 1125 then (if i < 1122 then (if i < 1120 then decide (15 ≤ count1105 b) else (if i < 1121 then decide (16 ≤ count1105 b) else decide (17 ≤ count1105 b))) else (if i < 1123 then decide (18 ≤ count1105 b) else (if i < 1124 then decide (19 ≤ count1105 b) else decide (20 ≤ count1105 b)))) else (if i < 1128 then (if i < 1126 then decide (21 ≤ count1105 b) else (if i < 1127 then decide (22 ≤ count1105 b) else decide (23 ≤ count1105 b))) else (if i < 1129 then decide (24 ≤ count1105 b) else (if i < 1130 then decide (25 ≤ count1105 b) else decide (26 ≤ count1105 b))))) else (if i < 1137 then (if i < 1134 then (if i < 1132 then decide (1 ≤ count1131 b) else (if i < 1133 then decide (2 ≤ count1131 b) else decide (1 ≤ count1133 b))) else (if i < 1135 then decide (2 ≤ count1133 b) else (if i < 1136 then decide (3 ≤ count1133 b) else decide (1 ≤ count1136 b)))) else (if i < 1140 then (if i < 1138 then decide (2 ≤ count1136 b) else (if i < 1139 then decide (1 ≤ count1138 b) else decide (2 ≤ count1138 b))) else (if i < 1141 then decide (3 ≤ count1138 b) else (if i < 1142 then decide (1 ≤ count1141 b) else decide (2 ≤ count1141 b)))))))))) else (if i < 1334 then (if i < 1238 then (if i < 1190 then (if i < 1166 then (if i < 1154 then (if i < 1148 then (if i < 1145 then (if i < 1144 then decide (3 ≤ count1141 b) else decide (4 ≤ count1141 b)) else (if i < 1146 then decide (5 ≤ count1141 b) else (if i < 1147 then decide (6 ≤ count1141 b) else decide (1 ≤ count1147 b)))) else (if i < 1151 then (if i < 1149 then decide (2 ≤ count1147 b) else (if i < 1150 then decide (1 ≤ count1149 b) else decide (2 ≤ count1149 b))) else (if i < 1152 then decide (3 ≤ count1149 b) else (if i < 1153 then decide (1 ≤ count1152 b) else decide (2 ≤ count1152 b))))) else (if i < 1160 then (if i < 1157 then (if i < 1155 then decide (1 ≤ count1154 b) else (if i < 1156 then decide (2 ≤ count1154 b) else decide (1 ≤ count1156 b))) else (if i < 1158 then decide (2 ≤ count1156 b) else (if i < 1159 then decide (3 ≤ count1156 b) else decide (4 ≤ count1156 b)))) else (if i < 1163 then (if i < 1161 then decide (1 ≤ count1160 b) else (if i < 1162 then decide (2 ≤ count1160 b) else decide (3 ≤ count1160 b))) else (if i < 1164 then decide (4 ≤ count1160 b) else (if i < 1165 then decide (5 ≤ count1160 b) else decide (6 ≤ count1160 b)))))) else (if i < 1178 then (if i < 1172 then (if i < 1169 then (if i < 1167 then decide (7 ≤ count1160 b) else (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b))) else (if i < 1170 then decide (3 ≤ count1167 b) else (if i < 1171 then decide (4 ≤ count1167 b) else decide (5 ≤ count1167 b)))) else (if i < 1175 then (if i < 1173 then decide (6 ≤ count1167 b) else (if i < 1174 then decide (7 ≤ count1167 b) else decide (8 ≤ count1167 b))) else (if i < 1176 then decide (9 ≤ count1167 b) else (if i < 1177 then decide (10 ≤ count1167 b) else decide (11 ≤ count1167 b))))) else (if i < 1184 then (if i < 1181 then (if i < 1179 then decide (12 ≤ count1167 b) else (if i < 1180 then decide (13 ≤ count1167 b) else decide (1 ≤ count1180 b))) else (if i < 1182 then decide (2 ≤ count1180 b) else (if i < 1183 then decide (1 ≤ count1182 b) else decide (2 ≤ count1182 b)))) else (if i < 1187 then (if i < 1185 then decide (3 ≤ count1182 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))) else (if i < 1188 then decide (1 ≤ count1187 b) else (if i < 1189 then decide (2 ≤ count1187 b) else decide (3 ≤ count1187 b))))))) else (if i < 1214 then (if i < 1202 then (if i < 1196 then (if i < 1193 then (if i < 1191 then decide (1 ≤ count1190 b) else (if i < 1192 then decide (2 ≤ count1190 b) else decide (3 ≤ count1190 b))) else (if i < 1194 then decide (4 ≤ count1190 b) else (if i < 1195 then decide (5 ≤ count1190 b) else decide (6 ≤ count1190 b)))) else (if i < 1199 then (if i < 1197 then decide (1 ≤ count1196 b) else (if i < 1198 then decide (2 ≤ count1196 b) else decide (1 ≤ count1198 b))) else (if i < 1200 then decide (2 ≤ count1198 b) else (if i < 1201 then decide (3 ≤ count1198 b) else decide (1 ≤ count1201 b))))) else (if i < 1208 then (if i < 1205 then (if i < 1203 then decide (2 ≤ count1201 b) else (if i < 1204 then decide (1 ≤ count1203 b) else decide (2 ≤ count1203 b))) else (if i < 1206 then decide (1 ≤ count1205 b) else (if i < 1207 then decide (2 ≤ count1205 b) else decide (3 ≤ count1205 b)))) else (if i < 1211 then (if i < 1209 then decide (4 ≤ count1205 b) else (if i < 1210 then decide (1 ≤ count1209 b) else decide (2 ≤ count1209 b))) else (if i < 1212 then decide (3 ≤ count1209 b) else (if i < 1213 then decide (4 ≤ count1209 b) else decide (5 ≤ count1209 b)))))) else (if i < 1226 then (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (6 ≤ count1209 b) else (if i < 1216 then decide (7 ≤ count1209 b) else decide (1 ≤ count1216 b))) else (if i < 1218 then decide (2 ≤ count1216 b) else (if i < 1219 then decide (3 ≤ count1216 b) else decide (4 ≤ count1216 b)))) else (if i < 1223 then (if i < 1221 then decide (5 ≤ count1216 b) else (if i < 1222 then decide (6 ≤ count1216 b) else decide (7 ≤ count1216 b))) else (if i < 1224 then decide (8 ≤ count1216 b) else (if i < 1225 then decide (9 ≤ count1216 b) else decide (10 ≤ count1216 b))))) else (if i < 1232 then (if i < 1229 then (if i < 1227 then decide (11 ≤ count1216 b) else (if i < 1228 then decide (12 ≤ count1216 b) else decide (13 ≤ count1216 b))) else (if i < 1230 then decide (1 ≤ count1229 b) else (if i < 1231 then decide (2 ≤ count1229 b) else decide (3 ≤ count1229 b)))) else (if i < 1235 then (if i < 1233 then decide (4 ≤ count1229 b) else (if i < 1234 then decide (5 ≤ count1229 b) else decide (6 ≤ count1229 b))) else (if i < 1236 then decide (7 ≤ count1229 b) else (if i < 1237 then decide (8 ≤ count1229 b) else decide (9 ≤ count1229 b)))))))) else (if i < 1286 then (if i < 1262 then (if i < 1250 then (if i < 1244 then (if i < 1241 then (if i < 1239 then decide (10 ≤ count1229 b) else (if i < 1240 then decide (11 ≤ count1229 b) else decide (12 ≤ count1229 b))) else (if i < 1242 then decide (13 ≤ count1229 b) else (if i < 1243 then decide (14 ≤ count1229 b) else decide (15 ≤ count1229 b)))) else (if i < 1247 then (if i < 1245 then decide (16 ≤ count1229 b) else (if i < 1246 then decide (17 ≤ count1229 b) else decide (18 ≤ count1229 b))) else (if i < 1248 then decide (19 ≤ count1229 b) else (if i < 1249 then decide (20 ≤ count1229 b) else decide (21 ≤ count1229 b))))) else (if i < 1256 then (if i < 1253 then (if i < 1251 then decide (22 ≤ count1229 b) else (if i < 1252 then decide (23 ≤ count1229 b) else decide (24 ≤ count1229 b))) else (if i < 1254 then decide (25 ≤ count1229 b) else (if i < 1255 then decide (26 ≤ count1229 b) else decide (1 ≤ count1255 b)))) else (if i < 1259 then (if i < 1257 then decide (2 ≤ count1255 b) else (if i < 1258 then decide (3 ≤ count1255 b) else decide (4 ≤ count1255 b))) else (if i < 1260 then decide (5 ≤ count1255 b) else (if i < 1261 then decide (6 ≤ count1255 b) else decide (7 ≤ count1255 b)))))) else (if i < 1274 then (if i < 1268 then (if i < 1265 then (if i < 1263 then decide (8 ≤ count1255 b) else (if i < 1264 then decide (9 ≤ count1255 b) else decide (10 ≤ count1255 b))) else (if i < 1266 then decide (11 ≤ count1255 b) else (if i < 1267 then decide (12 ≤ count1255 b) else decide (13 ≤ count1255 b)))) else (if i < 1271 then (if i < 1269 then decide (14 ≤ count1255 b) else (if i < 1270 then decide (15 ≤ count1255 b) else decide (16 ≤ count1255 b))) else (if i < 1272 then decide (17 ≤ count1255 b) else (if i < 1273 then decide (18 ≤ count1255 b) else decide (19 ≤ count1255 b))))) else (if i < 1280 then (if i < 1277 then (if i < 1275 then decide (20 ≤ count1255 b) else (if i < 1276 then decide (21 ≤ count1255 b) else decide (22 ≤ count1255 b))) else (if i < 1278 then decide (23 ≤ count1255 b) else (if i < 1279 then decide (24 ≤ count1255 b) else decide (25 ≤ count1255 b)))) else (if i < 1283 then (if i < 1281 then decide (26 ≤ count1255 b) else (if i < 1282 then decide (27 ≤ count1255 b) else decide (28 ≤ count1255 b))) else (if i < 1284 then decide (29 ≤ count1255 b) else (if i < 1285 then decide (30 ≤ count1255 b) else decide (31 ≤ count1255 b))))))) else (if i < 1310 then (if i < 1298 then (if i < 1292 then (if i < 1289 then (if i < 1287 then decide (32 ≤ count1255 b) else (if i < 1288 then decide (33 ≤ count1255 b) else decide (34 ≤ count1255 b))) else (if i < 1290 then decide (35 ≤ count1255 b) else (if i < 1291 then decide (36 ≤ count1255 b) else decide (37 ≤ count1255 b)))) else (if i < 1295 then (if i < 1293 then decide (38 ≤ count1255 b) else (if i < 1294 then decide (39 ≤ count1255 b) else decide (40 ≤ count1255 b))) else (if i < 1296 then decide (41 ≤ count1255 b) else (if i < 1297 then decide (42 ≤ count1255 b) else decide (1 ≤ count1297 b))))) else (if i < 1304 then (if i < 1301 then (if i < 1299 then decide (2 ≤ count1297 b) else (if i < 1300 then decide (1 ≤ count1299 b) else decide (2 ≤ count1299 b))) else (if i < 1302 then decide (3 ≤ count1299 b) else (if i < 1303 then decide (1 ≤ count1302 b) else decide (2 ≤ count1302 b)))) else (if i < 1307 then (if i < 1305 then decide (1 ≤ count1304 b) else (if i < 1306 then decide (2 ≤ count1304 b) else decide (3 ≤ count1304 b))) else (if i < 1308 then decide (1 ≤ count1307 b) else (if i < 1309 then decide (2 ≤ count1307 b) else decide (3 ≤ count1307 b)))))) else (if i < 1322 then (if i < 1316 then (if i < 1313 then (if i < 1311 then decide (4 ≤ count1307 b) else (if i < 1312 then decide (5 ≤ count1307 b) else decide (6 ≤ count1307 b))) else (if i < 1314 then decide (1 ≤ count1313 b) else (if i < 1315 then decide (2 ≤ count1313 b) else decide (1 ≤ count1315 b)))) else (if i < 1319 then (if i < 1317 then decide (2 ≤ count1315 b) else (if i < 1318 then decide (3 ≤ count1315 b) else decide (1 ≤ count1318 b))) else (if i < 1320 then decide (2 ≤ count1318 b) else (if i < 1321 then decide (1 ≤ count1320 b) else decide (2 ≤ count1320 b))))) else (if i < 1328 then (if i < 1325 then (if i < 1323 then decide (1 ≤ count1322 b) else (if i < 1324 then decide (2 ≤ count1322 b) else decide (3 ≤ count1322 b))) else (if i < 1326 then decide (4 ≤ count1322 b) else (if i < 1327 then decide (1 ≤ count1326 b) else decide (2 ≤ count1326 b)))) else (if i < 1331 then (if i < 1329 then decide (3 ≤ count1326 b) else (if i < 1330 then decide (4 ≤ count1326 b) else decide (5 ≤ count1326 b))) else (if i < 1332 then decide (6 ≤ count1326 b) else (if i < 1333 then decide (7 ≤ count1326 b) else decide (1 ≤ count1333 b))))))))) else (if i < 1429 then (if i < 1381 then (if i < 1357 then (if i < 1345 then (if i < 1339 then (if i < 1336 then (if i < 1335 then decide (2 ≤ count1333 b) else decide (3 ≤ count1333 b)) else (if i < 1337 then decide (4 ≤ count1333 b) else (if i < 1338 then decide (5 ≤ count1333 b) else decide (6 ≤ count1333 b)))) else (if i < 1342 then (if i < 1340 then decide (7 ≤ count1333 b) else (if i < 1341 then decide (8 ≤ count1333 b) else decide (9 ≤ count1333 b))) else (if i < 1343 then decide (10 ≤ count1333 b) else (if i < 1344 then decide (11 ≤ count1333 b) else decide (12 ≤ count1333 b))))) else (if i < 1351 then (if i < 1348 then (if i < 1346 then decide (1 ≤ count1345 b) else (if i < 1347 then decide (2 ≤ count1345 b) else decide (1 ≤ count1347 b))) else (if i < 1349 then decide (2 ≤ count1347 b) else (if i < 1350 then decide (3 ≤ count1347 b) else decide (1 ≤ count1350 b)))) else (if i < 1354 then (if i < 1352 then decide (2 ≤ count1350 b) else (if i < 1353 then decide (1 ≤ count1352 b) else decide (2 ≤ count1352 b))) else (if i < 1355 then decide (3 ≤ count1352 b) else (if i < 1356 then decide (1 ≤ count1355 b) else decide (2 ≤ count1355 b)))))) else (if i < 1369 then (if i < 1363 then (if i < 1360 then (if i < 1358 then decide (3 ≤ count1355 b) else (if i < 1359 then decide (4 ≤ count1355 b) else decide (5 ≤ count1355 b))) else (if i < 1361 then decide (6 ≤ count1355 b) else (if i < 1362 then decide (1 ≤ count1361 b) else decide (2 ≤ count1361 b)))) else (if i < 1366 then (if i < 1364 then decide (1 ≤ count1363 b) else (if i < 1365 then decide (2 ≤ count1363 b) else decide (3 ≤ count1363 b))) else (if i < 1367 then decide (1 ≤ count1366 b) else (if i < 1368 then decide (2 ≤ count1366 b) else decide (1 ≤ count1368 b))))) else (if i < 1375 then (if i < 1372 then (if i < 1370 then decide (2 ≤ count1368 b) else (if i < 1371 then decide (1 ≤ count1370 b) else decide (2 ≤ count1370 b))) else (if i < 1373 then decide (3 ≤ count1370 b) else (if i < 1374 then decide (4 ≤ count1370 b) else decide (1 ≤ count1374 b)))) else (if i < 1378 then (if i < 1376 then decide (2 ≤ count1374 b) else (if i < 1377 then decide (3 ≤ count1374 b) else decide (4 ≤ count1374 b))) else (if i < 1379 then decide (5 ≤ count1374 b) else (if i < 1380 then decide (6 ≤ count1374 b) else decide (7 ≤ count1374 b))))))) else (if i < 1405 then (if i < 1393 then (if i < 1387 then (if i < 1384 then (if i < 1382 then decide (1 ≤ count1381 b) else (if i < 1383 then decide (2 ≤ count1381 b) else decide (3 ≤ count1381 b))) else (if i < 1385 then decide (4 ≤ count1381 b) else (if i < 1386 then decide (5 ≤ count1381 b) else decide (6 ≤ count1381 b)))) else (if i < 1390 then (if i < 1388 then decide (7 ≤ count1381 b) else (if i < 1389 then decide (8 ≤ count1381 b) else decide (9 ≤ count1381 b))) else (if i < 1391 then decide (10 ≤ count1381 b) else (if i < 1392 then decide (11 ≤ count1381 b) else decide (12 ≤ count1381 b))))) else (if i < 1399 then (if i < 1396 then (if i < 1394 then decide (1 ≤ count1393 b) else (if i < 1395 then decide (2 ≤ count1393 b) else decide (3 ≤ count1393 b))) else (if i < 1397 then decide (4 ≤ count1393 b) else (if i < 1398 then decide (5 ≤ count1393 b) else decide (6 ≤ count1393 b)))) else (if i < 1402 then (if i < 1400 then decide (7 ≤ count1393 b) else (if i < 1401 then decide (8 ≤ count1393 b) else decide (9 ≤ count1393 b))) else (if i < 1403 then decide (10 ≤ count1393 b) else (if i < 1404 then decide (11 ≤ count1393 b) else decide (12 ≤ count1393 b)))))) else (if i < 1417 then (if i < 1411 then (if i < 1408 then (if i < 1406 then decide (1 ≤ count1405 b) else (if i < 1407 then decide (2 ≤ count1405 b) else decide (1 ≤ count1407 b))) else (if i < 1409 then decide (2 ≤ count1407 b) else (if i < 1410 then decide (3 ≤ count1407 b) else decide (1 ≤ count1410 b)))) else (if i < 1414 then (if i < 1412 then decide (2 ≤ count1410 b) else (if i < 1413 then decide (1 ≤ count1412 b) else decide (2 ≤ count1412 b))) else (if i < 1415 then decide (3 ≤ count1412 b) else (if i < 1416 then decide (1 ≤ count1415 b) else decide (2 ≤ count1415 b))))) else (if i < 1423 then (if i < 1420 then (if i < 1418 then decide (3 ≤ count1415 b) else (if i < 1419 then decide (4 ≤ count1415 b) else decide (5 ≤ count1415 b))) else (if i < 1421 then decide (6 ≤ count1415 b) else (if i < 1422 then decide (1 ≤ count1421 b) else decide (2 ≤ count1421 b)))) else (if i < 1426 then (if i < 1424 then decide (1 ≤ count1423 b) else (if i < 1425 then decide (2 ≤ count1423 b) else decide (3 ≤ count1423 b))) else (if i < 1427 then decide (1 ≤ count1426 b) else (if i < 1428 then decide (2 ≤ count1426 b) else decide (1 ≤ count1428 b)))))))) else (if i < 1477 then (if i < 1453 then (if i < 1441 then (if i < 1435 then (if i < 1432 then (if i < 1430 then decide (2 ≤ count1428 b) else (if i < 1431 then decide (1 ≤ count1430 b) else decide (2 ≤ count1430 b))) else (if i < 1433 then decide (3 ≤ count1430 b) else (if i < 1434 then decide (4 ≤ count1430 b) else decide (1 ≤ count1434 b)))) else (if i < 1438 then (if i < 1436 then decide (2 ≤ count1434 b) else (if i < 1437 then decide (3 ≤ count1434 b) else decide (4 ≤ count1434 b))) else (if i < 1439 then decide (5 ≤ count1434 b) else (if i < 1440 then decide (6 ≤ count1434 b) else decide (7 ≤ count1434 b))))) else (if i < 1447 then (if i < 1444 then (if i < 1442 then decide (1 ≤ count1441 b) else (if i < 1443 then decide (2 ≤ count1441 b) else decide (3 ≤ count1441 b))) else (if i < 1445 then decide (4 ≤ count1441 b) else (if i < 1446 then decide (5 ≤ count1441 b) else decide (6 ≤ count1441 b)))) else (if i < 1450 then (if i < 1448 then decide (7 ≤ count1441 b) else (if i < 1449 then decide (8 ≤ count1441 b) else decide (9 ≤ count1441 b))) else (if i < 1451 then decide (10 ≤ count1441 b) else (if i < 1452 then decide (11 ≤ count1441 b) else decide (12 ≤ count1441 b)))))) else (if i < 1465 then (if i < 1459 then (if i < 1456 then (if i < 1454 then decide (1 ≤ count1453 b) else (if i < 1455 then decide (2 ≤ count1453 b) else decide (1 ≤ count1455 b))) else (if i < 1457 then decide (2 ≤ count1455 b) else (if i < 1458 then decide (3 ≤ count1455 b) else decide (1 ≤ count1458 b)))) else (if i < 1462 then (if i < 1460 then decide (2 ≤ count1458 b) else (if i < 1461 then decide (1 ≤ count1460 b) else decide (2 ≤ count1460 b))) else (if i < 1463 then decide (3 ≤ count1460 b) else (if i < 1464 then decide (1 ≤ count1463 b) else decide (2 ≤ count1463 b))))) else (if i < 1471 then (if i < 1468 then (if i < 1466 then decide (3 ≤ count1463 b) else (if i < 1467 then decide (4 ≤ count1463 b) else decide (5 ≤ count1463 b))) else (if i < 1469 then decide (6 ≤ count1463 b) else (if i < 1470 then decide (1 ≤ count1469 b) else decide (2 ≤ count1469 b)))) else (if i < 1474 then (if i < 1472 then decide (1 ≤ count1471 b) else (if i < 1473 then decide (2 ≤ count1471 b) else decide (3 ≤ count1471 b))) else (if i < 1475 then decide (1 ≤ count1474 b) else (if i < 1476 then decide (2 ≤ count1474 b) else decide (1 ≤ count1476 b))))))) else (if i < 1501 then (if i < 1489 then (if i < 1483 then (if i < 1480 then (if i < 1478 then decide (2 ≤ count1476 b) else (if i < 1479 then decide (1 ≤ count1478 b) else decide (2 ≤ count1478 b))) else (if i < 1481 then decide (3 ≤ count1478 b) else (if i < 1482 then decide (4 ≤ count1478 b) else decide (1 ≤ count1482 b)))) else (if i < 1486 then (if i < 1484 then decide (2 ≤ count1482 b) else (if i < 1485 then decide (3 ≤ count1482 b) else decide (4 ≤ count1482 b))) else (if i < 1487 then decide (5 ≤ count1482 b) else (if i < 1488 then decide (6 ≤ count1482 b) else decide (7 ≤ count1482 b))))) else (if i < 1495 then (if i < 1492 then (if i < 1490 then decide (1 ≤ count1489 b) else (if i < 1491 then decide (2 ≤ count1489 b) else decide (3 ≤ count1489 b))) else (if i < 1493 then decide (4 ≤ count1489 b) else (if i < 1494 then decide (5 ≤ count1489 b) else decide (6 ≤ count1489 b)))) else (if i < 1498 then (if i < 1496 then decide (7 ≤ count1489 b) else (if i < 1497 then decide (8 ≤ count1489 b) else decide (9 ≤ count1489 b))) else (if i < 1499 then decide (10 ≤ count1489 b) else (if i < 1500 then decide (11 ≤ count1489 b) else decide (12 ≤ count1489 b)))))) else (if i < 1513 then (if i < 1507 then (if i < 1504 then (if i < 1502 then decide (1 ≤ count1501 b) else (if i < 1503 then decide (2 ≤ count1501 b) else decide (3 ≤ count1501 b))) else (if i < 1505 then decide (4 ≤ count1501 b) else (if i < 1506 then decide (5 ≤ count1501 b) else decide (6 ≤ count1501 b)))) else (if i < 1510 then (if i < 1508 then decide (7 ≤ count1501 b) else (if i < 1509 then decide (8 ≤ count1501 b) else decide (9 ≤ count1501 b))) else (if i < 1511 then decide (10 ≤ count1501 b) else (if i < 1512 then decide (11 ≤ count1501 b) else decide (12 ≤ count1501 b))))) else (if i < 1519 then (if i < 1516 then (if i < 1514 then decide (1 ≤ count1513 b) else (if i < 1515 then decide (2 ≤ count1513 b) else decide (3 ≤ count1513 b))) else (if i < 1517 then decide (4 ≤ count1513 b) else (if i < 1518 then decide (5 ≤ count1513 b) else decide (6 ≤ count1513 b)))) else (if i < 1522 then (if i < 1520 then decide (7 ≤ count1513 b) else (if i < 1521 then decide (8 ≤ count1513 b) else decide (9 ≤ count1513 b))) else (if i < 1523 then decide (10 ≤ count1513 b) else (if i < 1524 then decide (11 ≤ count1513 b) else decide (12 ≤ count1513 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (2 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (3 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (5 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (6 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (11 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (13 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (15 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (16 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (17 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (18 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (19 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (22 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (24 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (28 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (29 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (30 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (31 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (66 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (68 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (69 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (70 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (75 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (78 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (84 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (85 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (87 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (89 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (91 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (95 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (160 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (161 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (165 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (171 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (173 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (175 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (176 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (177 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (178 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (179 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (182 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (184 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (188 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (189 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (190 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (191 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (245 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (247 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (248 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (249 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (251 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (255 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (258 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (259 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (260 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (261 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (266 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (267 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (268 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (270 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (272 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (276 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (277 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (279 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (280 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (281 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (283 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (287 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (326 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (327 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (331 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (333 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (335 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (340 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (348 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (349 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (384 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (387 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (400 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (401 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (403 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (419 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (421 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (427 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (432 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (436 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (437 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (439 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (441 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (443 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (447 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (450 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (451 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (452 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (458 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (459 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (462 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (464 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (468 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (469 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (471 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (472 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (473 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (475 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (479 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (3 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (5 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (24 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (30 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (75 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (85 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (89 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (91 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (165 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (184 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (248 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (260 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (270 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (326 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (340 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (387 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (437 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (441 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (450 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (471 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (473 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (479 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (1 ≤ count217 (baseVal q)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value276 (q : Snake 81) : valuation q 276 = decide (2 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value288 (q : Snake 81) : valuation q 288 = decide (2 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value292 (q : Snake 81) : valuation q 292 = decide (2 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value316 (q : Snake 81) : valuation q 316 = decide (2 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value320 (q : Snake 81) : valuation q 320 = decide (2 ≤ count319 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value356 (q : Snake 81) : valuation q 356 = decide (2 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value370 (q : Snake 81) : valuation q 370 = decide (2 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value382 (q : Snake 81) : valuation q 382 = decide (2 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value396 (q : Snake 81) : valuation q 396 = decide (2 ≤ count395 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value424 (q : Snake 81) : valuation q 424 = decide (2 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value426 (q : Snake 81) : valuation q 426 = decide (2 ≤ count425 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value743 (q : Snake 81) : valuation q 743 = decide (1 ≤ count743 (baseVal q)) := rfl
theorem value744 (q : Snake 81) : valuation q 744 = decide (2 ≤ count743 (baseVal q)) := rfl
theorem value745 (q : Snake 81) : valuation q 745 = decide (1 ≤ count745 (baseVal q)) := rfl
theorem value746 (q : Snake 81) : valuation q 746 = decide (2 ≤ count745 (baseVal q)) := rfl
theorem value747 (q : Snake 81) : valuation q 747 = decide (3 ≤ count745 (baseVal q)) := rfl
theorem value748 (q : Snake 81) : valuation q 748 = decide (1 ≤ count748 (baseVal q)) := rfl
theorem value749 (q : Snake 81) : valuation q 749 = decide (2 ≤ count748 (baseVal q)) := rfl
theorem value750 (q : Snake 81) : valuation q 750 = decide (1 ≤ count750 (baseVal q)) := rfl
theorem value751 (q : Snake 81) : valuation q 751 = decide (2 ≤ count750 (baseVal q)) := rfl
theorem value752 (q : Snake 81) : valuation q 752 = decide (1 ≤ count752 (baseVal q)) := rfl
theorem value753 (q : Snake 81) : valuation q 753 = decide (2 ≤ count752 (baseVal q)) := rfl
theorem value754 (q : Snake 81) : valuation q 754 = decide (3 ≤ count752 (baseVal q)) := rfl
theorem value755 (q : Snake 81) : valuation q 755 = decide (4 ≤ count752 (baseVal q)) := rfl
theorem value756 (q : Snake 81) : valuation q 756 = decide (1 ≤ count756 (baseVal q)) := rfl
theorem value757 (q : Snake 81) : valuation q 757 = decide (2 ≤ count756 (baseVal q)) := rfl
theorem value758 (q : Snake 81) : valuation q 758 = decide (3 ≤ count756 (baseVal q)) := rfl
theorem value759 (q : Snake 81) : valuation q 759 = decide (4 ≤ count756 (baseVal q)) := rfl
theorem value760 (q : Snake 81) : valuation q 760 = decide (5 ≤ count756 (baseVal q)) := rfl
theorem value763 (q : Snake 81) : valuation q 763 = decide (1 ≤ count763 (baseVal q)) := rfl
theorem value764 (q : Snake 81) : valuation q 764 = decide (2 ≤ count763 (baseVal q)) := rfl
theorem value765 (q : Snake 81) : valuation q 765 = decide (1 ≤ count765 (baseVal q)) := rfl
theorem value766 (q : Snake 81) : valuation q 766 = decide (2 ≤ count765 (baseVal q)) := rfl
theorem value767 (q : Snake 81) : valuation q 767 = decide (3 ≤ count765 (baseVal q)) := rfl
theorem value768 (q : Snake 81) : valuation q 768 = decide (1 ≤ count768 (baseVal q)) := rfl
theorem value769 (q : Snake 81) : valuation q 769 = decide (2 ≤ count768 (baseVal q)) := rfl
theorem value770 (q : Snake 81) : valuation q 770 = decide (1 ≤ count770 (baseVal q)) := rfl
theorem value771 (q : Snake 81) : valuation q 771 = decide (2 ≤ count770 (baseVal q)) := rfl
theorem value772 (q : Snake 81) : valuation q 772 = decide (1 ≤ count772 (baseVal q)) := rfl
theorem value773 (q : Snake 81) : valuation q 773 = decide (2 ≤ count772 (baseVal q)) := rfl
theorem value774 (q : Snake 81) : valuation q 774 = decide (3 ≤ count772 (baseVal q)) := rfl
theorem value775 (q : Snake 81) : valuation q 775 = decide (4 ≤ count772 (baseVal q)) := rfl
theorem value776 (q : Snake 81) : valuation q 776 = decide (1 ≤ count776 (baseVal q)) := rfl
theorem value777 (q : Snake 81) : valuation q 777 = decide (2 ≤ count776 (baseVal q)) := rfl
theorem value778 (q : Snake 81) : valuation q 778 = decide (3 ≤ count776 (baseVal q)) := rfl
theorem value779 (q : Snake 81) : valuation q 779 = decide (4 ≤ count776 (baseVal q)) := rfl
theorem value780 (q : Snake 81) : valuation q 780 = decide (5 ≤ count776 (baseVal q)) := rfl
theorem value786 (q : Snake 81) : valuation q 786 = decide (4 ≤ count783 (baseVal q)) := rfl
theorem value787 (q : Snake 81) : valuation q 787 = decide (5 ≤ count783 (baseVal q)) := rfl
theorem value788 (q : Snake 81) : valuation q 788 = decide (6 ≤ count783 (baseVal q)) := rfl
theorem value789 (q : Snake 81) : valuation q 789 = decide (7 ≤ count783 (baseVal q)) := rfl
theorem value790 (q : Snake 81) : valuation q 790 = decide (8 ≤ count783 (baseVal q)) := rfl
theorem value797 (q : Snake 81) : valuation q 797 = decide (1 ≤ count797 (baseVal q)) := rfl
theorem value798 (q : Snake 81) : valuation q 798 = decide (2 ≤ count797 (baseVal q)) := rfl
theorem value799 (q : Snake 81) : valuation q 799 = decide (1 ≤ count799 (baseVal q)) := rfl
theorem value800 (q : Snake 81) : valuation q 800 = decide (2 ≤ count799 (baseVal q)) := rfl
theorem value801 (q : Snake 81) : valuation q 801 = decide (3 ≤ count799 (baseVal q)) := rfl
theorem value802 (q : Snake 81) : valuation q 802 = decide (1 ≤ count802 (baseVal q)) := rfl
theorem value803 (q : Snake 81) : valuation q 803 = decide (2 ≤ count802 (baseVal q)) := rfl
theorem value804 (q : Snake 81) : valuation q 804 = decide (1 ≤ count804 (baseVal q)) := rfl
theorem value805 (q : Snake 81) : valuation q 805 = decide (2 ≤ count804 (baseVal q)) := rfl
theorem value806 (q : Snake 81) : valuation q 806 = decide (1 ≤ count806 (baseVal q)) := rfl
theorem value807 (q : Snake 81) : valuation q 807 = decide (2 ≤ count806 (baseVal q)) := rfl
theorem value808 (q : Snake 81) : valuation q 808 = decide (3 ≤ count806 (baseVal q)) := rfl
theorem value809 (q : Snake 81) : valuation q 809 = decide (4 ≤ count806 (baseVal q)) := rfl
theorem value810 (q : Snake 81) : valuation q 810 = decide (1 ≤ count810 (baseVal q)) := rfl
theorem value811 (q : Snake 81) : valuation q 811 = decide (2 ≤ count810 (baseVal q)) := rfl
theorem value812 (q : Snake 81) : valuation q 812 = decide (3 ≤ count810 (baseVal q)) := rfl
theorem value813 (q : Snake 81) : valuation q 813 = decide (4 ≤ count810 (baseVal q)) := rfl
theorem value814 (q : Snake 81) : valuation q 814 = decide (5 ≤ count810 (baseVal q)) := rfl
theorem value817 (q : Snake 81) : valuation q 817 = decide (1 ≤ count817 (baseVal q)) := rfl
theorem value818 (q : Snake 81) : valuation q 818 = decide (2 ≤ count817 (baseVal q)) := rfl
theorem value819 (q : Snake 81) : valuation q 819 = decide (1 ≤ count819 (baseVal q)) := rfl
theorem value820 (q : Snake 81) : valuation q 820 = decide (2 ≤ count819 (baseVal q)) := rfl
theorem value822 (q : Snake 81) : valuation q 822 = decide (1 ≤ count822 (baseVal q)) := rfl
theorem value824 (q : Snake 81) : valuation q 824 = decide (1 ≤ count824 (baseVal q)) := rfl
theorem value825 (q : Snake 81) : valuation q 825 = decide (2 ≤ count824 (baseVal q)) := rfl
theorem value826 (q : Snake 81) : valuation q 826 = decide (1 ≤ count826 (baseVal q)) := rfl
theorem value827 (q : Snake 81) : valuation q 827 = decide (2 ≤ count826 (baseVal q)) := rfl
theorem value828 (q : Snake 81) : valuation q 828 = decide (3 ≤ count826 (baseVal q)) := rfl
theorem value830 (q : Snake 81) : valuation q 830 = decide (1 ≤ count830 (baseVal q)) := rfl
theorem value831 (q : Snake 81) : valuation q 831 = decide (2 ≤ count830 (baseVal q)) := rfl
theorem value832 (q : Snake 81) : valuation q 832 = decide (3 ≤ count830 (baseVal q)) := rfl
theorem value838 (q : Snake 81) : valuation q 838 = decide (2 ≤ count837 (baseVal q)) := rfl
theorem value839 (q : Snake 81) : valuation q 839 = decide (3 ≤ count837 (baseVal q)) := rfl
theorem value840 (q : Snake 81) : valuation q 840 = decide (4 ≤ count837 (baseVal q)) := rfl
theorem value841 (q : Snake 81) : valuation q 841 = decide (5 ≤ count837 (baseVal q)) := rfl
theorem value842 (q : Snake 81) : valuation q 842 = decide (6 ≤ count837 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (7 ≤ count851 (baseVal q)) := rfl
theorem value858 (q : Snake 81) : valuation q 858 = decide (8 ≤ count851 (baseVal q)) := rfl
theorem value859 (q : Snake 81) : valuation q 859 = decide (9 ≤ count851 (baseVal q)) := rfl
theorem value860 (q : Snake 81) : valuation q 860 = decide (10 ≤ count851 (baseVal q)) := rfl
theorem value861 (q : Snake 81) : valuation q 861 = decide (11 ≤ count851 (baseVal q)) := rfl
theorem value862 (q : Snake 81) : valuation q 862 = decide (12 ≤ count851 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (1 ≤ count867 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (2 ≤ count867 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (1 ≤ count869 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (2 ≤ count869 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (3 ≤ count869 (baseVal q)) := rfl
theorem value872 (q : Snake 81) : valuation q 872 = decide (1 ≤ count872 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (2 ≤ count872 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (1 ≤ count874 (baseVal q)) := rfl
theorem value875 (q : Snake 81) : valuation q 875 = decide (2 ≤ count874 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (1 ≤ count876 (baseVal q)) := rfl
theorem value877 (q : Snake 81) : valuation q 877 = decide (2 ≤ count876 (baseVal q)) := rfl
theorem value878 (q : Snake 81) : valuation q 878 = decide (3 ≤ count876 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (1 ≤ count880 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (2 ≤ count880 (baseVal q)) := rfl
theorem value882 (q : Snake 81) : valuation q 882 = decide (3 ≤ count880 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (4 ≤ count880 (baseVal q)) := rfl
theorem value887 (q : Snake 81) : valuation q 887 = decide (1 ≤ count887 (baseVal q)) := rfl
theorem value888 (q : Snake 81) : valuation q 888 = decide (2 ≤ count887 (baseVal q)) := rfl
theorem value889 (q : Snake 81) : valuation q 889 = decide (1 ≤ count889 (baseVal q)) := rfl
theorem value890 (q : Snake 81) : valuation q 890 = decide (2 ≤ count889 (baseVal q)) := rfl
theorem value891 (q : Snake 81) : valuation q 891 = decide (3 ≤ count889 (baseVal q)) := rfl
theorem value892 (q : Snake 81) : valuation q 892 = decide (1 ≤ count892 (baseVal q)) := rfl
theorem value893 (q : Snake 81) : valuation q 893 = decide (2 ≤ count892 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (1 ≤ count894 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (2 ≤ count894 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (1 ≤ count896 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (2 ≤ count896 (baseVal q)) := rfl
theorem value898 (q : Snake 81) : valuation q 898 = decide (3 ≤ count896 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (1 ≤ count900 (baseVal q)) := rfl
theorem value901 (q : Snake 81) : valuation q 901 = decide (2 ≤ count900 (baseVal q)) := rfl
theorem value902 (q : Snake 81) : valuation q 902 = decide (3 ≤ count900 (baseVal q)) := rfl
theorem value903 (q : Snake 81) : valuation q 903 = decide (4 ≤ count900 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (1 ≤ count907 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (2 ≤ count907 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (3 ≤ count907 (baseVal q)) := rfl
theorem value910 (q : Snake 81) : valuation q 910 = decide (4 ≤ count907 (baseVal q)) := rfl
theorem value911 (q : Snake 81) : valuation q 911 = decide (5 ≤ count907 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (6 ≤ count907 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (1 ≤ count921 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (2 ≤ count921 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (1 ≤ count923 (baseVal q)) := rfl
theorem value924 (q : Snake 81) : valuation q 924 = decide (2 ≤ count923 (baseVal q)) := rfl
theorem value926 (q : Snake 81) : valuation q 926 = decide (1 ≤ count926 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (2 ≤ count926 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (1 ≤ count928 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (1 ≤ count930 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (2 ≤ count930 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (3 ≤ count930 (baseVal q)) := rfl
theorem value934 (q : Snake 81) : valuation q 934 = decide (1 ≤ count934 (baseVal q)) := rfl
theorem value935 (q : Snake 81) : valuation q 935 = decide (2 ≤ count934 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (3 ≤ count934 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (4 ≤ count934 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (1 ≤ count941 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (1 ≤ count943 (baseVal q)) := rfl
theorem value944 (q : Snake 81) : valuation q 944 = decide (2 ≤ count943 (baseVal q)) := rfl
theorem value946 (q : Snake 81) : valuation q 946 = decide (1 ≤ count946 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (2 ≤ count946 (baseVal q)) := rfl
theorem value948 (q : Snake 81) : valuation q 948 = decide (1 ≤ count948 (baseVal q)) := rfl
theorem value950 (q : Snake 81) : valuation q 950 = decide (1 ≤ count950 (baseVal q)) := rfl
theorem value951 (q : Snake 81) : valuation q 951 = decide (2 ≤ count950 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (3 ≤ count950 (baseVal q)) := rfl
theorem value954 (q : Snake 81) : valuation q 954 = decide (1 ≤ count954 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (2 ≤ count954 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (3 ≤ count954 (baseVal q)) := rfl
theorem value963 (q : Snake 81) : valuation q 963 = decide (3 ≤ count961 (baseVal q)) := rfl
theorem value964 (q : Snake 81) : valuation q 964 = decide (4 ≤ count961 (baseVal q)) := rfl
theorem value965 (q : Snake 81) : valuation q 965 = decide (5 ≤ count961 (baseVal q)) := rfl
theorem value978 (q : Snake 81) : valuation q 978 = decide (4 ≤ count975 (baseVal q)) := rfl
theorem value979 (q : Snake 81) : valuation q 979 = decide (5 ≤ count975 (baseVal q)) := rfl
theorem value980 (q : Snake 81) : valuation q 980 = decide (6 ≤ count975 (baseVal q)) := rfl
theorem value981 (q : Snake 81) : valuation q 981 = decide (7 ≤ count975 (baseVal q)) := rfl
theorem value982 (q : Snake 81) : valuation q 982 = decide (8 ≤ count975 (baseVal q)) := rfl
theorem value983 (q : Snake 81) : valuation q 983 = decide (9 ≤ count975 (baseVal q)) := rfl
theorem value1006 (q : Snake 81) : valuation q 1006 = decide (16 ≤ count991 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (1 ≤ count1313 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (1 ≤ count1315 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (1 ≤ count1318 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (1 ≤ count1320 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (1 ≤ count1322 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (2 ≤ count1326 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (2 ≤ count1333 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (1 ≤ count1345 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (1 ≤ count1347 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (1 ≤ count1350 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (1 ≤ count1352 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (2 ≤ count1355 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (1 ≤ count1361 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (1 ≤ count1363 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (1 ≤ count1368 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (1 ≤ count1370 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (2 ≤ count1374 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (4 ≤ count1381 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (6 ≤ count1393 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (1 ≤ count1412 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (1 ≤ count1415 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (1 ≤ count1421 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (1 ≤ count1423 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (1 ≤ count1426 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (1 ≤ count1430 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (1 ≤ count1434 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (2 ≤ count1441 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (1 ≤ count1453 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (1 ≤ count1455 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (1 ≤ count1463 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (1 ≤ count1474 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (2 ≤ count1476 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (3 ≤ count1478 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (3 ≤ count1482 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (4 ≤ count1489 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (6 ≤ count1501 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (12 ≤ count1513 (baseVal q)) := rfl
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
theorem meaningNeg69 (b : Nat → Bool) : literal (valuationOf b) (-69) = decide (1 ≤ countLit b [-69]) := by
  change literal b (-69) = decide (1 ≤ countLit b [-69])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-69) <;> decide
theorem meaningNeg67 (b : Nat → Bool) : literal (valuationOf b) (-67) = decide (1 ≤ countLit b [-67]) := by
  change literal b (-67) = decide (1 ≤ countLit b [-67])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-67) <;> decide
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
theorem meaningNeg51 (b : Nat → Bool) : literal (valuationOf b) (-51) = decide (1 ≤ countLit b [-51]) := by
  change literal b (-51) = decide (1 ≤ countLit b [-51])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-51) <;> decide
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
theorem meaningNeg11 (b : Nat → Bool) : literal (valuationOf b) (-11) = decide (1 ≤ countLit b [-11]) := by
  change literal b (-11) = decide (1 ≤ countLit b [-11])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-11) <;> decide
theorem meaningNeg9 (b : Nat → Bool) : literal (valuationOf b) (-9) = decide (1 ≤ countLit b [-9]) := by
  change literal b (-9) = decide (1 ≤ countLit b [-9])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-9) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning110 (b : Nat → Bool) : literal (valuationOf b) (110) = decide (1 ≤ countLit b [110]) := by
  change literal b (110) = decide (1 ≤ countLit b [110])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (110) <;> decide
theorem meaning116 (b : Nat → Bool) : literal (valuationOf b) (116) = decide (1 ≤ countLit b [116]) := by
  change literal b (116) = decide (1 ≤ countLit b [116])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (116) <;> decide
theorem meaning122 (b : Nat → Bool) : literal (valuationOf b) (122) = decide (1 ≤ countLit b [122]) := by
  change literal b (122) = decide (1 ≤ countLit b [122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (122) <;> decide
theorem meaning124 (b : Nat → Bool) : literal (valuationOf b) (124) = decide (1 ≤ countLit b [124]) := by
  change literal b (124) = decide (1 ≤ countLit b [124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (124) <;> decide
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
theorem meaning144 (b : Nat → Bool) : literal (valuationOf b) (144) = decide (1 ≤ countLit b [144]) := by
  change literal b (144) = decide (1 ≤ countLit b [144])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (144) <;> decide
theorem meaning149 (b : Nat → Bool) : literal (valuationOf b) (149) = decide (1 ≤ countLit b [149]) := by
  change literal b (149) = decide (1 ≤ countLit b [149])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (149) <;> decide
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
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
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
theorem meaning173 (b : Nat → Bool) : literal (valuationOf b) (173) = decide (1 ≤ countLit b [173]) := by
  change literal b (173) = decide (1 ≤ countLit b [173])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (173) <;> decide
theorem meaning174 (b : Nat → Bool) : literal (valuationOf b) (174) = decide (1 ≤ countLit b [174]) := by
  change literal b (174) = decide (1 ≤ countLit b [174])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (174) <;> decide
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
theorem meaning184 (b : Nat → Bool) : literal (valuationOf b) (184) = decide (1 ≤ countLit b [184]) := by
  change literal b (184) = decide (1 ≤ countLit b [184])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (184) <;> decide
theorem meaning190 (b : Nat → Bool) : literal (valuationOf b) (190) = decide (1 ≤ countLit b [190]) := by
  change literal b (190) = decide (1 ≤ countLit b [190])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (190) <;> decide
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
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) (199) = decide (1 ≤ countLit b [199]) := by
  change literal b (199) = decide (1 ≤ countLit b [199])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (199) <;> decide
theorem meaning212 (b : Nat → Bool) : literal (valuationOf b) (212) = decide (1 ≤ countLit b [212]) := by
  change literal b (212) = decide (1 ≤ countLit b [212])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (212) <;> decide
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
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) 217 = decide (1 ≤ count217 b) := rfl
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning276 (b : Nat → Bool) : literal (valuationOf b) 276 = decide (2 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning288 (b : Nat → Bool) : literal (valuationOf b) 288 = decide (2 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning292 (b : Nat → Bool) : literal (valuationOf b) 292 = decide (2 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning316 (b : Nat → Bool) : literal (valuationOf b) 316 = decide (2 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning320 (b : Nat → Bool) : literal (valuationOf b) 320 = decide (2 ≤ count319 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning356 (b : Nat → Bool) : literal (valuationOf b) 356 = decide (2 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning370 (b : Nat → Bool) : literal (valuationOf b) 370 = decide (2 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning382 (b : Nat → Bool) : literal (valuationOf b) 382 = decide (2 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning396 (b : Nat → Bool) : literal (valuationOf b) 396 = decide (2 ≤ count395 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning424 (b : Nat → Bool) : literal (valuationOf b) 424 = decide (2 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning426 (b : Nat → Bool) : literal (valuationOf b) 426 = decide (2 ≤ count425 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning743 (b : Nat → Bool) : literal (valuationOf b) 743 = decide (1 ≤ count743 b) := rfl
theorem meaning744 (b : Nat → Bool) : literal (valuationOf b) 744 = decide (2 ≤ count743 b) := rfl
theorem meaning745 (b : Nat → Bool) : literal (valuationOf b) 745 = decide (1 ≤ count745 b) := rfl
theorem meaning746 (b : Nat → Bool) : literal (valuationOf b) 746 = decide (2 ≤ count745 b) := rfl
theorem meaning747 (b : Nat → Bool) : literal (valuationOf b) 747 = decide (3 ≤ count745 b) := rfl
theorem meaning748 (b : Nat → Bool) : literal (valuationOf b) 748 = decide (1 ≤ count748 b) := rfl
theorem meaning749 (b : Nat → Bool) : literal (valuationOf b) 749 = decide (2 ≤ count748 b) := rfl
theorem meaning750 (b : Nat → Bool) : literal (valuationOf b) 750 = decide (1 ≤ count750 b) := rfl
theorem meaning751 (b : Nat → Bool) : literal (valuationOf b) 751 = decide (2 ≤ count750 b) := rfl
theorem meaning752 (b : Nat → Bool) : literal (valuationOf b) 752 = decide (1 ≤ count752 b) := rfl
theorem meaning753 (b : Nat → Bool) : literal (valuationOf b) 753 = decide (2 ≤ count752 b) := rfl
theorem meaning754 (b : Nat → Bool) : literal (valuationOf b) 754 = decide (3 ≤ count752 b) := rfl
theorem meaning755 (b : Nat → Bool) : literal (valuationOf b) 755 = decide (4 ≤ count752 b) := rfl
theorem meaning756 (b : Nat → Bool) : literal (valuationOf b) 756 = decide (1 ≤ count756 b) := rfl
theorem meaning757 (b : Nat → Bool) : literal (valuationOf b) 757 = decide (2 ≤ count756 b) := rfl
theorem meaning758 (b : Nat → Bool) : literal (valuationOf b) 758 = decide (3 ≤ count756 b) := rfl
theorem meaning759 (b : Nat → Bool) : literal (valuationOf b) 759 = decide (4 ≤ count756 b) := rfl
theorem meaning760 (b : Nat → Bool) : literal (valuationOf b) 760 = decide (5 ≤ count756 b) := rfl
theorem meaning763 (b : Nat → Bool) : literal (valuationOf b) 763 = decide (1 ≤ count763 b) := rfl
theorem meaning764 (b : Nat → Bool) : literal (valuationOf b) 764 = decide (2 ≤ count763 b) := rfl
theorem meaning765 (b : Nat → Bool) : literal (valuationOf b) 765 = decide (1 ≤ count765 b) := rfl
theorem meaning766 (b : Nat → Bool) : literal (valuationOf b) 766 = decide (2 ≤ count765 b) := rfl
theorem meaning767 (b : Nat → Bool) : literal (valuationOf b) 767 = decide (3 ≤ count765 b) := rfl
theorem meaning768 (b : Nat → Bool) : literal (valuationOf b) 768 = decide (1 ≤ count768 b) := rfl
theorem meaning769 (b : Nat → Bool) : literal (valuationOf b) 769 = decide (2 ≤ count768 b) := rfl
theorem meaning770 (b : Nat → Bool) : literal (valuationOf b) 770 = decide (1 ≤ count770 b) := rfl
theorem meaning771 (b : Nat → Bool) : literal (valuationOf b) 771 = decide (2 ≤ count770 b) := rfl
theorem meaning772 (b : Nat → Bool) : literal (valuationOf b) 772 = decide (1 ≤ count772 b) := rfl
theorem meaning773 (b : Nat → Bool) : literal (valuationOf b) 773 = decide (2 ≤ count772 b) := rfl
theorem meaning774 (b : Nat → Bool) : literal (valuationOf b) 774 = decide (3 ≤ count772 b) := rfl
theorem meaning775 (b : Nat → Bool) : literal (valuationOf b) 775 = decide (4 ≤ count772 b) := rfl
theorem meaning776 (b : Nat → Bool) : literal (valuationOf b) 776 = decide (1 ≤ count776 b) := rfl
theorem meaning777 (b : Nat → Bool) : literal (valuationOf b) 777 = decide (2 ≤ count776 b) := rfl
theorem meaning778 (b : Nat → Bool) : literal (valuationOf b) 778 = decide (3 ≤ count776 b) := rfl
theorem meaning779 (b : Nat → Bool) : literal (valuationOf b) 779 = decide (4 ≤ count776 b) := rfl
theorem meaning780 (b : Nat → Bool) : literal (valuationOf b) 780 = decide (5 ≤ count776 b) := rfl
theorem meaning786 (b : Nat → Bool) : literal (valuationOf b) 786 = decide (4 ≤ count783 b) := rfl
theorem meaning787 (b : Nat → Bool) : literal (valuationOf b) 787 = decide (5 ≤ count783 b) := rfl
theorem meaning788 (b : Nat → Bool) : literal (valuationOf b) 788 = decide (6 ≤ count783 b) := rfl
theorem meaning789 (b : Nat → Bool) : literal (valuationOf b) 789 = decide (7 ≤ count783 b) := rfl
theorem meaning790 (b : Nat → Bool) : literal (valuationOf b) 790 = decide (8 ≤ count783 b) := rfl
theorem meaning797 (b : Nat → Bool) : literal (valuationOf b) 797 = decide (1 ≤ count797 b) := rfl
theorem meaning798 (b : Nat → Bool) : literal (valuationOf b) 798 = decide (2 ≤ count797 b) := rfl
theorem meaning799 (b : Nat → Bool) : literal (valuationOf b) 799 = decide (1 ≤ count799 b) := rfl
theorem meaning800 (b : Nat → Bool) : literal (valuationOf b) 800 = decide (2 ≤ count799 b) := rfl
theorem meaning801 (b : Nat → Bool) : literal (valuationOf b) 801 = decide (3 ≤ count799 b) := rfl
theorem meaning802 (b : Nat → Bool) : literal (valuationOf b) 802 = decide (1 ≤ count802 b) := rfl
theorem meaning803 (b : Nat → Bool) : literal (valuationOf b) 803 = decide (2 ≤ count802 b) := rfl
theorem meaning804 (b : Nat → Bool) : literal (valuationOf b) 804 = decide (1 ≤ count804 b) := rfl
theorem meaning805 (b : Nat → Bool) : literal (valuationOf b) 805 = decide (2 ≤ count804 b) := rfl
theorem meaning806 (b : Nat → Bool) : literal (valuationOf b) 806 = decide (1 ≤ count806 b) := rfl
theorem meaning807 (b : Nat → Bool) : literal (valuationOf b) 807 = decide (2 ≤ count806 b) := rfl
theorem meaning808 (b : Nat → Bool) : literal (valuationOf b) 808 = decide (3 ≤ count806 b) := rfl
theorem meaning809 (b : Nat → Bool) : literal (valuationOf b) 809 = decide (4 ≤ count806 b) := rfl
theorem meaning810 (b : Nat → Bool) : literal (valuationOf b) 810 = decide (1 ≤ count810 b) := rfl
theorem meaning811 (b : Nat → Bool) : literal (valuationOf b) 811 = decide (2 ≤ count810 b) := rfl
theorem meaning812 (b : Nat → Bool) : literal (valuationOf b) 812 = decide (3 ≤ count810 b) := rfl
theorem meaning813 (b : Nat → Bool) : literal (valuationOf b) 813 = decide (4 ≤ count810 b) := rfl
theorem meaning814 (b : Nat → Bool) : literal (valuationOf b) 814 = decide (5 ≤ count810 b) := rfl
theorem meaning817 (b : Nat → Bool) : literal (valuationOf b) 817 = decide (1 ≤ count817 b) := rfl
theorem meaning818 (b : Nat → Bool) : literal (valuationOf b) 818 = decide (2 ≤ count817 b) := rfl
theorem meaning819 (b : Nat → Bool) : literal (valuationOf b) 819 = decide (1 ≤ count819 b) := rfl
theorem meaning820 (b : Nat → Bool) : literal (valuationOf b) 820 = decide (2 ≤ count819 b) := rfl
theorem meaning822 (b : Nat → Bool) : literal (valuationOf b) 822 = decide (1 ≤ count822 b) := rfl
theorem meaning824 (b : Nat → Bool) : literal (valuationOf b) 824 = decide (1 ≤ count824 b) := rfl
theorem meaning825 (b : Nat → Bool) : literal (valuationOf b) 825 = decide (2 ≤ count824 b) := rfl
theorem meaning826 (b : Nat → Bool) : literal (valuationOf b) 826 = decide (1 ≤ count826 b) := rfl
theorem meaning827 (b : Nat → Bool) : literal (valuationOf b) 827 = decide (2 ≤ count826 b) := rfl
theorem meaning828 (b : Nat → Bool) : literal (valuationOf b) 828 = decide (3 ≤ count826 b) := rfl
theorem meaning830 (b : Nat → Bool) : literal (valuationOf b) 830 = decide (1 ≤ count830 b) := rfl
theorem meaning831 (b : Nat → Bool) : literal (valuationOf b) 831 = decide (2 ≤ count830 b) := rfl
theorem meaning832 (b : Nat → Bool) : literal (valuationOf b) 832 = decide (3 ≤ count830 b) := rfl
theorem meaning838 (b : Nat → Bool) : literal (valuationOf b) 838 = decide (2 ≤ count837 b) := rfl
theorem meaning839 (b : Nat → Bool) : literal (valuationOf b) 839 = decide (3 ≤ count837 b) := rfl
theorem meaning840 (b : Nat → Bool) : literal (valuationOf b) 840 = decide (4 ≤ count837 b) := rfl
theorem meaning841 (b : Nat → Bool) : literal (valuationOf b) 841 = decide (5 ≤ count837 b) := rfl
theorem meaning842 (b : Nat → Bool) : literal (valuationOf b) 842 = decide (6 ≤ count837 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (7 ≤ count851 b) := rfl
theorem meaning858 (b : Nat → Bool) : literal (valuationOf b) 858 = decide (8 ≤ count851 b) := rfl
theorem meaning859 (b : Nat → Bool) : literal (valuationOf b) 859 = decide (9 ≤ count851 b) := rfl
theorem meaning860 (b : Nat → Bool) : literal (valuationOf b) 860 = decide (10 ≤ count851 b) := rfl
theorem meaning861 (b : Nat → Bool) : literal (valuationOf b) 861 = decide (11 ≤ count851 b) := rfl
theorem meaning862 (b : Nat → Bool) : literal (valuationOf b) 862 = decide (12 ≤ count851 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (1 ≤ count867 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (2 ≤ count867 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (1 ≤ count869 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (2 ≤ count869 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (3 ≤ count869 b) := rfl
theorem meaning872 (b : Nat → Bool) : literal (valuationOf b) 872 = decide (1 ≤ count872 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (2 ≤ count872 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (1 ≤ count874 b) := rfl
theorem meaning875 (b : Nat → Bool) : literal (valuationOf b) 875 = decide (2 ≤ count874 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (1 ≤ count876 b) := rfl
theorem meaning877 (b : Nat → Bool) : literal (valuationOf b) 877 = decide (2 ≤ count876 b) := rfl
theorem meaning878 (b : Nat → Bool) : literal (valuationOf b) 878 = decide (3 ≤ count876 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (1 ≤ count880 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (2 ≤ count880 b) := rfl
theorem meaning882 (b : Nat → Bool) : literal (valuationOf b) 882 = decide (3 ≤ count880 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (4 ≤ count880 b) := rfl
theorem meaning887 (b : Nat → Bool) : literal (valuationOf b) 887 = decide (1 ≤ count887 b) := rfl
theorem meaning888 (b : Nat → Bool) : literal (valuationOf b) 888 = decide (2 ≤ count887 b) := rfl
theorem meaning889 (b : Nat → Bool) : literal (valuationOf b) 889 = decide (1 ≤ count889 b) := rfl
theorem meaning890 (b : Nat → Bool) : literal (valuationOf b) 890 = decide (2 ≤ count889 b) := rfl
theorem meaning891 (b : Nat → Bool) : literal (valuationOf b) 891 = decide (3 ≤ count889 b) := rfl
theorem meaning892 (b : Nat → Bool) : literal (valuationOf b) 892 = decide (1 ≤ count892 b) := rfl
theorem meaning893 (b : Nat → Bool) : literal (valuationOf b) 893 = decide (2 ≤ count892 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (1 ≤ count894 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (2 ≤ count894 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (1 ≤ count896 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (2 ≤ count896 b) := rfl
theorem meaning898 (b : Nat → Bool) : literal (valuationOf b) 898 = decide (3 ≤ count896 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (1 ≤ count900 b) := rfl
theorem meaning901 (b : Nat → Bool) : literal (valuationOf b) 901 = decide (2 ≤ count900 b) := rfl
theorem meaning902 (b : Nat → Bool) : literal (valuationOf b) 902 = decide (3 ≤ count900 b) := rfl
theorem meaning903 (b : Nat → Bool) : literal (valuationOf b) 903 = decide (4 ≤ count900 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (1 ≤ count907 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (2 ≤ count907 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (3 ≤ count907 b) := rfl
theorem meaning910 (b : Nat → Bool) : literal (valuationOf b) 910 = decide (4 ≤ count907 b) := rfl
theorem meaning911 (b : Nat → Bool) : literal (valuationOf b) 911 = decide (5 ≤ count907 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (6 ≤ count907 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (1 ≤ count921 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (2 ≤ count921 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (1 ≤ count923 b) := rfl
theorem meaning924 (b : Nat → Bool) : literal (valuationOf b) 924 = decide (2 ≤ count923 b) := rfl
theorem meaning926 (b : Nat → Bool) : literal (valuationOf b) 926 = decide (1 ≤ count926 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (2 ≤ count926 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (1 ≤ count928 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (1 ≤ count930 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (2 ≤ count930 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (3 ≤ count930 b) := rfl
theorem meaning934 (b : Nat → Bool) : literal (valuationOf b) 934 = decide (1 ≤ count934 b) := rfl
theorem meaning935 (b : Nat → Bool) : literal (valuationOf b) 935 = decide (2 ≤ count934 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (3 ≤ count934 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (4 ≤ count934 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (1 ≤ count941 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (1 ≤ count943 b) := rfl
theorem meaning944 (b : Nat → Bool) : literal (valuationOf b) 944 = decide (2 ≤ count943 b) := rfl
theorem meaning946 (b : Nat → Bool) : literal (valuationOf b) 946 = decide (1 ≤ count946 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (2 ≤ count946 b) := rfl
theorem meaning948 (b : Nat → Bool) : literal (valuationOf b) 948 = decide (1 ≤ count948 b) := rfl
theorem meaning950 (b : Nat → Bool) : literal (valuationOf b) 950 = decide (1 ≤ count950 b) := rfl
theorem meaning951 (b : Nat → Bool) : literal (valuationOf b) 951 = decide (2 ≤ count950 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (3 ≤ count950 b) := rfl
theorem meaning954 (b : Nat → Bool) : literal (valuationOf b) 954 = decide (1 ≤ count954 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (2 ≤ count954 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (3 ≤ count954 b) := rfl
theorem meaning963 (b : Nat → Bool) : literal (valuationOf b) 963 = decide (3 ≤ count961 b) := rfl
theorem meaning964 (b : Nat → Bool) : literal (valuationOf b) 964 = decide (4 ≤ count961 b) := rfl
theorem meaning965 (b : Nat → Bool) : literal (valuationOf b) 965 = decide (5 ≤ count961 b) := rfl
theorem meaning978 (b : Nat → Bool) : literal (valuationOf b) 978 = decide (4 ≤ count975 b) := rfl
theorem meaning979 (b : Nat → Bool) : literal (valuationOf b) 979 = decide (5 ≤ count975 b) := rfl
theorem meaning980 (b : Nat → Bool) : literal (valuationOf b) 980 = decide (6 ≤ count975 b) := rfl
theorem meaning981 (b : Nat → Bool) : literal (valuationOf b) 981 = decide (7 ≤ count975 b) := rfl
theorem meaning982 (b : Nat → Bool) : literal (valuationOf b) 982 = decide (8 ≤ count975 b) := rfl
theorem meaning983 (b : Nat → Bool) : literal (valuationOf b) 983 = decide (9 ≤ count975 b) := rfl
theorem meaning1006 (b : Nat → Bool) : literal (valuationOf b) 1006 = decide (16 ≤ count991 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (1 ≤ count1313 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (1 ≤ count1315 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (1 ≤ count1318 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (1 ≤ count1320 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (1 ≤ count1322 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (2 ≤ count1326 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (2 ≤ count1333 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (1 ≤ count1345 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (1 ≤ count1347 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (1 ≤ count1350 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (1 ≤ count1352 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (2 ≤ count1355 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (1 ≤ count1361 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (1 ≤ count1363 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (1 ≤ count1368 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (1 ≤ count1370 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (2 ≤ count1374 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (4 ≤ count1381 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (6 ≤ count1393 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (1 ≤ count1412 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (1 ≤ count1415 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (1 ≤ count1421 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (1 ≤ count1423 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (1 ≤ count1426 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (1 ≤ count1430 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (1 ≤ count1434 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (2 ≤ count1441 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (1 ≤ count1453 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (1 ≤ count1455 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (1 ≤ count1463 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (1 ≤ count1474 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (2 ≤ count1476 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (3 ≤ count1478 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (3 ≤ count1482 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (4 ≤ count1489 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (6 ≤ count1501 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (12 ≤ count1513 b) := rfl
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
end Snake9.Regrowth.E112185
