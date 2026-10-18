import E112249Data
namespace Snake9.Regrowth.E112249
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 106 then (if i < 53 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 4 then decide (InPath q (5 : Vertex)) else (if i < 5 then decide (InPath q (6 : Vertex)) else decide (InPath q (7 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (9 : Vertex)) else (if i < 8 then decide (InPath q (13 : Vertex)) else decide (InPath q (15 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex))) else (if i < 12 then decide (InPath q (19 : Vertex)) else decide (InPath q (22 : Vertex)))))) else (if i < 19 then (if i < 16 then (if i < 14 then decide (InPath q (26 : Vertex)) else (if i < 15 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex)))) else (if i < 17 then decide (InPath q (30 : Vertex)) else (if i < 18 then decide (InPath q (96 : Vertex)) else decide (InPath q (97 : Vertex))))) else (if i < 22 then (if i < 20 then decide (InPath q (102 : Vertex)) else (if i < 21 then decide (InPath q (103 : Vertex)) else decide (InPath q (104 : Vertex)))) else (if i < 24 then (if i < 23 then decide (InPath q (105 : Vertex)) else decide (InPath q (109 : Vertex))) else (if i < 25 then decide (InPath q (111 : Vertex)) else decide (InPath q (113 : Vertex))))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then decide (InPath q (114 : Vertex)) else (if i < 28 then decide (InPath q (115 : Vertex)) else decide (InPath q (118 : Vertex)))) else (if i < 30 then decide (InPath q (122 : Vertex)) else (if i < 31 then decide (InPath q (124 : Vertex)) else decide (InPath q (125 : Vertex))))) else (if i < 35 then (if i < 33 then decide (InPath q (126 : Vertex)) else (if i < 34 then decide (InPath q (130 : Vertex)) else decide (InPath q (134 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (142 : Vertex)) else decide (InPath q (166 : Vertex))) else (if i < 38 then decide (InPath q (169 : Vertex)) else decide (InPath q (173 : Vertex)))))) else (if i < 46 then (if i < 42 then (if i < 40 then decide (InPath q (175 : Vertex)) else (if i < 41 then decide (InPath q (182 : Vertex)) else decide (InPath q (186 : Vertex)))) else (if i < 44 then (if i < 43 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex))) else (if i < 45 then decide (InPath q (190 : Vertex)) else decide (InPath q (198 : Vertex))))) else (if i < 49 then (if i < 47 then decide (InPath q (258 : Vertex)) else (if i < 48 then decide (InPath q (260 : Vertex)) else decide (InPath q (262 : Vertex)))) else (if i < 51 then (if i < 50 then decide (InPath q (263 : Vertex)) else decide (InPath q (265 : Vertex))) else (if i < 52 then decide (InPath q (266 : Vertex)) else decide (InPath q (268 : Vertex)))))))) else (if i < 79 then (if i < 66 then (if i < 59 then (if i < 56 then (if i < 54 then decide (InPath q (270 : Vertex)) else (if i < 55 then decide (InPath q (276 : Vertex)) else decide (InPath q (277 : Vertex)))) else (if i < 57 then decide (InPath q (279 : Vertex)) else (if i < 58 then decide (InPath q (281 : Vertex)) else decide (InPath q (282 : Vertex))))) else (if i < 62 then (if i < 60 then decide (InPath q (283 : Vertex)) else (if i < 61 then decide (InPath q (287 : Vertex)) else decide (InPath q (326 : Vertex)))) else (if i < 64 then (if i < 63 then decide (InPath q (328 : Vertex)) else decide (InPath q (329 : Vertex))) else (if i < 65 then decide (InPath q (333 : Vertex)) else decide (InPath q (335 : Vertex)))))) else (if i < 72 then (if i < 69 then (if i < 67 then decide (InPath q (342 : Vertex)) else (if i < 68 then decide (InPath q (346 : Vertex)) else decide (InPath q (348 : Vertex)))) else (if i < 70 then decide (InPath q (349 : Vertex)) else (if i < 71 then decide (InPath q (350 : Vertex)) else decide (InPath q (354 : Vertex))))) else (if i < 75 then (if i < 73 then decide (InPath q (358 : Vertex)) else (if i < 74 then decide (InPath q (360 : Vertex)) else decide (InPath q (364 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (366 : Vertex)) else decide (InPath q (418 : Vertex))) else (if i < 78 then decide (InPath q (420 : Vertex)) else decide (InPath q (422 : Vertex))))))) else (if i < 92 then (if i < 85 then (if i < 82 then (if i < 80 then decide (InPath q (423 : Vertex)) else (if i < 81 then decide (InPath q (425 : Vertex)) else decide (InPath q (426 : Vertex)))) else (if i < 83 then decide (InPath q (428 : Vertex)) else (if i < 84 then decide (InPath q (430 : Vertex)) else decide (InPath q (436 : Vertex))))) else (if i < 88 then (if i < 86 then decide (InPath q (437 : Vertex)) else (if i < 87 then decide (InPath q (439 : Vertex)) else decide (InPath q (441 : Vertex)))) else (if i < 90 then (if i < 89 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex))) else (if i < 91 then decide (InPath q (447 : Vertex)) else decide (InPath q (480 : Vertex)))))) else (if i < 99 then (if i < 95 then (if i < 93 then decide (InPath q (481 : Vertex)) else (if i < 94 then decide (InPath q (486 : Vertex)) else decide (InPath q (487 : Vertex)))) else (if i < 97 then (if i < 96 then decide (InPath q (488 : Vertex)) else decide (InPath q (489 : Vertex))) else (if i < 98 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex))))) else (if i < 102 then (if i < 100 then decide (InPath q (497 : Vertex)) else (if i < 101 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 104 then (if i < 103 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 105 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 159 then (if i < 132 then (if i < 119 then (if i < 112 then (if i < 109 then (if i < 107 then decide (InPath q (510 : Vertex)) else (if i < 108 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 110 then decide (BallClauseLogic.Endpoint q (5 : Vertex)) else (if i < 111 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else decide (BallClauseLogic.Endpoint q (7 : Vertex))))) else (if i < 115 then (if i < 113 then decide (BallClauseLogic.Endpoint q (9 : Vertex)) else (if i < 114 then decide (BallClauseLogic.Endpoint q (13 : Vertex)) else decide (BallClauseLogic.Endpoint q (15 : Vertex)))) else (if i < 117 then (if i < 116 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex))) else (if i < 118 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (22 : Vertex)))))) else (if i < 125 then (if i < 122 then (if i < 120 then decide (BallClauseLogic.Endpoint q (26 : Vertex)) else (if i < 121 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex)))) else (if i < 123 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (96 : Vertex)) else decide (BallClauseLogic.Endpoint q (97 : Vertex))))) else (if i < 128 then (if i < 126 then decide (BallClauseLogic.Endpoint q (102 : Vertex)) else (if i < 127 then decide (BallClauseLogic.Endpoint q (103 : Vertex)) else decide (BallClauseLogic.Endpoint q (104 : Vertex)))) else (if i < 130 then (if i < 129 then decide (BallClauseLogic.Endpoint q (105 : Vertex)) else decide (BallClauseLogic.Endpoint q (109 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (111 : Vertex)) else decide (BallClauseLogic.Endpoint q (113 : Vertex))))))) else (if i < 145 then (if i < 138 then (if i < 135 then (if i < 133 then decide (BallClauseLogic.Endpoint q (114 : Vertex)) else (if i < 134 then decide (BallClauseLogic.Endpoint q (115 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex)))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (122 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (124 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex))))) else (if i < 141 then (if i < 139 then decide (BallClauseLogic.Endpoint q (126 : Vertex)) else (if i < 140 then decide (BallClauseLogic.Endpoint q (130 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex)))) else (if i < 143 then (if i < 142 then decide (BallClauseLogic.Endpoint q (142 : Vertex)) else decide (BallClauseLogic.Endpoint q (166 : Vertex))) else (if i < 144 then decide (BallClauseLogic.Endpoint q (169 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex)))))) else (if i < 152 then (if i < 148 then (if i < 146 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else (if i < 147 then decide (BallClauseLogic.Endpoint q (182 : Vertex)) else decide (BallClauseLogic.Endpoint q (186 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (190 : Vertex)) else decide (BallClauseLogic.Endpoint q (198 : Vertex))))) else (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (260 : Vertex)) else decide (BallClauseLogic.Endpoint q (262 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (263 : Vertex)) else decide (BallClauseLogic.Endpoint q (265 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex)))))))) else (if i < 186 then (if i < 172 then (if i < 165 then (if i < 162 then (if i < 160 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else (if i < 161 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (277 : Vertex)))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else (if i < 164 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex))))) else (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (328 : Vertex)) else decide (BallClauseLogic.Endpoint q (329 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (335 : Vertex)))))) else (if i < 179 then (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else decide (BallClauseLogic.Endpoint q (348 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (354 : Vertex)) else decide (BallClauseLogic.Endpoint q (358 : Vertex))))) else (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (360 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (364 : Vertex)) else decide (BallClauseLogic.Endpoint q (366 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (420 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (422 : Vertex)) else decide (BallClauseLogic.Endpoint q (423 : Vertex))))))) else (if i < 199 then (if i < 192 then (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (426 : Vertex)) else decide (BallClauseLogic.Endpoint q (428 : Vertex)))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else (if i < 191 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex))))) else (if i < 195 then (if i < 193 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else (if i < 194 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else decide (BallClauseLogic.Endpoint q (442 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (447 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))))) else (if i < 206 then (if i < 202 then (if i < 200 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else (if i < 201 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))) else (if i < 204 then (if i < 203 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))) else (if i < 205 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 209 then (if i < 207 then decide (BallClauseLogic.Endpoint q (498 : Vertex)) else (if i < 208 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 211 then (if i < 210 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 212 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count213 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count215 (b : Nat → Bool) : Nat := countLit b [107, 108, 109]
def count217 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count219 (b : Nat → Bool) : Nat := countLit b [110, 111, 112]
def count221 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112]
def count223 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count225 (b : Nat → Bool) : Nat := countLit b [113, 114, 115]
def count227 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count231 (b : Nat → Bool) : Nat := countLit b [116, 117, 118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [113, 114, 115, 116, 117, 118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119]
def count237 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [120, 121, 122]
def count241 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124, 125]
def count245 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125]
def count247 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count255 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132]
def count257 (b : Nat → Bool) : Nat := countLit b [126, 127, 128, 129, 130, 131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count281 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 152]
def count293 (b : Nat → Bool) : Nat := countLit b [149, 150, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count303 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count307 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159]
def count315 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [166, 167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count333 (b : Nat → Bool) : Nat := countLit b [169, 170, 171, 172]
def count335 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172]
def count339 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [173, 174, 175, 176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count357 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count377 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count381 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count383 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [199, 200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count395 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count399 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count403 (b : Nat → Bool) : Nat := countLit b [206, 207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count407 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count409 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212]
def count411 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209, 210, 211, 212]
def count413 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count419 (b : Nat → Bool) : Nat := countLit b [107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count421 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count423 (b : Nat → Bool) : Nat := countLit b [1, 3, 4]
def count426 (b : Nat → Bool) : Nat := countLit b [6, 8]
def count428 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count430 (b : Nat → Bool) : Nat := countLit b [6, 8, 9, 10]
def count434 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 9, 10]
def count441 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count443 (b : Nat → Bool) : Nat := countLit b [15, 16, 17]
def count446 (b : Nat → Bool) : Nat := countLit b [19, 22]
def count448 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count450 (b : Nat → Bool) : Nat := countLit b [19, 22, 24, 25]
def count454 (b : Nat → Bool) : Nat := countLit b [15, 16, 17, 19, 22, 24, 25]
def count461 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 9, 10, 15, 16, 17, 19, 22, 24, 25]
def count475 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count477 (b : Nat → Bool) : Nat := countLit b [26, 31, 32]
def count480 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count482 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count484 (b : Nat → Bool) : Nat := countLit b [33, 35, 36, 37]
def count488 (b : Nat → Bool) : Nat := countLit b [26, 31, 32, 33, 35, 36, 37]
def count495 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count497 (b : Nat → Bool) : Nat := countLit b [39, 43, 44]
def count500 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count502 (b : Nat → Bool) : Nat := countLit b [47, 49]
def count504 (b : Nat → Bool) : Nat := countLit b [45, 46, 47, 49]
def count508 (b : Nat → Bool) : Nat := countLit b [39, 43, 44, 45, 46, 47, 49]
def count515 (b : Nat → Bool) : Nat := countLit b [26, 31, 32, 33, 35, 36, 37, 39, 43, 44, 45, 46, 47, 49]
def count529 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 9, 10, 15, 16, 17, 19, 22, 24, 25, 26, 31, 32, 33, 35, 36, 37, 39, 43, 44, 45, 46, 47, 49]
def count557 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count559 (b : Nat → Bool) : Nat := countLit b [53, 55, 57]
def count562 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count564 (b : Nat → Bool) : Nat := countLit b [61, 63]
def count566 (b : Nat → Bool) : Nat := countLit b [58, 60, 61, 63]
def count570 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 58, 60, 61, 63]
def count577 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count579 (b : Nat → Bool) : Nat := countLit b [65, 69, 70]
def count582 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count584 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count586 (b : Nat → Bool) : Nat := countLit b [71, 73, 75, 76]
def count590 (b : Nat → Bool) : Nat := countLit b [65, 69, 70, 71, 73, 75, 76]
def count597 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 58, 60, 61, 63, 65, 69, 70, 71, 73, 75, 76]
def count611 (b : Nat → Bool) : Nat := countLit b [79, 83]
def count613 (b : Nat → Bool) : Nat := countLit b [77, 79, 83]
def count616 (b : Nat → Bool) : Nat := countLit b [85, 87]
def count618 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count620 (b : Nat → Bool) : Nat := countLit b [85, 87, 88, 90]
def count624 (b : Nat → Bool) : Nat := countLit b [77, 79, 83, 85, 87, 88, 90]
def count631 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count633 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count635 (b : Nat → Bool) : Nat := countLit b [91, 93, 96, 98]
def count639 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count641 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count643 (b : Nat → Bool) : Nat := countLit b [99, 100, 105, 106]
def count647 (b : Nat → Bool) : Nat := countLit b [91, 93, 96, 98, 99, 100, 105, 106]
def count655 (b : Nat → Bool) : Nat := countLit b [77, 79, 83, 85, 87, 88, 90, 91, 93, 96, 98, 99, 100, 105, 106]
def count670 (b : Nat → Bool) : Nat := countLit b [53, 55, 57, 58, 60, 61, 63, 65, 69, 70, 71, 73, 75, 76, 77, 79, 83, 85, 87, 88, 90, 91, 93, 96, 98, 99, 100, 105, 106]
def count699 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 9, 10, 15, 16, 17, 19, 22, 24, 25, 26, 31, 32, 33, 35, 36, 37, 39, 43, 44, 45, 46, 47, 49, 53, 55, 57, 58, 60, 61, 63, 65, 69, 70, 71, 73, 75, 76, 77, 79, 83, 85, 87, 88, 90, 91, 93, 96, 98, 99, 100, 105, 106]
def count741 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count743 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4]
def count746 (b : Nat → Bool) : Nat := countLit b [-6, -8]
def count748 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count750 (b : Nat → Bool) : Nat := countLit b [-6, -8, -9, -10]
def count754 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -9, -10]
def count761 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count763 (b : Nat → Bool) : Nat := countLit b [-15, -16, -17]
def count766 (b : Nat → Bool) : Nat := countLit b [-19, -22]
def count768 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count770 (b : Nat → Bool) : Nat := countLit b [-19, -22, -24, -25]
def count774 (b : Nat → Bool) : Nat := countLit b [-15, -16, -17, -19, -22, -24, -25]
def count781 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -9, -10, -15, -16, -17, -19, -22, -24, -25]
def count795 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count797 (b : Nat → Bool) : Nat := countLit b [-26, -31, -32]
def count800 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count802 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count804 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36, -37]
def count808 (b : Nat → Bool) : Nat := countLit b [-26, -31, -32, -33, -35, -36, -37]
def count815 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count817 (b : Nat → Bool) : Nat := countLit b [-39, -43, -44]
def count820 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count822 (b : Nat → Bool) : Nat := countLit b [-47, -49]
def count824 (b : Nat → Bool) : Nat := countLit b [-45, -46, -47, -49]
def count828 (b : Nat → Bool) : Nat := countLit b [-39, -43, -44, -45, -46, -47, -49]
def count835 (b : Nat → Bool) : Nat := countLit b [-26, -31, -32, -33, -35, -36, -37, -39, -43, -44, -45, -46, -47, -49]
def count849 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -9, -10, -15, -16, -17, -19, -22, -24, -25, -26, -31, -32, -33, -35, -36, -37, -39, -43, -44, -45, -46, -47, -49]
def count866 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count868 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57]
def count871 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count873 (b : Nat → Bool) : Nat := countLit b [-61, -63]
def count875 (b : Nat → Bool) : Nat := countLit b [-58, -60, -61, -63]
def count879 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -58, -60, -61, -63]
def count886 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count888 (b : Nat → Bool) : Nat := countLit b [-65, -69, -70]
def count891 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count893 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count895 (b : Nat → Bool) : Nat := countLit b [-71, -73, -75, -76]
def count899 (b : Nat → Bool) : Nat := countLit b [-65, -69, -70, -71, -73, -75, -76]
def count906 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -58, -60, -61, -63, -65, -69, -70, -71, -73, -75, -76]
def count920 (b : Nat → Bool) : Nat := countLit b [-79, -83]
def count922 (b : Nat → Bool) : Nat := countLit b [-77, -79, -83]
def count925 (b : Nat → Bool) : Nat := countLit b [-85, -87]
def count927 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count929 (b : Nat → Bool) : Nat := countLit b [-85, -87, -88, -90]
def count933 (b : Nat → Bool) : Nat := countLit b [-77, -79, -83, -85, -87, -88, -90]
def count940 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count942 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count944 (b : Nat → Bool) : Nat := countLit b [-91, -93, -96, -98]
def count948 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count950 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count952 (b : Nat → Bool) : Nat := countLit b [-99, -100, -105, -106]
def count956 (b : Nat → Bool) : Nat := countLit b [-91, -93, -96, -98, -99, -100, -105, -106]
def count964 (b : Nat → Bool) : Nat := countLit b [-77, -79, -83, -85, -87, -88, -90, -91, -93, -96, -98, -99, -100, -105, -106]
def count979 (b : Nat → Bool) : Nat := countLit b [-53, -55, -57, -58, -60, -61, -63, -65, -69, -70, -71, -73, -75, -76, -77, -79, -83, -85, -87, -88, -90, -91, -93, -96, -98, -99, -100, -105, -106]
def count996 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -9, -10, -15, -16, -17, -19, -22, -24, -25, -26, -31, -32, -33, -35, -36, -37, -39, -43, -44, -45, -46, -47, -49, -53, -55, -57, -58, -60, -61, -63, -65, -69, -70, -71, -73, -75, -76, -77, -79, -83, -85, -87, -88, -90, -91, -93, -96, -98, -99, -100, -105, -106]
def count1013 (b : Nat → Bool) : Nat := countLit b [5, 7]
def count1015 (b : Nat → Bool) : Nat := countLit b [2, 5, 7]
def count1018 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count1020 (b : Nat → Bool) : Nat := countLit b [11, 12, 13]
def count1023 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 11, 12, 13]
def count1029 (b : Nat → Bool) : Nat := countLit b [18, 20]
def count1031 (b : Nat → Bool) : Nat := countLit b [14, 18, 20]
def count1034 (b : Nat → Bool) : Nat := countLit b [23, 27]
def count1036 (b : Nat → Bool) : Nat := countLit b [21, 23, 27]
def count1039 (b : Nat → Bool) : Nat := countLit b [14, 18, 20, 21, 23, 27]
def count1045 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 11, 12, 13, 14, 18, 20, 21, 23, 27]
def count1057 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count1059 (b : Nat → Bool) : Nat := countLit b [28, 29, 30]
def count1062 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count1064 (b : Nat → Bool) : Nat := countLit b [34, 38, 40]
def count1067 (b : Nat → Bool) : Nat := countLit b [28, 29, 30, 34, 38, 40]
def count1073 (b : Nat → Bool) : Nat := countLit b [42, 48]
def count1075 (b : Nat → Bool) : Nat := countLit b [41, 42, 48]
def count1078 (b : Nat → Bool) : Nat := countLit b [51, 52]
def count1080 (b : Nat → Bool) : Nat := countLit b [50, 51, 52]
def count1083 (b : Nat → Bool) : Nat := countLit b [41, 42, 48, 50, 51, 52]
def count1089 (b : Nat → Bool) : Nat := countLit b [28, 29, 30, 34, 38, 40, 41, 42, 48, 50, 51, 52]
def count1101 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 11, 12, 13, 14, 18, 20, 21, 23, 27, 28, 29, 30, 34, 38, 40, 41, 42, 48, 50, 51, 52]
def count1125 (b : Nat → Bool) : Nat := countLit b [56, 59]
def count1127 (b : Nat → Bool) : Nat := countLit b [54, 56, 59]
def count1130 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count1132 (b : Nat → Bool) : Nat := countLit b [62, 64, 66]
def count1135 (b : Nat → Bool) : Nat := countLit b [54, 56, 59, 62, 64, 66]
def count1141 (b : Nat → Bool) : Nat := countLit b [68, 72]
def count1143 (b : Nat → Bool) : Nat := countLit b [67, 68, 72]
def count1146 (b : Nat → Bool) : Nat := countLit b [78, 80]
def count1148 (b : Nat → Bool) : Nat := countLit b [74, 78, 80]
def count1151 (b : Nat → Bool) : Nat := countLit b [67, 68, 72, 74, 78, 80]
def count1157 (b : Nat → Bool) : Nat := countLit b [54, 56, 59, 62, 64, 66, 67, 68, 72, 74, 78, 80]
def count1169 (b : Nat → Bool) : Nat := countLit b [82, 84]
def count1171 (b : Nat → Bool) : Nat := countLit b [81, 82, 84]
def count1174 (b : Nat → Bool) : Nat := countLit b [89, 92]
def count1176 (b : Nat → Bool) : Nat := countLit b [86, 89, 92]
def count1179 (b : Nat → Bool) : Nat := countLit b [81, 82, 84, 86, 89, 92]
def count1185 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count1187 (b : Nat → Bool) : Nat := countLit b [94, 95, 97]
def count1190 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count1192 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count1194 (b : Nat → Bool) : Nat := countLit b [101, 102, 103, 104]
def count1198 (b : Nat → Bool) : Nat := countLit b [94, 95, 97, 101, 102, 103, 104]
def count1205 (b : Nat → Bool) : Nat := countLit b [81, 82, 84, 86, 89, 92, 94, 95, 97, 101, 102, 103, 104]
def count1218 (b : Nat → Bool) : Nat := countLit b [54, 56, 59, 62, 64, 66, 67, 68, 72, 74, 78, 80, 81, 82, 84, 86, 89, 92, 94, 95, 97, 101, 102, 103, 104]
def count1243 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 11, 12, 13, 14, 18, 20, 21, 23, 27, 28, 29, 30, 34, 38, 40, 41, 42, 48, 50, 51, 52, 54, 56, 59, 62, 64, 66, 67, 68, 72, 74, 78, 80, 81, 82, 84, 86, 89, 92, 94, 95, 97, 101, 102, 103, 104]
def count1285 (b : Nat → Bool) : Nat := countLit b [-5, -7]
def count1287 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7]
def count1290 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count1292 (b : Nat → Bool) : Nat := countLit b [-11, -12, -13]
def count1295 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -11, -12, -13]
def count1301 (b : Nat → Bool) : Nat := countLit b [-18, -20]
def count1303 (b : Nat → Bool) : Nat := countLit b [-14, -18, -20]
def count1306 (b : Nat → Bool) : Nat := countLit b [-23, -27]
def count1308 (b : Nat → Bool) : Nat := countLit b [-21, -23, -27]
def count1311 (b : Nat → Bool) : Nat := countLit b [-14, -18, -20, -21, -23, -27]
def count1317 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27]
def count1326 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count1328 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30]
def count1331 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1333 (b : Nat → Bool) : Nat := countLit b [-34, -38, -40]
def count1336 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30, -34, -38, -40]
def count1342 (b : Nat → Bool) : Nat := countLit b [-42, -48]
def count1344 (b : Nat → Bool) : Nat := countLit b [-41, -42, -48]
def count1347 (b : Nat → Bool) : Nat := countLit b [-51, -52]
def count1349 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52]
def count1352 (b : Nat → Bool) : Nat := countLit b [-41, -42, -48, -50, -51, -52]
def count1358 (b : Nat → Bool) : Nat := countLit b [-28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]
def count1367 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52]
def count1376 (b : Nat → Bool) : Nat := countLit b [-56, -59]
def count1378 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59]
def count1381 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1383 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66]
def count1386 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59, -62, -64, -66]
def count1392 (b : Nat → Bool) : Nat := countLit b [-68, -72]
def count1394 (b : Nat → Bool) : Nat := countLit b [-67, -68, -72]
def count1397 (b : Nat → Bool) : Nat := countLit b [-78, -80]
def count1399 (b : Nat → Bool) : Nat := countLit b [-74, -78, -80]
def count1402 (b : Nat → Bool) : Nat := countLit b [-67, -68, -72, -74, -78, -80]
def count1408 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80]
def count1417 (b : Nat → Bool) : Nat := countLit b [-82, -84]
def count1419 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84]
def count1422 (b : Nat → Bool) : Nat := countLit b [-89, -92]
def count1424 (b : Nat → Bool) : Nat := countLit b [-86, -89, -92]
def count1427 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84, -86, -89, -92]
def count1433 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count1435 (b : Nat → Bool) : Nat := countLit b [-94, -95, -97]
def count1438 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count1440 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1442 (b : Nat → Bool) : Nat := countLit b [-101, -102, -103, -104]
def count1446 (b : Nat → Bool) : Nat := countLit b [-94, -95, -97, -101, -102, -103, -104]
def count1453 (b : Nat → Bool) : Nat := countLit b [-81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]
def count1462 (b : Nat → Bool) : Nat := countLit b [-54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]
def count1471 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -11, -12, -13, -14, -18, -20, -21, -23, -27, -28, -29, -30, -34, -38, -40, -41, -42, -48, -50, -51, -52, -54, -56, -59, -62, -64, -66, -67, -68, -72, -74, -78, -80, -81, -82, -84, -86, -89, -92, -94, -95, -97, -101, -102, -103, -104]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 740 then (if i < 370 then (if i < 185 then (if i < 92 then (if i < 46 then (if i < 23 then (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then false else b 1) else (if i < 3 then b 2 else (if i < 4 then b 3 else b 4))) else (if i < 8 then (if i < 6 then b 5 else (if i < 7 then b 6 else b 7)) else (if i < 9 then b 8 else (if i < 10 then b 9 else b 10)))) else (if i < 17 then (if i < 14 then (if i < 12 then b 11 else (if i < 13 then b 12 else b 13)) else (if i < 15 then b 14 else (if i < 16 then b 15 else b 16))) else (if i < 20 then (if i < 18 then b 17 else (if i < 19 then b 18 else b 19)) else (if i < 21 then b 20 else (if i < 22 then b 21 else b 22))))) else (if i < 34 then (if i < 28 then (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else (if i < 27 then b 26 else b 27))) else (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 32 then b 31 else (if i < 33 then b 32 else b 33)))) else (if i < 40 then (if i < 37 then (if i < 35 then b 34 else (if i < 36 then b 35 else b 36)) else (if i < 38 then b 37 else (if i < 39 then b 38 else b 39))) else (if i < 43 then (if i < 41 then b 40 else (if i < 42 then b 41 else b 42)) else (if i < 44 then b 43 else (if i < 45 then b 44 else b 45)))))) else (if i < 69 then (if i < 57 then (if i < 51 then (if i < 48 then (if i < 47 then b 46 else b 47) else (if i < 49 then b 48 else (if i < 50 then b 49 else b 50))) else (if i < 54 then (if i < 52 then b 51 else (if i < 53 then b 52 else b 53)) else (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)))) else (if i < 63 then (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 61 then b 60 else (if i < 62 then b 61 else b 62))) else (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 67 then b 66 else (if i < 68 then b 67 else b 68))))) else (if i < 80 then (if i < 74 then (if i < 71 then (if i < 70 then b 69 else b 70) else (if i < 72 then b 71 else (if i < 73 then b 72 else b 73))) else (if i < 77 then (if i < 75 then b 74 else (if i < 76 then b 75 else b 76)) else (if i < 78 then b 77 else (if i < 79 then b 78 else b 79)))) else (if i < 86 then (if i < 83 then (if i < 81 then b 80 else (if i < 82 then b 81 else b 82)) else (if i < 84 then b 83 else (if i < 85 then b 84 else b 85))) else (if i < 89 then (if i < 87 then b 86 else (if i < 88 then b 87 else b 88)) else (if i < 90 then b 89 else (if i < 91 then b 90 else b 91))))))) else (if i < 138 then (if i < 115 then (if i < 103 then (if i < 97 then (if i < 94 then (if i < 93 then b 92 else b 93) else (if i < 95 then b 94 else (if i < 96 then b 95 else b 96))) else (if i < 100 then (if i < 98 then b 97 else (if i < 99 then b 98 else b 99)) else (if i < 101 then b 100 else (if i < 102 then b 101 else b 102)))) else (if i < 109 then (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 107 then b 106 else (if i < 108 then b 107 else b 108))) else (if i < 112 then (if i < 110 then b 109 else (if i < 111 then b 110 else b 111)) else (if i < 113 then b 112 else (if i < 114 then b 113 else b 114))))) else (if i < 126 then (if i < 120 then (if i < 117 then (if i < 116 then b 115 else b 116) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119))) else (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)))) else (if i < 132 then (if i < 129 then (if i < 127 then b 126 else (if i < 128 then b 127 else b 128)) else (if i < 130 then b 129 else (if i < 131 then b 130 else b 131))) else (if i < 135 then (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)) else (if i < 136 then b 135 else (if i < 137 then b 136 else b 137)))))) else (if i < 161 then (if i < 149 then (if i < 143 then (if i < 140 then (if i < 139 then b 138 else b 139) else (if i < 141 then b 140 else (if i < 142 then b 141 else b 142))) else (if i < 146 then (if i < 144 then b 143 else (if i < 145 then b 144 else b 145)) else (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)))) else (if i < 155 then (if i < 152 then (if i < 150 then b 149 else (if i < 151 then b 150 else b 151)) else (if i < 153 then b 152 else (if i < 154 then b 153 else b 154))) else (if i < 158 then (if i < 156 then b 155 else (if i < 157 then b 156 else b 157)) else (if i < 159 then b 158 else (if i < 160 then b 159 else b 160))))) else (if i < 173 then (if i < 167 then (if i < 164 then (if i < 162 then b 161 else (if i < 163 then b 162 else b 163)) else (if i < 165 then b 164 else (if i < 166 then b 165 else b 166))) else (if i < 170 then (if i < 168 then b 167 else (if i < 169 then b 168 else b 169)) else (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)))) else (if i < 179 then (if i < 176 then (if i < 174 then b 173 else (if i < 175 then b 174 else b 175)) else (if i < 177 then b 176 else (if i < 178 then b 177 else b 178))) else (if i < 182 then (if i < 180 then b 179 else (if i < 181 then b 180 else b 181)) else (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)))))))) else (if i < 277 then (if i < 231 then (if i < 208 then (if i < 196 then (if i < 190 then (if i < 187 then (if i < 186 then b 185 else b 186) else (if i < 188 then b 187 else (if i < 189 then b 188 else b 189))) else (if i < 193 then (if i < 191 then b 190 else (if i < 192 then b 191 else b 192)) else (if i < 194 then b 193 else (if i < 195 then b 194 else b 195)))) else (if i < 202 then (if i < 199 then (if i < 197 then b 196 else (if i < 198 then b 197 else b 198)) else (if i < 200 then b 199 else (if i < 201 then b 200 else b 201))) else (if i < 205 then (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)) else (if i < 206 then b 205 else (if i < 207 then b 206 else b 207))))) else (if i < 219 then (if i < 213 then (if i < 210 then (if i < 209 then b 208 else b 209) else (if i < 211 then b 210 else (if i < 212 then b 211 else b 212))) else (if i < 216 then (if i < 214 then decide (1 ≤ count213 b) else (if i < 215 then decide (2 ≤ count213 b) else decide (1 ≤ count215 b))) else (if i < 217 then decide (2 ≤ count215 b) else (if i < 218 then decide (1 ≤ count217 b) else decide (2 ≤ count217 b))))) else (if i < 225 then (if i < 222 then (if i < 220 then decide (1 ≤ count219 b) else (if i < 221 then decide (2 ≤ count219 b) else decide (1 ≤ count221 b))) else (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b)))) else (if i < 228 then (if i < 226 then decide (1 ≤ count225 b) else (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b))) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b))))))) else (if i < 254 then (if i < 242 then (if i < 236 then (if i < 233 then (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b)) else (if i < 234 then decide (1 ≤ count233 b) else (if i < 235 then decide (2 ≤ count233 b) else decide (1 ≤ count235 b)))) else (if i < 239 then (if i < 237 then decide (2 ≤ count235 b) else (if i < 238 then decide (1 ≤ count237 b) else decide (2 ≤ count237 b))) else (if i < 240 then decide (1 ≤ count239 b) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b))))) else (if i < 248 then (if i < 245 then (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b))) else (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b)))) else (if i < 251 then (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 252 then decide (1 ≤ count251 b) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)))))) else (if i < 265 then (if i < 259 then (if i < 256 then (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b)) else (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)))) else (if i < 262 then (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))) else (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))))) else (if i < 271 then (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)))) else (if i < 274 then (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))) else (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b)))))))) else (if i < 323 then (if i < 300 then (if i < 288 then (if i < 282 then (if i < 279 then (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b)) else (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)))) else (if i < 285 then (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))) else (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))))) else (if i < 294 then (if i < 291 then (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))) else (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b)))) else (if i < 297 then (if i < 295 then decide (2 ≤ count293 b) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b))) else (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)))))) else (if i < 311 then (if i < 305 then (if i < 302 then (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)) else (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b)))) else (if i < 308 then (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))) else (if i < 309 then decide (2 ≤ count307 b) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b))))) else (if i < 317 then (if i < 314 then (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b))) else (if i < 315 then decide (2 ≤ count313 b) else (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b)))) else (if i < 320 then (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b))) else (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))))))) else (if i < 346 then (if i < 334 then (if i < 328 then (if i < 325 then (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b)) else (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b)))) else (if i < 331 then (if i < 329 then decide (2 ≤ count327 b) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b))) else (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b))))) else (if i < 340 then (if i < 337 then (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b))) else (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)))) else (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b)))))) else (if i < 358 then (if i < 352 then (if i < 349 then (if i < 347 then decide (2 ≤ count345 b) else (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b))) else (if i < 350 then decide (1 ≤ count349 b) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)))) else (if i < 355 then (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b))) else (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b))))) else (if i < 364 then (if i < 361 then (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b))) else (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)))) else (if i < 367 then (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))) else (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b)))))))))) else (if i < 555 then (if i < 462 then (if i < 416 then (if i < 393 then (if i < 381 then (if i < 375 then (if i < 372 then (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)) else (if i < 373 then decide (2 ≤ count371 b) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 378 then (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))) else (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))))) else (if i < 387 then (if i < 384 then (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b))) else (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)))) else (if i < 390 then (if i < 388 then decide (1 ≤ count387 b) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b))) else (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b)))))) else (if i < 404 then (if i < 398 then (if i < 395 then (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)) else (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b)))) else (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))))) else (if i < 410 then (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 408 then decide (1 ≤ count407 b) else (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)))) else (if i < 413 then (if i < 411 then decide (2 ≤ count409 b) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))) else (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b))))))) else (if i < 439 then (if i < 427 then (if i < 421 then (if i < 418 then (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)) else (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b)))) else (if i < 424 then (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))) else (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (3 ≤ count423 b) else decide (1 ≤ count426 b))))) else (if i < 433 then (if i < 430 then (if i < 428 then decide (2 ≤ count426 b) else (if i < 429 then decide (1 ≤ count428 b) else decide (2 ≤ count428 b))) else (if i < 431 then decide (1 ≤ count430 b) else (if i < 432 then decide (2 ≤ count430 b) else decide (3 ≤ count430 b)))) else (if i < 436 then (if i < 434 then decide (4 ≤ count430 b) else (if i < 435 then decide (1 ≤ count434 b) else decide (2 ≤ count434 b))) else (if i < 437 then decide (3 ≤ count434 b) else (if i < 438 then decide (4 ≤ count434 b) else decide (5 ≤ count434 b)))))) else (if i < 450 then (if i < 444 then (if i < 441 then (if i < 440 then decide (6 ≤ count434 b) else decide (7 ≤ count434 b)) else (if i < 442 then decide (1 ≤ count441 b) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)))) else (if i < 447 then (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (3 ≤ count443 b) else decide (1 ≤ count446 b))) else (if i < 448 then decide (2 ≤ count446 b) else (if i < 449 then decide (1 ≤ count448 b) else decide (2 ≤ count448 b))))) else (if i < 456 then (if i < 453 then (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (3 ≤ count450 b))) else (if i < 454 then decide (4 ≤ count450 b) else (if i < 455 then decide (1 ≤ count454 b) else decide (2 ≤ count454 b)))) else (if i < 459 then (if i < 457 then decide (3 ≤ count454 b) else (if i < 458 then decide (4 ≤ count454 b) else decide (5 ≤ count454 b))) else (if i < 460 then decide (6 ≤ count454 b) else (if i < 461 then decide (7 ≤ count454 b) else decide (1 ≤ count461 b)))))))) else (if i < 508 then (if i < 485 then (if i < 473 then (if i < 467 then (if i < 464 then (if i < 463 then decide (2 ≤ count461 b) else decide (3 ≤ count461 b)) else (if i < 465 then decide (4 ≤ count461 b) else (if i < 466 then decide (5 ≤ count461 b) else decide (6 ≤ count461 b)))) else (if i < 470 then (if i < 468 then decide (7 ≤ count461 b) else (if i < 469 then decide (8 ≤ count461 b) else decide (9 ≤ count461 b))) else (if i < 471 then decide (10 ≤ count461 b) else (if i < 472 then decide (11 ≤ count461 b) else decide (12 ≤ count461 b))))) else (if i < 479 then (if i < 476 then (if i < 474 then decide (13 ≤ count461 b) else (if i < 475 then decide (14 ≤ count461 b) else decide (1 ≤ count475 b))) else (if i < 477 then decide (2 ≤ count475 b) else (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b)))) else (if i < 482 then (if i < 480 then decide (3 ≤ count477 b) else (if i < 481 then decide (1 ≤ count480 b) else decide (2 ≤ count480 b))) else (if i < 483 then decide (1 ≤ count482 b) else (if i < 484 then decide (2 ≤ count482 b) else decide (1 ≤ count484 b)))))) else (if i < 496 then (if i < 490 then (if i < 487 then (if i < 486 then decide (2 ≤ count484 b) else decide (3 ≤ count484 b)) else (if i < 488 then decide (4 ≤ count484 b) else (if i < 489 then decide (1 ≤ count488 b) else decide (2 ≤ count488 b)))) else (if i < 493 then (if i < 491 then decide (3 ≤ count488 b) else (if i < 492 then decide (4 ≤ count488 b) else decide (5 ≤ count488 b))) else (if i < 494 then decide (6 ≤ count488 b) else (if i < 495 then decide (7 ≤ count488 b) else decide (1 ≤ count495 b))))) else (if i < 502 then (if i < 499 then (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (1 ≤ count497 b) else decide (2 ≤ count497 b))) else (if i < 500 then decide (3 ≤ count497 b) else (if i < 501 then decide (1 ≤ count500 b) else decide (2 ≤ count500 b)))) else (if i < 505 then (if i < 503 then decide (1 ≤ count502 b) else (if i < 504 then decide (2 ≤ count502 b) else decide (1 ≤ count504 b))) else (if i < 506 then decide (2 ≤ count504 b) else (if i < 507 then decide (3 ≤ count504 b) else decide (4 ≤ count504 b))))))) else (if i < 531 then (if i < 519 then (if i < 513 then (if i < 510 then (if i < 509 then decide (1 ≤ count508 b) else decide (2 ≤ count508 b)) else (if i < 511 then decide (3 ≤ count508 b) else (if i < 512 then decide (4 ≤ count508 b) else decide (5 ≤ count508 b)))) else (if i < 516 then (if i < 514 then decide (6 ≤ count508 b) else (if i < 515 then decide (7 ≤ count508 b) else decide (1 ≤ count515 b))) else (if i < 517 then decide (2 ≤ count515 b) else (if i < 518 then decide (3 ≤ count515 b) else decide (4 ≤ count515 b))))) else (if i < 525 then (if i < 522 then (if i < 520 then decide (5 ≤ count515 b) else (if i < 521 then decide (6 ≤ count515 b) else decide (7 ≤ count515 b))) else (if i < 523 then decide (8 ≤ count515 b) else (if i < 524 then decide (9 ≤ count515 b) else decide (10 ≤ count515 b)))) else (if i < 528 then (if i < 526 then decide (11 ≤ count515 b) else (if i < 527 then decide (12 ≤ count515 b) else decide (13 ≤ count515 b))) else (if i < 529 then decide (14 ≤ count515 b) else (if i < 530 then decide (1 ≤ count529 b) else decide (2 ≤ count529 b)))))) else (if i < 543 then (if i < 537 then (if i < 534 then (if i < 532 then decide (3 ≤ count529 b) else (if i < 533 then decide (4 ≤ count529 b) else decide (5 ≤ count529 b))) else (if i < 535 then decide (6 ≤ count529 b) else (if i < 536 then decide (7 ≤ count529 b) else decide (8 ≤ count529 b)))) else (if i < 540 then (if i < 538 then decide (9 ≤ count529 b) else (if i < 539 then decide (10 ≤ count529 b) else decide (11 ≤ count529 b))) else (if i < 541 then decide (12 ≤ count529 b) else (if i < 542 then decide (13 ≤ count529 b) else decide (14 ≤ count529 b))))) else (if i < 549 then (if i < 546 then (if i < 544 then decide (15 ≤ count529 b) else (if i < 545 then decide (16 ≤ count529 b) else decide (17 ≤ count529 b))) else (if i < 547 then decide (18 ≤ count529 b) else (if i < 548 then decide (19 ≤ count529 b) else decide (20 ≤ count529 b)))) else (if i < 552 then (if i < 550 then decide (21 ≤ count529 b) else (if i < 551 then decide (22 ≤ count529 b) else decide (23 ≤ count529 b))) else (if i < 553 then decide (24 ≤ count529 b) else (if i < 554 then decide (25 ≤ count529 b) else decide (26 ≤ count529 b))))))))) else (if i < 647 then (if i < 601 then (if i < 578 then (if i < 566 then (if i < 560 then (if i < 557 then (if i < 556 then decide (27 ≤ count529 b) else decide (28 ≤ count529 b)) else (if i < 558 then decide (1 ≤ count557 b) else (if i < 559 then decide (2 ≤ count557 b) else decide (1 ≤ count559 b)))) else (if i < 563 then (if i < 561 then decide (2 ≤ count559 b) else (if i < 562 then decide (3 ≤ count559 b) else decide (1 ≤ count562 b))) else (if i < 564 then decide (2 ≤ count562 b) else (if i < 565 then decide (1 ≤ count564 b) else decide (2 ≤ count564 b))))) else (if i < 572 then (if i < 569 then (if i < 567 then decide (1 ≤ count566 b) else (if i < 568 then decide (2 ≤ count566 b) else decide (3 ≤ count566 b))) else (if i < 570 then decide (4 ≤ count566 b) else (if i < 571 then decide (1 ≤ count570 b) else decide (2 ≤ count570 b)))) else (if i < 575 then (if i < 573 then decide (3 ≤ count570 b) else (if i < 574 then decide (4 ≤ count570 b) else decide (5 ≤ count570 b))) else (if i < 576 then decide (6 ≤ count570 b) else (if i < 577 then decide (7 ≤ count570 b) else decide (1 ≤ count577 b)))))) else (if i < 589 then (if i < 583 then (if i < 580 then (if i < 579 then decide (2 ≤ count577 b) else decide (1 ≤ count579 b)) else (if i < 581 then decide (2 ≤ count579 b) else (if i < 582 then decide (3 ≤ count579 b) else decide (1 ≤ count582 b)))) else (if i < 586 then (if i < 584 then decide (2 ≤ count582 b) else (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b))) else (if i < 587 then decide (1 ≤ count586 b) else (if i < 588 then decide (2 ≤ count586 b) else decide (3 ≤ count586 b))))) else (if i < 595 then (if i < 592 then (if i < 590 then decide (4 ≤ count586 b) else (if i < 591 then decide (1 ≤ count590 b) else decide (2 ≤ count590 b))) else (if i < 593 then decide (3 ≤ count590 b) else (if i < 594 then decide (4 ≤ count590 b) else decide (5 ≤ count590 b)))) else (if i < 598 then (if i < 596 then decide (6 ≤ count590 b) else (if i < 597 then decide (7 ≤ count590 b) else decide (1 ≤ count597 b))) else (if i < 599 then decide (2 ≤ count597 b) else (if i < 600 then decide (3 ≤ count597 b) else decide (4 ≤ count597 b))))))) else (if i < 624 then (if i < 612 then (if i < 606 then (if i < 603 then (if i < 602 then decide (5 ≤ count597 b) else decide (6 ≤ count597 b)) else (if i < 604 then decide (7 ≤ count597 b) else (if i < 605 then decide (8 ≤ count597 b) else decide (9 ≤ count597 b)))) else (if i < 609 then (if i < 607 then decide (10 ≤ count597 b) else (if i < 608 then decide (11 ≤ count597 b) else decide (12 ≤ count597 b))) else (if i < 610 then decide (13 ≤ count597 b) else (if i < 611 then decide (14 ≤ count597 b) else decide (1 ≤ count611 b))))) else (if i < 618 then (if i < 615 then (if i < 613 then decide (2 ≤ count611 b) else (if i < 614 then decide (1 ≤ count613 b) else decide (2 ≤ count613 b))) else (if i < 616 then decide (3 ≤ count613 b) else (if i < 617 then decide (1 ≤ count616 b) else decide (2 ≤ count616 b)))) else (if i < 621 then (if i < 619 then decide (1 ≤ count618 b) else (if i < 620 then decide (2 ≤ count618 b) else decide (1 ≤ count620 b))) else (if i < 622 then decide (2 ≤ count620 b) else (if i < 623 then decide (3 ≤ count620 b) else decide (4 ≤ count620 b)))))) else (if i < 635 then (if i < 629 then (if i < 626 then (if i < 625 then decide (1 ≤ count624 b) else decide (2 ≤ count624 b)) else (if i < 627 then decide (3 ≤ count624 b) else (if i < 628 then decide (4 ≤ count624 b) else decide (5 ≤ count624 b)))) else (if i < 632 then (if i < 630 then decide (6 ≤ count624 b) else (if i < 631 then decide (7 ≤ count624 b) else decide (1 ≤ count631 b))) else (if i < 633 then decide (2 ≤ count631 b) else (if i < 634 then decide (1 ≤ count633 b) else decide (2 ≤ count633 b))))) else (if i < 641 then (if i < 638 then (if i < 636 then decide (1 ≤ count635 b) else (if i < 637 then decide (2 ≤ count635 b) else decide (3 ≤ count635 b))) else (if i < 639 then decide (4 ≤ count635 b) else (if i < 640 then decide (1 ≤ count639 b) else decide (2 ≤ count639 b)))) else (if i < 644 then (if i < 642 then decide (1 ≤ count641 b) else (if i < 643 then decide (2 ≤ count641 b) else decide (1 ≤ count643 b))) else (if i < 645 then decide (2 ≤ count643 b) else (if i < 646 then decide (3 ≤ count643 b) else decide (4 ≤ count643 b)))))))) else (if i < 693 then (if i < 670 then (if i < 658 then (if i < 652 then (if i < 649 then (if i < 648 then decide (1 ≤ count647 b) else decide (2 ≤ count647 b)) else (if i < 650 then decide (3 ≤ count647 b) else (if i < 651 then decide (4 ≤ count647 b) else decide (5 ≤ count647 b)))) else (if i < 655 then (if i < 653 then decide (6 ≤ count647 b) else (if i < 654 then decide (7 ≤ count647 b) else decide (8 ≤ count647 b))) else (if i < 656 then decide (1 ≤ count655 b) else (if i < 657 then decide (2 ≤ count655 b) else decide (3 ≤ count655 b))))) else (if i < 664 then (if i < 661 then (if i < 659 then decide (4 ≤ count655 b) else (if i < 660 then decide (5 ≤ count655 b) else decide (6 ≤ count655 b))) else (if i < 662 then decide (7 ≤ count655 b) else (if i < 663 then decide (8 ≤ count655 b) else decide (9 ≤ count655 b)))) else (if i < 667 then (if i < 665 then decide (10 ≤ count655 b) else (if i < 666 then decide (11 ≤ count655 b) else decide (12 ≤ count655 b))) else (if i < 668 then decide (13 ≤ count655 b) else (if i < 669 then decide (14 ≤ count655 b) else decide (15 ≤ count655 b)))))) else (if i < 681 then (if i < 675 then (if i < 672 then (if i < 671 then decide (1 ≤ count670 b) else decide (2 ≤ count670 b)) else (if i < 673 then decide (3 ≤ count670 b) else (if i < 674 then decide (4 ≤ count670 b) else decide (5 ≤ count670 b)))) else (if i < 678 then (if i < 676 then decide (6 ≤ count670 b) else (if i < 677 then decide (7 ≤ count670 b) else decide (8 ≤ count670 b))) else (if i < 679 then decide (9 ≤ count670 b) else (if i < 680 then decide (10 ≤ count670 b) else decide (11 ≤ count670 b))))) else (if i < 687 then (if i < 684 then (if i < 682 then decide (12 ≤ count670 b) else (if i < 683 then decide (13 ≤ count670 b) else decide (14 ≤ count670 b))) else (if i < 685 then decide (15 ≤ count670 b) else (if i < 686 then decide (16 ≤ count670 b) else decide (17 ≤ count670 b)))) else (if i < 690 then (if i < 688 then decide (18 ≤ count670 b) else (if i < 689 then decide (19 ≤ count670 b) else decide (20 ≤ count670 b))) else (if i < 691 then decide (21 ≤ count670 b) else (if i < 692 then decide (22 ≤ count670 b) else decide (23 ≤ count670 b))))))) else (if i < 716 then (if i < 704 then (if i < 698 then (if i < 695 then (if i < 694 then decide (24 ≤ count670 b) else decide (25 ≤ count670 b)) else (if i < 696 then decide (26 ≤ count670 b) else (if i < 697 then decide (27 ≤ count670 b) else decide (28 ≤ count670 b)))) else (if i < 701 then (if i < 699 then decide (29 ≤ count670 b) else (if i < 700 then decide (1 ≤ count699 b) else decide (2 ≤ count699 b))) else (if i < 702 then decide (3 ≤ count699 b) else (if i < 703 then decide (4 ≤ count699 b) else decide (5 ≤ count699 b))))) else (if i < 710 then (if i < 707 then (if i < 705 then decide (6 ≤ count699 b) else (if i < 706 then decide (7 ≤ count699 b) else decide (8 ≤ count699 b))) else (if i < 708 then decide (9 ≤ count699 b) else (if i < 709 then decide (10 ≤ count699 b) else decide (11 ≤ count699 b)))) else (if i < 713 then (if i < 711 then decide (12 ≤ count699 b) else (if i < 712 then decide (13 ≤ count699 b) else decide (14 ≤ count699 b))) else (if i < 714 then decide (15 ≤ count699 b) else (if i < 715 then decide (16 ≤ count699 b) else decide (17 ≤ count699 b)))))) else (if i < 728 then (if i < 722 then (if i < 719 then (if i < 717 then decide (18 ≤ count699 b) else (if i < 718 then decide (19 ≤ count699 b) else decide (20 ≤ count699 b))) else (if i < 720 then decide (21 ≤ count699 b) else (if i < 721 then decide (22 ≤ count699 b) else decide (23 ≤ count699 b)))) else (if i < 725 then (if i < 723 then decide (24 ≤ count699 b) else (if i < 724 then decide (25 ≤ count699 b) else decide (26 ≤ count699 b))) else (if i < 726 then decide (27 ≤ count699 b) else (if i < 727 then decide (28 ≤ count699 b) else decide (29 ≤ count699 b))))) else (if i < 734 then (if i < 731 then (if i < 729 then decide (30 ≤ count699 b) else (if i < 730 then decide (31 ≤ count699 b) else decide (32 ≤ count699 b))) else (if i < 732 then decide (33 ≤ count699 b) else (if i < 733 then decide (34 ≤ count699 b) else decide (35 ≤ count699 b)))) else (if i < 737 then (if i < 735 then decide (36 ≤ count699 b) else (if i < 736 then decide (37 ≤ count699 b) else decide (38 ≤ count699 b))) else (if i < 738 then decide (39 ≤ count699 b) else (if i < 739 then decide (40 ≤ count699 b) else decide (41 ≤ count699 b))))))))))) else (if i < 1110 then (if i < 925 then (if i < 832 then (if i < 786 then (if i < 763 then (if i < 751 then (if i < 745 then (if i < 742 then (if i < 741 then decide (42 ≤ count699 b) else decide (1 ≤ count741 b)) else (if i < 743 then decide (2 ≤ count741 b) else (if i < 744 then decide (1 ≤ count743 b) else decide (2 ≤ count743 b)))) else (if i < 748 then (if i < 746 then decide (3 ≤ count743 b) else (if i < 747 then decide (1 ≤ count746 b) else decide (2 ≤ count746 b))) else (if i < 749 then decide (1 ≤ count748 b) else (if i < 750 then decide (2 ≤ count748 b) else decide (1 ≤ count750 b))))) else (if i < 757 then (if i < 754 then (if i < 752 then decide (2 ≤ count750 b) else (if i < 753 then decide (3 ≤ count750 b) else decide (4 ≤ count750 b))) else (if i < 755 then decide (1 ≤ count754 b) else (if i < 756 then decide (2 ≤ count754 b) else decide (3 ≤ count754 b)))) else (if i < 760 then (if i < 758 then decide (4 ≤ count754 b) else (if i < 759 then decide (5 ≤ count754 b) else decide (6 ≤ count754 b))) else (if i < 761 then decide (7 ≤ count754 b) else (if i < 762 then decide (1 ≤ count761 b) else decide (2 ≤ count761 b)))))) else (if i < 774 then (if i < 768 then (if i < 765 then (if i < 764 then decide (1 ≤ count763 b) else decide (2 ≤ count763 b)) else (if i < 766 then decide (3 ≤ count763 b) else (if i < 767 then decide (1 ≤ count766 b) else decide (2 ≤ count766 b)))) else (if i < 771 then (if i < 769 then decide (1 ≤ count768 b) else (if i < 770 then decide (2 ≤ count768 b) else decide (1 ≤ count770 b))) else (if i < 772 then decide (2 ≤ count770 b) else (if i < 773 then decide (3 ≤ count770 b) else decide (4 ≤ count770 b))))) else (if i < 780 then (if i < 777 then (if i < 775 then decide (1 ≤ count774 b) else (if i < 776 then decide (2 ≤ count774 b) else decide (3 ≤ count774 b))) else (if i < 778 then decide (4 ≤ count774 b) else (if i < 779 then decide (5 ≤ count774 b) else decide (6 ≤ count774 b)))) else (if i < 783 then (if i < 781 then decide (7 ≤ count774 b) else (if i < 782 then decide (1 ≤ count781 b) else decide (2 ≤ count781 b))) else (if i < 784 then decide (3 ≤ count781 b) else (if i < 785 then decide (4 ≤ count781 b) else decide (5 ≤ count781 b))))))) else (if i < 809 then (if i < 797 then (if i < 791 then (if i < 788 then (if i < 787 then decide (6 ≤ count781 b) else decide (7 ≤ count781 b)) else (if i < 789 then decide (8 ≤ count781 b) else (if i < 790 then decide (9 ≤ count781 b) else decide (10 ≤ count781 b)))) else (if i < 794 then (if i < 792 then decide (11 ≤ count781 b) else (if i < 793 then decide (12 ≤ count781 b) else decide (13 ≤ count781 b))) else (if i < 795 then decide (14 ≤ count781 b) else (if i < 796 then decide (1 ≤ count795 b) else decide (2 ≤ count795 b))))) else (if i < 803 then (if i < 800 then (if i < 798 then decide (1 ≤ count797 b) else (if i < 799 then decide (2 ≤ count797 b) else decide (3 ≤ count797 b))) else (if i < 801 then decide (1 ≤ count800 b) else (if i < 802 then decide (2 ≤ count800 b) else decide (1 ≤ count802 b)))) else (if i < 806 then (if i < 804 then decide (2 ≤ count802 b) else (if i < 805 then decide (1 ≤ count804 b) else decide (2 ≤ count804 b))) else (if i < 807 then decide (3 ≤ count804 b) else (if i < 808 then decide (4 ≤ count804 b) else decide (1 ≤ count808 b)))))) else (if i < 820 then (if i < 814 then (if i < 811 then (if i < 810 then decide (2 ≤ count808 b) else decide (3 ≤ count808 b)) else (if i < 812 then decide (4 ≤ count808 b) else (if i < 813 then decide (5 ≤ count808 b) else decide (6 ≤ count808 b)))) else (if i < 817 then (if i < 815 then decide (7 ≤ count808 b) else (if i < 816 then decide (1 ≤ count815 b) else decide (2 ≤ count815 b))) else (if i < 818 then decide (1 ≤ count817 b) else (if i < 819 then decide (2 ≤ count817 b) else decide (3 ≤ count817 b))))) else (if i < 826 then (if i < 823 then (if i < 821 then decide (1 ≤ count820 b) else (if i < 822 then decide (2 ≤ count820 b) else decide (1 ≤ count822 b))) else (if i < 824 then decide (2 ≤ count822 b) else (if i < 825 then decide (1 ≤ count824 b) else decide (2 ≤ count824 b)))) else (if i < 829 then (if i < 827 then decide (3 ≤ count824 b) else (if i < 828 then decide (4 ≤ count824 b) else decide (1 ≤ count828 b))) else (if i < 830 then decide (2 ≤ count828 b) else (if i < 831 then decide (3 ≤ count828 b) else decide (4 ≤ count828 b)))))))) else (if i < 878 then (if i < 855 then (if i < 843 then (if i < 837 then (if i < 834 then (if i < 833 then decide (5 ≤ count828 b) else decide (6 ≤ count828 b)) else (if i < 835 then decide (7 ≤ count828 b) else (if i < 836 then decide (1 ≤ count835 b) else decide (2 ≤ count835 b)))) else (if i < 840 then (if i < 838 then decide (3 ≤ count835 b) else (if i < 839 then decide (4 ≤ count835 b) else decide (5 ≤ count835 b))) else (if i < 841 then decide (6 ≤ count835 b) else (if i < 842 then decide (7 ≤ count835 b) else decide (8 ≤ count835 b))))) else (if i < 849 then (if i < 846 then (if i < 844 then decide (9 ≤ count835 b) else (if i < 845 then decide (10 ≤ count835 b) else decide (11 ≤ count835 b))) else (if i < 847 then decide (12 ≤ count835 b) else (if i < 848 then decide (13 ≤ count835 b) else decide (14 ≤ count835 b)))) else (if i < 852 then (if i < 850 then decide (1 ≤ count849 b) else (if i < 851 then decide (2 ≤ count849 b) else decide (3 ≤ count849 b))) else (if i < 853 then decide (4 ≤ count849 b) else (if i < 854 then decide (5 ≤ count849 b) else decide (6 ≤ count849 b)))))) else (if i < 866 then (if i < 860 then (if i < 857 then (if i < 856 then decide (7 ≤ count849 b) else decide (8 ≤ count849 b)) else (if i < 858 then decide (9 ≤ count849 b) else (if i < 859 then decide (10 ≤ count849 b) else decide (11 ≤ count849 b)))) else (if i < 863 then (if i < 861 then decide (12 ≤ count849 b) else (if i < 862 then decide (13 ≤ count849 b) else decide (14 ≤ count849 b))) else (if i < 864 then decide (15 ≤ count849 b) else (if i < 865 then decide (16 ≤ count849 b) else decide (17 ≤ count849 b))))) else (if i < 872 then (if i < 869 then (if i < 867 then decide (1 ≤ count866 b) else (if i < 868 then decide (2 ≤ count866 b) else decide (1 ≤ count868 b))) else (if i < 870 then decide (2 ≤ count868 b) else (if i < 871 then decide (3 ≤ count868 b) else decide (1 ≤ count871 b)))) else (if i < 875 then (if i < 873 then decide (2 ≤ count871 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b))) else (if i < 876 then decide (1 ≤ count875 b) else (if i < 877 then decide (2 ≤ count875 b) else decide (3 ≤ count875 b))))))) else (if i < 901 then (if i < 889 then (if i < 883 then (if i < 880 then (if i < 879 then decide (4 ≤ count875 b) else decide (1 ≤ count879 b)) else (if i < 881 then decide (2 ≤ count879 b) else (if i < 882 then decide (3 ≤ count879 b) else decide (4 ≤ count879 b)))) else (if i < 886 then (if i < 884 then decide (5 ≤ count879 b) else (if i < 885 then decide (6 ≤ count879 b) else decide (7 ≤ count879 b))) else (if i < 887 then decide (1 ≤ count886 b) else (if i < 888 then decide (2 ≤ count886 b) else decide (1 ≤ count888 b))))) else (if i < 895 then (if i < 892 then (if i < 890 then decide (2 ≤ count888 b) else (if i < 891 then decide (3 ≤ count888 b) else decide (1 ≤ count891 b))) else (if i < 893 then decide (2 ≤ count891 b) else (if i < 894 then decide (1 ≤ count893 b) else decide (2 ≤ count893 b)))) else (if i < 898 then (if i < 896 then decide (1 ≤ count895 b) else (if i < 897 then decide (2 ≤ count895 b) else decide (3 ≤ count895 b))) else (if i < 899 then decide (4 ≤ count895 b) else (if i < 900 then decide (1 ≤ count899 b) else decide (2 ≤ count899 b)))))) else (if i < 913 then (if i < 907 then (if i < 904 then (if i < 902 then decide (3 ≤ count899 b) else (if i < 903 then decide (4 ≤ count899 b) else decide (5 ≤ count899 b))) else (if i < 905 then decide (6 ≤ count899 b) else (if i < 906 then decide (7 ≤ count899 b) else decide (1 ≤ count906 b)))) else (if i < 910 then (if i < 908 then decide (2 ≤ count906 b) else (if i < 909 then decide (3 ≤ count906 b) else decide (4 ≤ count906 b))) else (if i < 911 then decide (5 ≤ count906 b) else (if i < 912 then decide (6 ≤ count906 b) else decide (7 ≤ count906 b))))) else (if i < 919 then (if i < 916 then (if i < 914 then decide (8 ≤ count906 b) else (if i < 915 then decide (9 ≤ count906 b) else decide (10 ≤ count906 b))) else (if i < 917 then decide (11 ≤ count906 b) else (if i < 918 then decide (12 ≤ count906 b) else decide (13 ≤ count906 b)))) else (if i < 922 then (if i < 920 then decide (14 ≤ count906 b) else (if i < 921 then decide (1 ≤ count920 b) else decide (2 ≤ count920 b))) else (if i < 923 then decide (1 ≤ count922 b) else (if i < 924 then decide (2 ≤ count922 b) else decide (3 ≤ count922 b))))))))) else (if i < 1017 then (if i < 971 then (if i < 948 then (if i < 936 then (if i < 930 then (if i < 927 then (if i < 926 then decide (1 ≤ count925 b) else decide (2 ≤ count925 b)) else (if i < 928 then decide (1 ≤ count927 b) else (if i < 929 then decide (2 ≤ count927 b) else decide (1 ≤ count929 b)))) else (if i < 933 then (if i < 931 then decide (2 ≤ count929 b) else (if i < 932 then decide (3 ≤ count929 b) else decide (4 ≤ count929 b))) else (if i < 934 then decide (1 ≤ count933 b) else (if i < 935 then decide (2 ≤ count933 b) else decide (3 ≤ count933 b))))) else (if i < 942 then (if i < 939 then (if i < 937 then decide (4 ≤ count933 b) else (if i < 938 then decide (5 ≤ count933 b) else decide (6 ≤ count933 b))) else (if i < 940 then decide (7 ≤ count933 b) else (if i < 941 then decide (1 ≤ count940 b) else decide (2 ≤ count940 b)))) else (if i < 945 then (if i < 943 then decide (1 ≤ count942 b) else (if i < 944 then decide (2 ≤ count942 b) else decide (1 ≤ count944 b))) else (if i < 946 then decide (2 ≤ count944 b) else (if i < 947 then decide (3 ≤ count944 b) else decide (4 ≤ count944 b)))))) else (if i < 959 then (if i < 953 then (if i < 950 then (if i < 949 then decide (1 ≤ count948 b) else decide (2 ≤ count948 b)) else (if i < 951 then decide (1 ≤ count950 b) else (if i < 952 then decide (2 ≤ count950 b) else decide (1 ≤ count952 b)))) else (if i < 956 then (if i < 954 then decide (2 ≤ count952 b) else (if i < 955 then decide (3 ≤ count952 b) else decide (4 ≤ count952 b))) else (if i < 957 then decide (1 ≤ count956 b) else (if i < 958 then decide (2 ≤ count956 b) else decide (3 ≤ count956 b))))) else (if i < 965 then (if i < 962 then (if i < 960 then decide (4 ≤ count956 b) else (if i < 961 then decide (5 ≤ count956 b) else decide (6 ≤ count956 b))) else (if i < 963 then decide (7 ≤ count956 b) else (if i < 964 then decide (8 ≤ count956 b) else decide (1 ≤ count964 b)))) else (if i < 968 then (if i < 966 then decide (2 ≤ count964 b) else (if i < 967 then decide (3 ≤ count964 b) else decide (4 ≤ count964 b))) else (if i < 969 then decide (5 ≤ count964 b) else (if i < 970 then decide (6 ≤ count964 b) else decide (7 ≤ count964 b))))))) else (if i < 994 then (if i < 982 then (if i < 976 then (if i < 973 then (if i < 972 then decide (8 ≤ count964 b) else decide (9 ≤ count964 b)) else (if i < 974 then decide (10 ≤ count964 b) else (if i < 975 then decide (11 ≤ count964 b) else decide (12 ≤ count964 b)))) else (if i < 979 then (if i < 977 then decide (13 ≤ count964 b) else (if i < 978 then decide (14 ≤ count964 b) else decide (15 ≤ count964 b))) else (if i < 980 then decide (1 ≤ count979 b) else (if i < 981 then decide (2 ≤ count979 b) else decide (3 ≤ count979 b))))) else (if i < 988 then (if i < 985 then (if i < 983 then decide (4 ≤ count979 b) else (if i < 984 then decide (5 ≤ count979 b) else decide (6 ≤ count979 b))) else (if i < 986 then decide (7 ≤ count979 b) else (if i < 987 then decide (8 ≤ count979 b) else decide (9 ≤ count979 b)))) else (if i < 991 then (if i < 989 then decide (10 ≤ count979 b) else (if i < 990 then decide (11 ≤ count979 b) else decide (12 ≤ count979 b))) else (if i < 992 then decide (13 ≤ count979 b) else (if i < 993 then decide (14 ≤ count979 b) else decide (15 ≤ count979 b)))))) else (if i < 1005 then (if i < 999 then (if i < 996 then (if i < 995 then decide (16 ≤ count979 b) else decide (17 ≤ count979 b)) else (if i < 997 then decide (1 ≤ count996 b) else (if i < 998 then decide (2 ≤ count996 b) else decide (3 ≤ count996 b)))) else (if i < 1002 then (if i < 1000 then decide (4 ≤ count996 b) else (if i < 1001 then decide (5 ≤ count996 b) else decide (6 ≤ count996 b))) else (if i < 1003 then decide (7 ≤ count996 b) else (if i < 1004 then decide (8 ≤ count996 b) else decide (9 ≤ count996 b))))) else (if i < 1011 then (if i < 1008 then (if i < 1006 then decide (10 ≤ count996 b) else (if i < 1007 then decide (11 ≤ count996 b) else decide (12 ≤ count996 b))) else (if i < 1009 then decide (13 ≤ count996 b) else (if i < 1010 then decide (14 ≤ count996 b) else decide (15 ≤ count996 b)))) else (if i < 1014 then (if i < 1012 then decide (16 ≤ count996 b) else (if i < 1013 then decide (17 ≤ count996 b) else decide (1 ≤ count1013 b))) else (if i < 1015 then decide (2 ≤ count1013 b) else (if i < 1016 then decide (1 ≤ count1015 b) else decide (2 ≤ count1015 b)))))))) else (if i < 1063 then (if i < 1040 then (if i < 1028 then (if i < 1022 then (if i < 1019 then (if i < 1018 then decide (3 ≤ count1015 b) else decide (1 ≤ count1018 b)) else (if i < 1020 then decide (2 ≤ count1018 b) else (if i < 1021 then decide (1 ≤ count1020 b) else decide (2 ≤ count1020 b)))) else (if i < 1025 then (if i < 1023 then decide (3 ≤ count1020 b) else (if i < 1024 then decide (1 ≤ count1023 b) else decide (2 ≤ count1023 b))) else (if i < 1026 then decide (3 ≤ count1023 b) else (if i < 1027 then decide (4 ≤ count1023 b) else decide (5 ≤ count1023 b))))) else (if i < 1034 then (if i < 1031 then (if i < 1029 then decide (6 ≤ count1023 b) else (if i < 1030 then decide (1 ≤ count1029 b) else decide (2 ≤ count1029 b))) else (if i < 1032 then decide (1 ≤ count1031 b) else (if i < 1033 then decide (2 ≤ count1031 b) else decide (3 ≤ count1031 b)))) else (if i < 1037 then (if i < 1035 then decide (1 ≤ count1034 b) else (if i < 1036 then decide (2 ≤ count1034 b) else decide (1 ≤ count1036 b))) else (if i < 1038 then decide (2 ≤ count1036 b) else (if i < 1039 then decide (3 ≤ count1036 b) else decide (1 ≤ count1039 b)))))) else (if i < 1051 then (if i < 1045 then (if i < 1042 then (if i < 1041 then decide (2 ≤ count1039 b) else decide (3 ≤ count1039 b)) else (if i < 1043 then decide (4 ≤ count1039 b) else (if i < 1044 then decide (5 ≤ count1039 b) else decide (6 ≤ count1039 b)))) else (if i < 1048 then (if i < 1046 then decide (1 ≤ count1045 b) else (if i < 1047 then decide (2 ≤ count1045 b) else decide (3 ≤ count1045 b))) else (if i < 1049 then decide (4 ≤ count1045 b) else (if i < 1050 then decide (5 ≤ count1045 b) else decide (6 ≤ count1045 b))))) else (if i < 1057 then (if i < 1054 then (if i < 1052 then decide (7 ≤ count1045 b) else (if i < 1053 then decide (8 ≤ count1045 b) else decide (9 ≤ count1045 b))) else (if i < 1055 then decide (10 ≤ count1045 b) else (if i < 1056 then decide (11 ≤ count1045 b) else decide (12 ≤ count1045 b)))) else (if i < 1060 then (if i < 1058 then decide (1 ≤ count1057 b) else (if i < 1059 then decide (2 ≤ count1057 b) else decide (1 ≤ count1059 b))) else (if i < 1061 then decide (2 ≤ count1059 b) else (if i < 1062 then decide (3 ≤ count1059 b) else decide (1 ≤ count1062 b))))))) else (if i < 1086 then (if i < 1074 then (if i < 1068 then (if i < 1065 then (if i < 1064 then decide (2 ≤ count1062 b) else decide (1 ≤ count1064 b)) else (if i < 1066 then decide (2 ≤ count1064 b) else (if i < 1067 then decide (3 ≤ count1064 b) else decide (1 ≤ count1067 b)))) else (if i < 1071 then (if i < 1069 then decide (2 ≤ count1067 b) else (if i < 1070 then decide (3 ≤ count1067 b) else decide (4 ≤ count1067 b))) else (if i < 1072 then decide (5 ≤ count1067 b) else (if i < 1073 then decide (6 ≤ count1067 b) else decide (1 ≤ count1073 b))))) else (if i < 1080 then (if i < 1077 then (if i < 1075 then decide (2 ≤ count1073 b) else (if i < 1076 then decide (1 ≤ count1075 b) else decide (2 ≤ count1075 b))) else (if i < 1078 then decide (3 ≤ count1075 b) else (if i < 1079 then decide (1 ≤ count1078 b) else decide (2 ≤ count1078 b)))) else (if i < 1083 then (if i < 1081 then decide (1 ≤ count1080 b) else (if i < 1082 then decide (2 ≤ count1080 b) else decide (3 ≤ count1080 b))) else (if i < 1084 then decide (1 ≤ count1083 b) else (if i < 1085 then decide (2 ≤ count1083 b) else decide (3 ≤ count1083 b)))))) else (if i < 1098 then (if i < 1092 then (if i < 1089 then (if i < 1087 then decide (4 ≤ count1083 b) else (if i < 1088 then decide (5 ≤ count1083 b) else decide (6 ≤ count1083 b))) else (if i < 1090 then decide (1 ≤ count1089 b) else (if i < 1091 then decide (2 ≤ count1089 b) else decide (3 ≤ count1089 b)))) else (if i < 1095 then (if i < 1093 then decide (4 ≤ count1089 b) else (if i < 1094 then decide (5 ≤ count1089 b) else decide (6 ≤ count1089 b))) else (if i < 1096 then decide (7 ≤ count1089 b) else (if i < 1097 then decide (8 ≤ count1089 b) else decide (9 ≤ count1089 b))))) else (if i < 1104 then (if i < 1101 then (if i < 1099 then decide (10 ≤ count1089 b) else (if i < 1100 then decide (11 ≤ count1089 b) else decide (12 ≤ count1089 b))) else (if i < 1102 then decide (1 ≤ count1101 b) else (if i < 1103 then decide (2 ≤ count1101 b) else decide (3 ≤ count1101 b)))) else (if i < 1107 then (if i < 1105 then decide (4 ≤ count1101 b) else (if i < 1106 then decide (5 ≤ count1101 b) else decide (6 ≤ count1101 b))) else (if i < 1108 then decide (7 ≤ count1101 b) else (if i < 1109 then decide (8 ≤ count1101 b) else decide (9 ≤ count1101 b)))))))))) else (if i < 1295 then (if i < 1202 then (if i < 1156 then (if i < 1133 then (if i < 1121 then (if i < 1115 then (if i < 1112 then (if i < 1111 then decide (10 ≤ count1101 b) else decide (11 ≤ count1101 b)) else (if i < 1113 then decide (12 ≤ count1101 b) else (if i < 1114 then decide (13 ≤ count1101 b) else decide (14 ≤ count1101 b)))) else (if i < 1118 then (if i < 1116 then decide (15 ≤ count1101 b) else (if i < 1117 then decide (16 ≤ count1101 b) else decide (17 ≤ count1101 b))) else (if i < 1119 then decide (18 ≤ count1101 b) else (if i < 1120 then decide (19 ≤ count1101 b) else decide (20 ≤ count1101 b))))) else (if i < 1127 then (if i < 1124 then (if i < 1122 then decide (21 ≤ count1101 b) else (if i < 1123 then decide (22 ≤ count1101 b) else decide (23 ≤ count1101 b))) else (if i < 1125 then decide (24 ≤ count1101 b) else (if i < 1126 then decide (1 ≤ count1125 b) else decide (2 ≤ count1125 b)))) else (if i < 1130 then (if i < 1128 then decide (1 ≤ count1127 b) else (if i < 1129 then decide (2 ≤ count1127 b) else decide (3 ≤ count1127 b))) else (if i < 1131 then decide (1 ≤ count1130 b) else (if i < 1132 then decide (2 ≤ count1130 b) else decide (1 ≤ count1132 b)))))) else (if i < 1144 then (if i < 1138 then (if i < 1135 then (if i < 1134 then decide (2 ≤ count1132 b) else decide (3 ≤ count1132 b)) else (if i < 1136 then decide (1 ≤ count1135 b) else (if i < 1137 then decide (2 ≤ count1135 b) else decide (3 ≤ count1135 b)))) else (if i < 1141 then (if i < 1139 then decide (4 ≤ count1135 b) else (if i < 1140 then decide (5 ≤ count1135 b) else decide (6 ≤ count1135 b))) else (if i < 1142 then decide (1 ≤ count1141 b) else (if i < 1143 then decide (2 ≤ count1141 b) else decide (1 ≤ count1143 b))))) else (if i < 1150 then (if i < 1147 then (if i < 1145 then decide (2 ≤ count1143 b) else (if i < 1146 then decide (3 ≤ count1143 b) else decide (1 ≤ count1146 b))) else (if i < 1148 then decide (2 ≤ count1146 b) else (if i < 1149 then decide (1 ≤ count1148 b) else decide (2 ≤ count1148 b)))) else (if i < 1153 then (if i < 1151 then decide (3 ≤ count1148 b) else (if i < 1152 then decide (1 ≤ count1151 b) else decide (2 ≤ count1151 b))) else (if i < 1154 then decide (3 ≤ count1151 b) else (if i < 1155 then decide (4 ≤ count1151 b) else decide (5 ≤ count1151 b))))))) else (if i < 1179 then (if i < 1167 then (if i < 1161 then (if i < 1158 then (if i < 1157 then decide (6 ≤ count1151 b) else decide (1 ≤ count1157 b)) else (if i < 1159 then decide (2 ≤ count1157 b) else (if i < 1160 then decide (3 ≤ count1157 b) else decide (4 ≤ count1157 b)))) else (if i < 1164 then (if i < 1162 then decide (5 ≤ count1157 b) else (if i < 1163 then decide (6 ≤ count1157 b) else decide (7 ≤ count1157 b))) else (if i < 1165 then decide (8 ≤ count1157 b) else (if i < 1166 then decide (9 ≤ count1157 b) else decide (10 ≤ count1157 b))))) else (if i < 1173 then (if i < 1170 then (if i < 1168 then decide (11 ≤ count1157 b) else (if i < 1169 then decide (12 ≤ count1157 b) else decide (1 ≤ count1169 b))) else (if i < 1171 then decide (2 ≤ count1169 b) else (if i < 1172 then decide (1 ≤ count1171 b) else decide (2 ≤ count1171 b)))) else (if i < 1176 then (if i < 1174 then decide (3 ≤ count1171 b) else (if i < 1175 then decide (1 ≤ count1174 b) else decide (2 ≤ count1174 b))) else (if i < 1177 then decide (1 ≤ count1176 b) else (if i < 1178 then decide (2 ≤ count1176 b) else decide (3 ≤ count1176 b)))))) else (if i < 1190 then (if i < 1184 then (if i < 1181 then (if i < 1180 then decide (1 ≤ count1179 b) else decide (2 ≤ count1179 b)) else (if i < 1182 then decide (3 ≤ count1179 b) else (if i < 1183 then decide (4 ≤ count1179 b) else decide (5 ≤ count1179 b)))) else (if i < 1187 then (if i < 1185 then decide (6 ≤ count1179 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))) else (if i < 1188 then decide (1 ≤ count1187 b) else (if i < 1189 then decide (2 ≤ count1187 b) else decide (3 ≤ count1187 b))))) else (if i < 1196 then (if i < 1193 then (if i < 1191 then decide (1 ≤ count1190 b) else (if i < 1192 then decide (2 ≤ count1190 b) else decide (1 ≤ count1192 b))) else (if i < 1194 then decide (2 ≤ count1192 b) else (if i < 1195 then decide (1 ≤ count1194 b) else decide (2 ≤ count1194 b)))) else (if i < 1199 then (if i < 1197 then decide (3 ≤ count1194 b) else (if i < 1198 then decide (4 ≤ count1194 b) else decide (1 ≤ count1198 b))) else (if i < 1200 then decide (2 ≤ count1198 b) else (if i < 1201 then decide (3 ≤ count1198 b) else decide (4 ≤ count1198 b)))))))) else (if i < 1248 then (if i < 1225 then (if i < 1213 then (if i < 1207 then (if i < 1204 then (if i < 1203 then decide (5 ≤ count1198 b) else decide (6 ≤ count1198 b)) else (if i < 1205 then decide (7 ≤ count1198 b) else (if i < 1206 then decide (1 ≤ count1205 b) else decide (2 ≤ count1205 b)))) else (if i < 1210 then (if i < 1208 then decide (3 ≤ count1205 b) else (if i < 1209 then decide (4 ≤ count1205 b) else decide (5 ≤ count1205 b))) else (if i < 1211 then decide (6 ≤ count1205 b) else (if i < 1212 then decide (7 ≤ count1205 b) else decide (8 ≤ count1205 b))))) else (if i < 1219 then (if i < 1216 then (if i < 1214 then decide (9 ≤ count1205 b) else (if i < 1215 then decide (10 ≤ count1205 b) else decide (11 ≤ count1205 b))) else (if i < 1217 then decide (12 ≤ count1205 b) else (if i < 1218 then decide (13 ≤ count1205 b) else decide (1 ≤ count1218 b)))) else (if i < 1222 then (if i < 1220 then decide (2 ≤ count1218 b) else (if i < 1221 then decide (3 ≤ count1218 b) else decide (4 ≤ count1218 b))) else (if i < 1223 then decide (5 ≤ count1218 b) else (if i < 1224 then decide (6 ≤ count1218 b) else decide (7 ≤ count1218 b)))))) else (if i < 1236 then (if i < 1230 then (if i < 1227 then (if i < 1226 then decide (8 ≤ count1218 b) else decide (9 ≤ count1218 b)) else (if i < 1228 then decide (10 ≤ count1218 b) else (if i < 1229 then decide (11 ≤ count1218 b) else decide (12 ≤ count1218 b)))) else (if i < 1233 then (if i < 1231 then decide (13 ≤ count1218 b) else (if i < 1232 then decide (14 ≤ count1218 b) else decide (15 ≤ count1218 b))) else (if i < 1234 then decide (16 ≤ count1218 b) else (if i < 1235 then decide (17 ≤ count1218 b) else decide (18 ≤ count1218 b))))) else (if i < 1242 then (if i < 1239 then (if i < 1237 then decide (19 ≤ count1218 b) else (if i < 1238 then decide (20 ≤ count1218 b) else decide (21 ≤ count1218 b))) else (if i < 1240 then decide (22 ≤ count1218 b) else (if i < 1241 then decide (23 ≤ count1218 b) else decide (24 ≤ count1218 b)))) else (if i < 1245 then (if i < 1243 then decide (25 ≤ count1218 b) else (if i < 1244 then decide (1 ≤ count1243 b) else decide (2 ≤ count1243 b))) else (if i < 1246 then decide (3 ≤ count1243 b) else (if i < 1247 then decide (4 ≤ count1243 b) else decide (5 ≤ count1243 b))))))) else (if i < 1271 then (if i < 1259 then (if i < 1253 then (if i < 1250 then (if i < 1249 then decide (6 ≤ count1243 b) else decide (7 ≤ count1243 b)) else (if i < 1251 then decide (8 ≤ count1243 b) else (if i < 1252 then decide (9 ≤ count1243 b) else decide (10 ≤ count1243 b)))) else (if i < 1256 then (if i < 1254 then decide (11 ≤ count1243 b) else (if i < 1255 then decide (12 ≤ count1243 b) else decide (13 ≤ count1243 b))) else (if i < 1257 then decide (14 ≤ count1243 b) else (if i < 1258 then decide (15 ≤ count1243 b) else decide (16 ≤ count1243 b))))) else (if i < 1265 then (if i < 1262 then (if i < 1260 then decide (17 ≤ count1243 b) else (if i < 1261 then decide (18 ≤ count1243 b) else decide (19 ≤ count1243 b))) else (if i < 1263 then decide (20 ≤ count1243 b) else (if i < 1264 then decide (21 ≤ count1243 b) else decide (22 ≤ count1243 b)))) else (if i < 1268 then (if i < 1266 then decide (23 ≤ count1243 b) else (if i < 1267 then decide (24 ≤ count1243 b) else decide (25 ≤ count1243 b))) else (if i < 1269 then decide (26 ≤ count1243 b) else (if i < 1270 then decide (27 ≤ count1243 b) else decide (28 ≤ count1243 b)))))) else (if i < 1283 then (if i < 1277 then (if i < 1274 then (if i < 1272 then decide (29 ≤ count1243 b) else (if i < 1273 then decide (30 ≤ count1243 b) else decide (31 ≤ count1243 b))) else (if i < 1275 then decide (32 ≤ count1243 b) else (if i < 1276 then decide (33 ≤ count1243 b) else decide (34 ≤ count1243 b)))) else (if i < 1280 then (if i < 1278 then decide (35 ≤ count1243 b) else (if i < 1279 then decide (36 ≤ count1243 b) else decide (37 ≤ count1243 b))) else (if i < 1281 then decide (38 ≤ count1243 b) else (if i < 1282 then decide (39 ≤ count1243 b) else decide (40 ≤ count1243 b))))) else (if i < 1289 then (if i < 1286 then (if i < 1284 then decide (41 ≤ count1243 b) else (if i < 1285 then decide (42 ≤ count1243 b) else decide (1 ≤ count1285 b))) else (if i < 1287 then decide (2 ≤ count1285 b) else (if i < 1288 then decide (1 ≤ count1287 b) else decide (2 ≤ count1287 b)))) else (if i < 1292 then (if i < 1290 then decide (3 ≤ count1287 b) else (if i < 1291 then decide (1 ≤ count1290 b) else decide (2 ≤ count1290 b))) else (if i < 1293 then decide (1 ≤ count1292 b) else (if i < 1294 then decide (2 ≤ count1292 b) else decide (3 ≤ count1292 b))))))))) else (if i < 1387 then (if i < 1341 then (if i < 1318 then (if i < 1306 then (if i < 1300 then (if i < 1297 then (if i < 1296 then decide (1 ≤ count1295 b) else decide (2 ≤ count1295 b)) else (if i < 1298 then decide (3 ≤ count1295 b) else (if i < 1299 then decide (4 ≤ count1295 b) else decide (5 ≤ count1295 b)))) else (if i < 1303 then (if i < 1301 then decide (6 ≤ count1295 b) else (if i < 1302 then decide (1 ≤ count1301 b) else decide (2 ≤ count1301 b))) else (if i < 1304 then decide (1 ≤ count1303 b) else (if i < 1305 then decide (2 ≤ count1303 b) else decide (3 ≤ count1303 b))))) else (if i < 1312 then (if i < 1309 then (if i < 1307 then decide (1 ≤ count1306 b) else (if i < 1308 then decide (2 ≤ count1306 b) else decide (1 ≤ count1308 b))) else (if i < 1310 then decide (2 ≤ count1308 b) else (if i < 1311 then decide (3 ≤ count1308 b) else decide (1 ≤ count1311 b)))) else (if i < 1315 then (if i < 1313 then decide (2 ≤ count1311 b) else (if i < 1314 then decide (3 ≤ count1311 b) else decide (4 ≤ count1311 b))) else (if i < 1316 then decide (5 ≤ count1311 b) else (if i < 1317 then decide (6 ≤ count1311 b) else decide (1 ≤ count1317 b)))))) else (if i < 1329 then (if i < 1323 then (if i < 1320 then (if i < 1319 then decide (2 ≤ count1317 b) else decide (3 ≤ count1317 b)) else (if i < 1321 then decide (4 ≤ count1317 b) else (if i < 1322 then decide (5 ≤ count1317 b) else decide (6 ≤ count1317 b)))) else (if i < 1326 then (if i < 1324 then decide (7 ≤ count1317 b) else (if i < 1325 then decide (8 ≤ count1317 b) else decide (9 ≤ count1317 b))) else (if i < 1327 then decide (1 ≤ count1326 b) else (if i < 1328 then decide (2 ≤ count1326 b) else decide (1 ≤ count1328 b))))) else (if i < 1335 then (if i < 1332 then (if i < 1330 then decide (2 ≤ count1328 b) else (if i < 1331 then decide (3 ≤ count1328 b) else decide (1 ≤ count1331 b))) else (if i < 1333 then decide (2 ≤ count1331 b) else (if i < 1334 then decide (1 ≤ count1333 b) else decide (2 ≤ count1333 b)))) else (if i < 1338 then (if i < 1336 then decide (3 ≤ count1333 b) else (if i < 1337 then decide (1 ≤ count1336 b) else decide (2 ≤ count1336 b))) else (if i < 1339 then decide (3 ≤ count1336 b) else (if i < 1340 then decide (4 ≤ count1336 b) else decide (5 ≤ count1336 b))))))) else (if i < 1364 then (if i < 1352 then (if i < 1346 then (if i < 1343 then (if i < 1342 then decide (6 ≤ count1336 b) else decide (1 ≤ count1342 b)) else (if i < 1344 then decide (2 ≤ count1342 b) else (if i < 1345 then decide (1 ≤ count1344 b) else decide (2 ≤ count1344 b)))) else (if i < 1349 then (if i < 1347 then decide (3 ≤ count1344 b) else (if i < 1348 then decide (1 ≤ count1347 b) else decide (2 ≤ count1347 b))) else (if i < 1350 then decide (1 ≤ count1349 b) else (if i < 1351 then decide (2 ≤ count1349 b) else decide (3 ≤ count1349 b))))) else (if i < 1358 then (if i < 1355 then (if i < 1353 then decide (1 ≤ count1352 b) else (if i < 1354 then decide (2 ≤ count1352 b) else decide (3 ≤ count1352 b))) else (if i < 1356 then decide (4 ≤ count1352 b) else (if i < 1357 then decide (5 ≤ count1352 b) else decide (6 ≤ count1352 b)))) else (if i < 1361 then (if i < 1359 then decide (1 ≤ count1358 b) else (if i < 1360 then decide (2 ≤ count1358 b) else decide (3 ≤ count1358 b))) else (if i < 1362 then decide (4 ≤ count1358 b) else (if i < 1363 then decide (5 ≤ count1358 b) else decide (6 ≤ count1358 b)))))) else (if i < 1375 then (if i < 1369 then (if i < 1366 then (if i < 1365 then decide (7 ≤ count1358 b) else decide (8 ≤ count1358 b)) else (if i < 1367 then decide (9 ≤ count1358 b) else (if i < 1368 then decide (1 ≤ count1367 b) else decide (2 ≤ count1367 b)))) else (if i < 1372 then (if i < 1370 then decide (3 ≤ count1367 b) else (if i < 1371 then decide (4 ≤ count1367 b) else decide (5 ≤ count1367 b))) else (if i < 1373 then decide (6 ≤ count1367 b) else (if i < 1374 then decide (7 ≤ count1367 b) else decide (8 ≤ count1367 b))))) else (if i < 1381 then (if i < 1378 then (if i < 1376 then decide (9 ≤ count1367 b) else (if i < 1377 then decide (1 ≤ count1376 b) else decide (2 ≤ count1376 b))) else (if i < 1379 then decide (1 ≤ count1378 b) else (if i < 1380 then decide (2 ≤ count1378 b) else decide (3 ≤ count1378 b)))) else (if i < 1384 then (if i < 1382 then decide (1 ≤ count1381 b) else (if i < 1383 then decide (2 ≤ count1381 b) else decide (1 ≤ count1383 b))) else (if i < 1385 then decide (2 ≤ count1383 b) else (if i < 1386 then decide (3 ≤ count1383 b) else decide (1 ≤ count1386 b)))))))) else (if i < 1433 then (if i < 1410 then (if i < 1398 then (if i < 1392 then (if i < 1389 then (if i < 1388 then decide (2 ≤ count1386 b) else decide (3 ≤ count1386 b)) else (if i < 1390 then decide (4 ≤ count1386 b) else (if i < 1391 then decide (5 ≤ count1386 b) else decide (6 ≤ count1386 b)))) else (if i < 1395 then (if i < 1393 then decide (1 ≤ count1392 b) else (if i < 1394 then decide (2 ≤ count1392 b) else decide (1 ≤ count1394 b))) else (if i < 1396 then decide (2 ≤ count1394 b) else (if i < 1397 then decide (3 ≤ count1394 b) else decide (1 ≤ count1397 b))))) else (if i < 1404 then (if i < 1401 then (if i < 1399 then decide (2 ≤ count1397 b) else (if i < 1400 then decide (1 ≤ count1399 b) else decide (2 ≤ count1399 b))) else (if i < 1402 then decide (3 ≤ count1399 b) else (if i < 1403 then decide (1 ≤ count1402 b) else decide (2 ≤ count1402 b)))) else (if i < 1407 then (if i < 1405 then decide (3 ≤ count1402 b) else (if i < 1406 then decide (4 ≤ count1402 b) else decide (5 ≤ count1402 b))) else (if i < 1408 then decide (6 ≤ count1402 b) else (if i < 1409 then decide (1 ≤ count1408 b) else decide (2 ≤ count1408 b)))))) else (if i < 1421 then (if i < 1415 then (if i < 1412 then (if i < 1411 then decide (3 ≤ count1408 b) else decide (4 ≤ count1408 b)) else (if i < 1413 then decide (5 ≤ count1408 b) else (if i < 1414 then decide (6 ≤ count1408 b) else decide (7 ≤ count1408 b)))) else (if i < 1418 then (if i < 1416 then decide (8 ≤ count1408 b) else (if i < 1417 then decide (9 ≤ count1408 b) else decide (1 ≤ count1417 b))) else (if i < 1419 then decide (2 ≤ count1417 b) else (if i < 1420 then decide (1 ≤ count1419 b) else decide (2 ≤ count1419 b))))) else (if i < 1427 then (if i < 1424 then (if i < 1422 then decide (3 ≤ count1419 b) else (if i < 1423 then decide (1 ≤ count1422 b) else decide (2 ≤ count1422 b))) else (if i < 1425 then decide (1 ≤ count1424 b) else (if i < 1426 then decide (2 ≤ count1424 b) else decide (3 ≤ count1424 b)))) else (if i < 1430 then (if i < 1428 then decide (1 ≤ count1427 b) else (if i < 1429 then decide (2 ≤ count1427 b) else decide (3 ≤ count1427 b))) else (if i < 1431 then decide (4 ≤ count1427 b) else (if i < 1432 then decide (5 ≤ count1427 b) else decide (6 ≤ count1427 b))))))) else (if i < 1456 then (if i < 1444 then (if i < 1438 then (if i < 1435 then (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b)) else (if i < 1436 then decide (1 ≤ count1435 b) else (if i < 1437 then decide (2 ≤ count1435 b) else decide (3 ≤ count1435 b)))) else (if i < 1441 then (if i < 1439 then decide (1 ≤ count1438 b) else (if i < 1440 then decide (2 ≤ count1438 b) else decide (1 ≤ count1440 b))) else (if i < 1442 then decide (2 ≤ count1440 b) else (if i < 1443 then decide (1 ≤ count1442 b) else decide (2 ≤ count1442 b))))) else (if i < 1450 then (if i < 1447 then (if i < 1445 then decide (3 ≤ count1442 b) else (if i < 1446 then decide (4 ≤ count1442 b) else decide (1 ≤ count1446 b))) else (if i < 1448 then decide (2 ≤ count1446 b) else (if i < 1449 then decide (3 ≤ count1446 b) else decide (4 ≤ count1446 b)))) else (if i < 1453 then (if i < 1451 then decide (5 ≤ count1446 b) else (if i < 1452 then decide (6 ≤ count1446 b) else decide (7 ≤ count1446 b))) else (if i < 1454 then decide (1 ≤ count1453 b) else (if i < 1455 then decide (2 ≤ count1453 b) else decide (3 ≤ count1453 b)))))) else (if i < 1468 then (if i < 1462 then (if i < 1459 then (if i < 1457 then decide (4 ≤ count1453 b) else (if i < 1458 then decide (5 ≤ count1453 b) else decide (6 ≤ count1453 b))) else (if i < 1460 then decide (7 ≤ count1453 b) else (if i < 1461 then decide (8 ≤ count1453 b) else decide (9 ≤ count1453 b)))) else (if i < 1465 then (if i < 1463 then decide (1 ≤ count1462 b) else (if i < 1464 then decide (2 ≤ count1462 b) else decide (3 ≤ count1462 b))) else (if i < 1466 then decide (4 ≤ count1462 b) else (if i < 1467 then decide (5 ≤ count1462 b) else decide (6 ≤ count1462 b))))) else (if i < 1474 then (if i < 1471 then (if i < 1469 then decide (7 ≤ count1462 b) else (if i < 1470 then decide (8 ≤ count1462 b) else decide (9 ≤ count1462 b))) else (if i < 1472 then decide (1 ≤ count1471 b) else (if i < 1473 then decide (2 ≤ count1471 b) else decide (3 ≤ count1471 b)))) else (if i < 1477 then (if i < 1475 then decide (4 ≤ count1471 b) else (if i < 1476 then decide (5 ≤ count1471 b) else decide (6 ≤ count1471 b))) else (if i < 1478 then decide (7 ≤ count1471 b) else (if i < 1479 then decide (8 ≤ count1471 b) else decide (9 ≤ count1471 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (5 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (6 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (7 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (9 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (13 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (15 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (18 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (19 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (22 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (26 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (28 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (29 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (97 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (104 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (105 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (109 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (118 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (122 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (124 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (126 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (130 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (134 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (142 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (166 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (173 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (175 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (182 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (186 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (188 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (189 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (190 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (198 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (258 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (260 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (262 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (263 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (265 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (266 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (268 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (270 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (276 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (277 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (279 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (282 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (283 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (326 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (328 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (329 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (333 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (342 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (346 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (348 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (350 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (358 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (360 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (364 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (366 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (418 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (420 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (422 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (423 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (425 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (426 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (428 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (430 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (436 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (437 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (439 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (441 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (442 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (443 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (447 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (480 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (481 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (486 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (487 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (488 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (489 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (493 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (498 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (499 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (502 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (506 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (508 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (510 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (7 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (104 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (124 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (166 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (364 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (366 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (437 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (480 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (1 ≤ count213 (baseVal q)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (1 ≤ count215 (baseVal q)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (1 ≤ count217 (baseVal q)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (2 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (2 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (2 ≤ count235 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value262 (q : Snake 81) : valuation q 262 = decide (2 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value286 (q : Snake 81) : valuation q 286 = decide (2 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value310 (q : Snake 81) : valuation q 310 = decide (2 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value336 (q : Snake 81) : valuation q 336 = decide (2 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value364 (q : Snake 81) : valuation q 364 = decide (2 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value414 (q : Snake 81) : valuation q 414 = decide (2 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value420 (q : Snake 81) : valuation q 420 = decide (2 ≤ count419 (baseVal q)) := rfl
theorem value1285 (q : Snake 81) : valuation q 1285 = decide (1 ≤ count1285 (baseVal q)) := rfl
theorem value1287 (q : Snake 81) : valuation q 1287 = decide (1 ≤ count1287 (baseVal q)) := rfl
theorem value1290 (q : Snake 81) : valuation q 1290 = decide (1 ≤ count1290 (baseVal q)) := rfl
theorem value1292 (q : Snake 81) : valuation q 1292 = decide (1 ≤ count1292 (baseVal q)) := rfl
theorem value1295 (q : Snake 81) : valuation q 1295 = decide (1 ≤ count1295 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (2 ≤ count1295 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (1 ≤ count1301 (baseVal q)) := rfl
theorem value1303 (q : Snake 81) : valuation q 1303 = decide (1 ≤ count1303 (baseVal q)) := rfl
theorem value1306 (q : Snake 81) : valuation q 1306 = decide (1 ≤ count1306 (baseVal q)) := rfl
theorem value1308 (q : Snake 81) : valuation q 1308 = decide (1 ≤ count1308 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (1 ≤ count1311 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (1 ≤ count1317 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (2 ≤ count1317 (baseVal q)) := rfl
theorem value1319 (q : Snake 81) : valuation q 1319 = decide (3 ≤ count1317 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (1 ≤ count1326 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (1 ≤ count1328 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (1 ≤ count1331 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (2 ≤ count1331 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (1 ≤ count1333 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (2 ≤ count1333 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (1 ≤ count1336 (baseVal q)) := rfl
theorem value1337 (q : Snake 81) : valuation q 1337 = decide (2 ≤ count1336 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (3 ≤ count1336 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (1 ≤ count1342 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (2 ≤ count1342 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (1 ≤ count1344 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (2 ≤ count1344 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (3 ≤ count1344 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (1 ≤ count1347 (baseVal q)) := rfl
theorem value1348 (q : Snake 81) : valuation q 1348 = decide (2 ≤ count1347 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (2 ≤ count1349 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (1 ≤ count1352 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (2 ≤ count1352 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (3 ≤ count1352 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (2 ≤ count1358 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (3 ≤ count1358 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (4 ≤ count1358 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (5 ≤ count1358 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (3 ≤ count1367 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (4 ≤ count1367 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (5 ≤ count1367 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (6 ≤ count1367 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (1 ≤ count1376 (baseVal q)) := rfl
theorem value1378 (q : Snake 81) : valuation q 1378 = decide (1 ≤ count1378 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (2 ≤ count1378 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (1 ≤ count1381 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (2 ≤ count1381 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (1 ≤ count1383 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (2 ≤ count1383 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (1 ≤ count1386 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (2 ≤ count1386 (baseVal q)) := rfl
theorem value1388 (q : Snake 81) : valuation q 1388 = decide (3 ≤ count1386 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (4 ≤ count1386 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (1 ≤ count1392 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (1 ≤ count1394 (baseVal q)) := rfl
theorem value1397 (q : Snake 81) : valuation q 1397 = decide (1 ≤ count1397 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (2 ≤ count1397 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (1 ≤ count1399 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (2 ≤ count1399 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (1 ≤ count1402 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (2 ≤ count1402 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (3 ≤ count1402 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (1 ≤ count1408 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (2 ≤ count1408 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (3 ≤ count1408 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (4 ≤ count1408 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (1 ≤ count1417 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (1 ≤ count1419 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (1 ≤ count1422 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (1 ≤ count1424 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (1 ≤ count1427 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (2 ≤ count1427 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (1 ≤ count1433 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (2 ≤ count1433 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (1 ≤ count1435 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (2 ≤ count1435 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (1 ≤ count1438 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (1 ≤ count1440 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (1 ≤ count1442 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (1 ≤ count1446 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (2 ≤ count1446 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (3 ≤ count1446 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (1 ≤ count1453 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (2 ≤ count1453 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (3 ≤ count1453 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (4 ≤ count1453 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (3 ≤ count1462 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (4 ≤ count1462 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (5 ≤ count1462 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (6 ≤ count1462 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (9 ≤ count1471 (baseVal q)) := rfl
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
theorem meaningNeg97 (b : Nat → Bool) : literal (valuationOf b) (-97) = decide (1 ≤ countLit b [-97]) := by
  change literal b (-97) = decide (1 ≤ countLit b [-97])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-97) <;> decide
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
theorem meaningNeg89 (b : Nat → Bool) : literal (valuationOf b) (-89) = decide (1 ≤ countLit b [-89]) := by
  change literal b (-89) = decide (1 ≤ countLit b [-89])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-89) <;> decide
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
theorem meaningNeg23 (b : Nat → Bool) : literal (valuationOf b) (-23) = decide (1 ≤ countLit b [-23]) := by
  change literal b (-23) = decide (1 ≤ countLit b [-23])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-23) <;> decide
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
theorem meaningNeg7 (b : Nat → Bool) : literal (valuationOf b) (-7) = decide (1 ≤ countLit b [-7]) := by
  change literal b (-7) = decide (1 ≤ countLit b [-7])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-7) <;> decide
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
theorem meaning108 (b : Nat → Bool) : literal (valuationOf b) (108) = decide (1 ≤ countLit b [108]) := by
  change literal b (108) = decide (1 ≤ countLit b [108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (108) <;> decide
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
theorem meaning127 (b : Nat → Bool) : literal (valuationOf b) (127) = decide (1 ≤ countLit b [127]) := by
  change literal b (127) = decide (1 ≤ countLit b [127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (127) <;> decide
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
theorem meaning140 (b : Nat → Bool) : literal (valuationOf b) (140) = decide (1 ≤ countLit b [140]) := by
  change literal b (140) = decide (1 ≤ countLit b [140])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (140) <;> decide
theorem meaning144 (b : Nat → Bool) : literal (valuationOf b) (144) = decide (1 ≤ countLit b [144]) := by
  change literal b (144) = decide (1 ≤ countLit b [144])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (144) <;> decide
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
theorem meaning162 (b : Nat → Bool) : literal (valuationOf b) (162) = decide (1 ≤ countLit b [162]) := by
  change literal b (162) = decide (1 ≤ countLit b [162])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (162) <;> decide
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
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
theorem meaning187 (b : Nat → Bool) : literal (valuationOf b) (187) = decide (1 ≤ countLit b [187]) := by
  change literal b (187) = decide (1 ≤ countLit b [187])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (187) <;> decide
theorem meaning190 (b : Nat → Bool) : literal (valuationOf b) (190) = decide (1 ≤ countLit b [190]) := by
  change literal b (190) = decide (1 ≤ countLit b [190])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (190) <;> decide
theorem meaning192 (b : Nat → Bool) : literal (valuationOf b) (192) = decide (1 ≤ countLit b [192]) := by
  change literal b (192) = decide (1 ≤ countLit b [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (192) <;> decide
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
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) (201) = decide (1 ≤ countLit b [201]) := by
  change literal b (201) = decide (1 ≤ countLit b [201])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (201) <;> decide
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) 213 = decide (1 ≤ count213 b) := rfl
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) 215 = decide (1 ≤ count215 b) := rfl
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) 217 = decide (1 ≤ count217 b) := rfl
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) 232 = decide (2 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning234 (b : Nat → Bool) : literal (valuationOf b) 234 = decide (2 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning236 (b : Nat → Bool) : literal (valuationOf b) 236 = decide (2 ≤ count235 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning262 (b : Nat → Bool) : literal (valuationOf b) 262 = decide (2 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning286 (b : Nat → Bool) : literal (valuationOf b) 286 = decide (2 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning310 (b : Nat → Bool) : literal (valuationOf b) 310 = decide (2 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning336 (b : Nat → Bool) : literal (valuationOf b) 336 = decide (2 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning338 (b : Nat → Bool) : literal (valuationOf b) 338 = decide (2 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning364 (b : Nat → Bool) : literal (valuationOf b) 364 = decide (2 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning414 (b : Nat → Bool) : literal (valuationOf b) 414 = decide (2 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning420 (b : Nat → Bool) : literal (valuationOf b) 420 = decide (2 ≤ count419 b) := rfl
theorem meaning1285 (b : Nat → Bool) : literal (valuationOf b) 1285 = decide (1 ≤ count1285 b) := rfl
theorem meaning1287 (b : Nat → Bool) : literal (valuationOf b) 1287 = decide (1 ≤ count1287 b) := rfl
theorem meaning1290 (b : Nat → Bool) : literal (valuationOf b) 1290 = decide (1 ≤ count1290 b) := rfl
theorem meaning1292 (b : Nat → Bool) : literal (valuationOf b) 1292 = decide (1 ≤ count1292 b) := rfl
theorem meaning1295 (b : Nat → Bool) : literal (valuationOf b) 1295 = decide (1 ≤ count1295 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (2 ≤ count1295 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (1 ≤ count1301 b) := rfl
theorem meaning1303 (b : Nat → Bool) : literal (valuationOf b) 1303 = decide (1 ≤ count1303 b) := rfl
theorem meaning1306 (b : Nat → Bool) : literal (valuationOf b) 1306 = decide (1 ≤ count1306 b) := rfl
theorem meaning1308 (b : Nat → Bool) : literal (valuationOf b) 1308 = decide (1 ≤ count1308 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (1 ≤ count1311 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (1 ≤ count1317 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (2 ≤ count1317 b) := rfl
theorem meaning1319 (b : Nat → Bool) : literal (valuationOf b) 1319 = decide (3 ≤ count1317 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (1 ≤ count1326 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (1 ≤ count1328 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (1 ≤ count1331 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (2 ≤ count1331 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (1 ≤ count1333 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (2 ≤ count1333 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (1 ≤ count1336 b) := rfl
theorem meaning1337 (b : Nat → Bool) : literal (valuationOf b) 1337 = decide (2 ≤ count1336 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (3 ≤ count1336 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (1 ≤ count1342 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (2 ≤ count1342 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (1 ≤ count1344 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (2 ≤ count1344 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (3 ≤ count1344 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (1 ≤ count1347 b) := rfl
theorem meaning1348 (b : Nat → Bool) : literal (valuationOf b) 1348 = decide (2 ≤ count1347 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (2 ≤ count1349 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (1 ≤ count1352 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (2 ≤ count1352 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (3 ≤ count1352 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (2 ≤ count1358 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (3 ≤ count1358 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (4 ≤ count1358 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (5 ≤ count1358 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (3 ≤ count1367 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (4 ≤ count1367 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (5 ≤ count1367 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (6 ≤ count1367 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (1 ≤ count1376 b) := rfl
theorem meaning1378 (b : Nat → Bool) : literal (valuationOf b) 1378 = decide (1 ≤ count1378 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (2 ≤ count1378 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (1 ≤ count1381 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (2 ≤ count1381 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (1 ≤ count1383 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (2 ≤ count1383 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (1 ≤ count1386 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (2 ≤ count1386 b) := rfl
theorem meaning1388 (b : Nat → Bool) : literal (valuationOf b) 1388 = decide (3 ≤ count1386 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (4 ≤ count1386 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (1 ≤ count1392 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (1 ≤ count1394 b) := rfl
theorem meaning1397 (b : Nat → Bool) : literal (valuationOf b) 1397 = decide (1 ≤ count1397 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (2 ≤ count1397 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (1 ≤ count1399 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (2 ≤ count1399 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (1 ≤ count1402 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (2 ≤ count1402 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (3 ≤ count1402 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (1 ≤ count1408 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (2 ≤ count1408 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (3 ≤ count1408 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (4 ≤ count1408 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (1 ≤ count1417 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (1 ≤ count1419 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (1 ≤ count1422 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (1 ≤ count1424 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (1 ≤ count1427 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (2 ≤ count1427 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (1 ≤ count1433 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (2 ≤ count1433 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (1 ≤ count1435 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (2 ≤ count1435 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (1 ≤ count1438 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (1 ≤ count1440 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (1 ≤ count1442 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (1 ≤ count1446 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (2 ≤ count1446 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (3 ≤ count1446 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (1 ≤ count1453 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (2 ≤ count1453 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (3 ≤ count1453 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (4 ≤ count1453 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (3 ≤ count1462 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (4 ≤ count1462 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (5 ≤ count1462 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (6 ≤ count1462 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (9 ≤ count1471 b) := rfl
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
end Snake9.Regrowth.E112249
