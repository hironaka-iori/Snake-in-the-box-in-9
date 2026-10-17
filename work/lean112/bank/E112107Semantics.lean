import E112107Data
namespace Snake9.Regrowth.E112107
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 110 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (5 : Vertex)))) else (if i < 4 then decide (InPath q (9 : Vertex)) else (if i < 5 then decide (InPath q (13 : Vertex)) else decide (InPath q (15 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (16 : Vertex)) else (if i < 8 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (22 : Vertex)) else decide (InPath q (26 : Vertex))) else (if i < 12 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (30 : Vertex)) else (if i < 15 then decide (InPath q (160 : Vertex)) else decide (InPath q (161 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (167 : Vertex)) else decide (InPath q (173 : Vertex))) else (if i < 19 then decide (InPath q (175 : Vertex)) else decide (InPath q (177 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (178 : Vertex)) else (if i < 22 then decide (InPath q (179 : Vertex)) else decide (InPath q (182 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (186 : Vertex)) else decide (InPath q (188 : Vertex))) else (if i < 26 then decide (InPath q (189 : Vertex)) else decide (InPath q (190 : Vertex))))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then decide (InPath q (192 : Vertex)) else (if i < 29 then decide (InPath q (193 : Vertex)) else decide (InPath q (198 : Vertex)))) else (if i < 32 then (if i < 31 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex))) else (if i < 33 then decide (InPath q (201 : Vertex)) else decide (InPath q (205 : Vertex))))) else (if i < 37 then (if i < 35 then decide (InPath q (207 : Vertex)) else (if i < 36 then decide (InPath q (209 : Vertex)) else decide (InPath q (210 : Vertex)))) else (if i < 39 then (if i < 38 then decide (InPath q (211 : Vertex)) else decide (InPath q (214 : Vertex))) else (if i < 40 then decide (InPath q (218 : Vertex)) else decide (InPath q (220 : Vertex)))))) else (if i < 48 then (if i < 44 then (if i < 42 then decide (InPath q (221 : Vertex)) else (if i < 43 then decide (InPath q (222 : Vertex)) else decide (InPath q (256 : Vertex)))) else (if i < 46 then (if i < 45 then decide (InPath q (258 : Vertex)) else decide (InPath q (260 : Vertex))) else (if i < 47 then decide (InPath q (262 : Vertex)) else decide (InPath q (263 : Vertex))))) else (if i < 51 then (if i < 49 then decide (InPath q (264 : Vertex)) else (if i < 50 then decide (InPath q (265 : Vertex)) else decide (InPath q (266 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (268 : Vertex)) else decide (InPath q (270 : Vertex))) else (if i < 54 then decide (InPath q (272 : Vertex)) else decide (InPath q (276 : Vertex)))))))) else (if i < 82 then (if i < 68 then (if i < 61 then (if i < 58 then (if i < 56 then decide (InPath q (277 : Vertex)) else (if i < 57 then decide (InPath q (279 : Vertex)) else decide (InPath q (281 : Vertex)))) else (if i < 59 then decide (InPath q (282 : Vertex)) else (if i < 60 then decide (InPath q (283 : Vertex)) else decide (InPath q (285 : Vertex))))) else (if i < 64 then (if i < 62 then decide (InPath q (287 : Vertex)) else (if i < 63 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex)))) else (if i < 66 then (if i < 65 then decide (InPath q (325 : Vertex)) else decide (InPath q (326 : Vertex))) else (if i < 67 then decide (InPath q (327 : Vertex)) else decide (InPath q (328 : Vertex)))))) else (if i < 75 then (if i < 71 then (if i < 69 then decide (InPath q (329 : Vertex)) else (if i < 70 then decide (InPath q (333 : Vertex)) else decide (InPath q (335 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex))) else (if i < 74 then decide (InPath q (339 : Vertex)) else decide (InPath q (342 : Vertex))))) else (if i < 78 then (if i < 76 then decide (InPath q (346 : Vertex)) else (if i < 77 then decide (InPath q (348 : Vertex)) else decide (InPath q (349 : Vertex)))) else (if i < 80 then (if i < 79 then decide (InPath q (350 : Vertex)) else decide (InPath q (416 : Vertex))) else (if i < 81 then decide (InPath q (418 : Vertex)) else decide (InPath q (420 : Vertex))))))) else (if i < 96 then (if i < 89 then (if i < 85 then (if i < 83 then decide (InPath q (422 : Vertex)) else (if i < 84 then decide (InPath q (423 : Vertex)) else decide (InPath q (425 : Vertex)))) else (if i < 87 then (if i < 86 then decide (InPath q (426 : Vertex)) else decide (InPath q (428 : Vertex))) else (if i < 88 then decide (InPath q (430 : Vertex)) else decide (InPath q (436 : Vertex))))) else (if i < 92 then (if i < 90 then decide (InPath q (437 : Vertex)) else (if i < 91 then decide (InPath q (439 : Vertex)) else decide (InPath q (441 : Vertex)))) else (if i < 94 then (if i < 93 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex))) else (if i < 95 then decide (InPath q (445 : Vertex)) else decide (InPath q (447 : Vertex)))))) else (if i < 103 then (if i < 99 then (if i < 97 then decide (InPath q (450 : Vertex)) else (if i < 98 then decide (InPath q (454 : Vertex)) else decide (InPath q (456 : Vertex)))) else (if i < 101 then (if i < 100 then decide (InPath q (460 : Vertex)) else decide (InPath q (462 : Vertex))) else (if i < 102 then decide (InPath q (486 : Vertex)) else decide (InPath q (488 : Vertex))))) else (if i < 106 then (if i < 104 then decide (InPath q (489 : Vertex)) else (if i < 105 then decide (InPath q (493 : Vertex)) else decide (InPath q (495 : Vertex)))) else (if i < 108 then (if i < 107 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 109 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 165 then (if i < 137 then (if i < 123 then (if i < 116 then (if i < 113 then (if i < 111 then decide (InPath q (510 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (5 : Vertex)))) else (if i < 114 then decide (BallClauseLogic.Endpoint q (9 : Vertex)) else (if i < 115 then decide (BallClauseLogic.Endpoint q (13 : Vertex)) else decide (BallClauseLogic.Endpoint q (15 : Vertex))))) else (if i < 119 then (if i < 117 then decide (BallClauseLogic.Endpoint q (16 : Vertex)) else (if i < 118 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex)))) else (if i < 121 then (if i < 120 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (26 : Vertex))) else (if i < 122 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex)))))) else (if i < 130 then (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (167 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else decide (BallClauseLogic.Endpoint q (177 : Vertex))))) else (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (178 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex)))) else (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (188 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (189 : Vertex)) else decide (BallClauseLogic.Endpoint q (190 : Vertex))))))) else (if i < 151 then (if i < 144 then (if i < 140 then (if i < 138 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else decide (BallClauseLogic.Endpoint q (198 : Vertex)))) else (if i < 142 then (if i < 141 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (200 : Vertex))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex))))) else (if i < 147 then (if i < 145 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else (if i < 146 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else decide (BallClauseLogic.Endpoint q (210 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (220 : Vertex)))))) else (if i < 158 then (if i < 154 then (if i < 152 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else (if i < 153 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else decide (BallClauseLogic.Endpoint q (256 : Vertex)))) else (if i < 156 then (if i < 155 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (262 : Vertex)) else decide (BallClauseLogic.Endpoint q (263 : Vertex))))) else (if i < 161 then (if i < 159 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else (if i < 160 then decide (BallClauseLogic.Endpoint q (265 : Vertex)) else decide (BallClauseLogic.Endpoint q (266 : Vertex)))) else (if i < 163 then (if i < 162 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (270 : Vertex))) else (if i < 164 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex)))))))) else (if i < 193 then (if i < 179 then (if i < 172 then (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (281 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (282 : Vertex)) else decide (BallClauseLogic.Endpoint q (283 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (285 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex))))) else (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (325 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (326 : Vertex)) else decide (BallClauseLogic.Endpoint q (327 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (328 : Vertex)) else decide (BallClauseLogic.Endpoint q (329 : Vertex)))))) else (if i < 186 then (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (335 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (338 : Vertex)) else decide (BallClauseLogic.Endpoint q (339 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (346 : Vertex))))) else (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex)))) else (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (418 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (420 : Vertex)) else decide (BallClauseLogic.Endpoint q (422 : Vertex))))))) else (if i < 207 then (if i < 200 then (if i < 196 then (if i < 194 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else (if i < 195 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (426 : Vertex)))) else (if i < 198 then (if i < 197 then decide (BallClauseLogic.Endpoint q (428 : Vertex)) else decide (BallClauseLogic.Endpoint q (430 : Vertex))) else (if i < 199 then decide (BallClauseLogic.Endpoint q (436 : Vertex)) else decide (BallClauseLogic.Endpoint q (437 : Vertex))))) else (if i < 203 then (if i < 201 then decide (BallClauseLogic.Endpoint q (439 : Vertex)) else (if i < 202 then decide (BallClauseLogic.Endpoint q (441 : Vertex)) else decide (BallClauseLogic.Endpoint q (442 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (445 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else decide (BallClauseLogic.Endpoint q (450 : Vertex)))))) else (if i < 214 then (if i < 210 then (if i < 208 then decide (BallClauseLogic.Endpoint q (454 : Vertex)) else (if i < 209 then decide (BallClauseLogic.Endpoint q (456 : Vertex)) else decide (BallClauseLogic.Endpoint q (460 : Vertex)))) else (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (488 : Vertex)) else decide (BallClauseLogic.Endpoint q (489 : Vertex))))) else (if i < 217 then (if i < 215 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else (if i < 216 then decide (BallClauseLogic.Endpoint q (495 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count221 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count223 (b : Nat → Bool) : Nat := countLit b [111, 112, 113]
def count225 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count227 (b : Nat → Bool) : Nat := countLit b [114, 115, 116]
def count229 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116]
def count231 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [117, 118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count237 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count239 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123]
def count241 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123]
def count245 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count247 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count251 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131]
def count255 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count259 (b : Nat → Bool) : Nat := countLit b [132, 133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count263 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count265 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138]
def count267 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count275 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count289 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count291 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count303 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count305 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count313 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count315 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165]
def count319 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165]
def count327 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count329 (b : Nat → Bool) : Nat := countLit b [166, 167, 168]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175, 176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [179, 180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count371 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192]
def count373 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192]
def count375 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192]
def count379 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [193, 194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count387 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199]
def count391 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count393 (b : Nat → Bool) : Nat := countLit b [200, 201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count399 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206]
def count401 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203, 204, 205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [207, 208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count411 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count413 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count419 (b : Nat → Bool) : Nat := countLit b [214, 215, 216]
def count421 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count423 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count425 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220]
def count427 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]
def count433 (b : Nat → Bool) : Nat := countLit b [166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]
def count435 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]
def count437 (b : Nat → Bool) : Nat := countLit b [2, 3]
def count439 (b : Nat → Bool) : Nat := countLit b [1, 2, 3]
def count442 (b : Nat → Bool) : Nat := countLit b [5, 7]
def count444 (b : Nat → Bool) : Nat := countLit b [8, 12]
def count446 (b : Nat → Bool) : Nat := countLit b [5, 7, 8, 12]
def count450 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 5, 7, 8, 12]
def count457 (b : Nat → Bool) : Nat := countLit b [14, 18]
def count459 (b : Nat → Bool) : Nat := countLit b [13, 14, 18]
def count462 (b : Nat → Bool) : Nat := countLit b [19, 20]
def count464 (b : Nat → Bool) : Nat := countLit b [25, 26]
def count466 (b : Nat → Bool) : Nat := countLit b [19, 20, 25, 26]
def count470 (b : Nat → Bool) : Nat := countLit b [13, 14, 18, 19, 20, 25, 26]
def count477 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 5, 7, 8, 12, 13, 14, 18, 19, 20, 25, 26]
def count491 (b : Nat → Bool) : Nat := countLit b [29, 32]
def count493 (b : Nat → Bool) : Nat := countLit b [27, 29, 32]
def count496 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count498 (b : Nat → Bool) : Nat := countLit b [36, 41]
def count500 (b : Nat → Bool) : Nat := countLit b [34, 35, 36, 41]
def count504 (b : Nat → Bool) : Nat := countLit b [27, 29, 32, 34, 35, 36, 41]
def count511 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count513 (b : Nat → Bool) : Nat := countLit b [42, 44, 45]
def count516 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count518 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count520 (b : Nat → Bool) : Nat := countLit b [47, 48, 52, 53]
def count524 (b : Nat → Bool) : Nat := countLit b [42, 44, 45, 47, 48, 52, 53]
def count531 (b : Nat → Bool) : Nat := countLit b [27, 29, 32, 34, 35, 36, 41, 42, 44, 45, 47, 48, 52, 53]
def count545 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 5, 7, 8, 12, 13, 14, 18, 19, 20, 25, 26, 27, 29, 32, 34, 35, 36, 41, 42, 44, 45, 47, 48, 52, 53]
def count573 (b : Nat → Bool) : Nat := countLit b [57, 58]
def count575 (b : Nat → Bool) : Nat := countLit b [55, 57, 58]
def count578 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count580 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count582 (b : Nat → Bool) : Nat := countLit b [61, 62, 64, 65]
def count586 (b : Nat → Bool) : Nat := countLit b [55, 57, 58, 61, 62, 64, 65]
def count593 (b : Nat → Bool) : Nat := countLit b [70, 71]
def count595 (b : Nat → Bool) : Nat := countLit b [68, 70, 71]
def count598 (b : Nat → Bool) : Nat := countLit b [72, 77]
def count600 (b : Nat → Bool) : Nat := countLit b [78, 80]
def count602 (b : Nat → Bool) : Nat := countLit b [72, 77, 78, 80]
def count606 (b : Nat → Bool) : Nat := countLit b [68, 70, 71, 72, 77, 78, 80]
def count613 (b : Nat → Bool) : Nat := countLit b [55, 57, 58, 61, 62, 64, 65, 68, 70, 71, 72, 77, 78, 80]
def count627 (b : Nat → Bool) : Nat := countLit b [83, 87]
def count629 (b : Nat → Bool) : Nat := countLit b [81, 83, 87]
def count632 (b : Nat → Bool) : Nat := countLit b [89, 91]
def count634 (b : Nat → Bool) : Nat := countLit b [92, 95]
def count636 (b : Nat → Bool) : Nat := countLit b [89, 91, 92, 95]
def count640 (b : Nat → Bool) : Nat := countLit b [81, 83, 87, 89, 91, 92, 95]
def count647 (b : Nat → Bool) : Nat := countLit b [96, 98]
def count649 (b : Nat → Bool) : Nat := countLit b [100, 101]
def count651 (b : Nat → Bool) : Nat := countLit b [96, 98, 100, 101]
def count655 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count657 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count659 (b : Nat → Bool) : Nat := countLit b [103, 105, 109, 110]
def count663 (b : Nat → Bool) : Nat := countLit b [96, 98, 100, 101, 103, 105, 109, 110]
def count671 (b : Nat → Bool) : Nat := countLit b [81, 83, 87, 89, 91, 92, 95, 96, 98, 100, 101, 103, 105, 109, 110]
def count686 (b : Nat → Bool) : Nat := countLit b [55, 57, 58, 61, 62, 64, 65, 68, 70, 71, 72, 77, 78, 80, 81, 83, 87, 89, 91, 92, 95, 96, 98, 100, 101, 103, 105, 109, 110]
def count715 (b : Nat → Bool) : Nat := countLit b [1, 2, 3, 5, 7, 8, 12, 13, 14, 18, 19, 20, 25, 26, 27, 29, 32, 34, 35, 36, 41, 42, 44, 45, 47, 48, 52, 53, 55, 57, 58, 61, 62, 64, 65, 68, 70, 71, 72, 77, 78, 80, 81, 83, 87, 89, 91, 92, 95, 96, 98, 100, 101, 103, 105, 109, 110]
def count757 (b : Nat → Bool) : Nat := countLit b [-2, -3]
def count759 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3]
def count762 (b : Nat → Bool) : Nat := countLit b [-5, -7]
def count764 (b : Nat → Bool) : Nat := countLit b [-8, -12]
def count766 (b : Nat → Bool) : Nat := countLit b [-5, -7, -8, -12]
def count770 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -5, -7, -8, -12]
def count777 (b : Nat → Bool) : Nat := countLit b [-14, -18]
def count779 (b : Nat → Bool) : Nat := countLit b [-13, -14, -18]
def count782 (b : Nat → Bool) : Nat := countLit b [-19, -20]
def count784 (b : Nat → Bool) : Nat := countLit b [-25, -26]
def count786 (b : Nat → Bool) : Nat := countLit b [-19, -20, -25, -26]
def count790 (b : Nat → Bool) : Nat := countLit b [-13, -14, -18, -19, -20, -25, -26]
def count797 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -5, -7, -8, -12, -13, -14, -18, -19, -20, -25, -26]
def count811 (b : Nat → Bool) : Nat := countLit b [-29, -32]
def count813 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32]
def count816 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count818 (b : Nat → Bool) : Nat := countLit b [-36, -41]
def count820 (b : Nat → Bool) : Nat := countLit b [-34, -35, -36, -41]
def count824 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32, -34, -35, -36, -41]
def count831 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count833 (b : Nat → Bool) : Nat := countLit b [-42, -44, -45]
def count836 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count838 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count840 (b : Nat → Bool) : Nat := countLit b [-47, -48, -52, -53]
def count844 (b : Nat → Bool) : Nat := countLit b [-42, -44, -45, -47, -48, -52, -53]
def count851 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32, -34, -35, -36, -41, -42, -44, -45, -47, -48, -52, -53]
def count865 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -5, -7, -8, -12, -13, -14, -18, -19, -20, -25, -26, -27, -29, -32, -34, -35, -36, -41, -42, -44, -45, -47, -48, -52, -53]
def count882 (b : Nat → Bool) : Nat := countLit b [-57, -58]
def count884 (b : Nat → Bool) : Nat := countLit b [-55, -57, -58]
def count887 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count889 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count891 (b : Nat → Bool) : Nat := countLit b [-61, -62, -64, -65]
def count895 (b : Nat → Bool) : Nat := countLit b [-55, -57, -58, -61, -62, -64, -65]
def count902 (b : Nat → Bool) : Nat := countLit b [-70, -71]
def count904 (b : Nat → Bool) : Nat := countLit b [-68, -70, -71]
def count907 (b : Nat → Bool) : Nat := countLit b [-72, -77]
def count909 (b : Nat → Bool) : Nat := countLit b [-78, -80]
def count911 (b : Nat → Bool) : Nat := countLit b [-72, -77, -78, -80]
def count915 (b : Nat → Bool) : Nat := countLit b [-68, -70, -71, -72, -77, -78, -80]
def count922 (b : Nat → Bool) : Nat := countLit b [-55, -57, -58, -61, -62, -64, -65, -68, -70, -71, -72, -77, -78, -80]
def count936 (b : Nat → Bool) : Nat := countLit b [-83, -87]
def count938 (b : Nat → Bool) : Nat := countLit b [-81, -83, -87]
def count941 (b : Nat → Bool) : Nat := countLit b [-89, -91]
def count943 (b : Nat → Bool) : Nat := countLit b [-92, -95]
def count945 (b : Nat → Bool) : Nat := countLit b [-89, -91, -92, -95]
def count949 (b : Nat → Bool) : Nat := countLit b [-81, -83, -87, -89, -91, -92, -95]
def count956 (b : Nat → Bool) : Nat := countLit b [-96, -98]
def count958 (b : Nat → Bool) : Nat := countLit b [-100, -101]
def count960 (b : Nat → Bool) : Nat := countLit b [-96, -98, -100, -101]
def count964 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count966 (b : Nat → Bool) : Nat := countLit b [-109, -110]
def count968 (b : Nat → Bool) : Nat := countLit b [-103, -105, -109, -110]
def count972 (b : Nat → Bool) : Nat := countLit b [-96, -98, -100, -101, -103, -105, -109, -110]
def count980 (b : Nat → Bool) : Nat := countLit b [-81, -83, -87, -89, -91, -92, -95, -96, -98, -100, -101, -103, -105, -109, -110]
def count995 (b : Nat → Bool) : Nat := countLit b [-55, -57, -58, -61, -62, -64, -65, -68, -70, -71, -72, -77, -78, -80, -81, -83, -87, -89, -91, -92, -95, -96, -98, -100, -101, -103, -105, -109, -110]
def count1012 (b : Nat → Bool) : Nat := countLit b [-1, -2, -3, -5, -7, -8, -12, -13, -14, -18, -19, -20, -25, -26, -27, -29, -32, -34, -35, -36, -41, -42, -44, -45, -47, -48, -52, -53, -55, -57, -58, -61, -62, -64, -65, -68, -70, -71, -72, -77, -78, -80, -81, -83, -87, -89, -91, -92, -95, -96, -98, -100, -101, -103, -105, -109, -110]
def count1029 (b : Nat → Bool) : Nat := countLit b [6, 9]
def count1031 (b : Nat → Bool) : Nat := countLit b [4, 6, 9]
def count1034 (b : Nat → Bool) : Nat := countLit b [11, 15]
def count1036 (b : Nat → Bool) : Nat := countLit b [10, 11, 15]
def count1039 (b : Nat → Bool) : Nat := countLit b [4, 6, 9, 10, 11, 15]
def count1045 (b : Nat → Bool) : Nat := countLit b [17, 21]
def count1047 (b : Nat → Bool) : Nat := countLit b [16, 17, 21]
def count1050 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count1052 (b : Nat → Bool) : Nat := countLit b [24, 28]
def count1054 (b : Nat → Bool) : Nat := countLit b [22, 23, 24, 28]
def count1058 (b : Nat → Bool) : Nat := countLit b [16, 17, 21, 22, 23, 24, 28]
def count1065 (b : Nat → Bool) : Nat := countLit b [4, 6, 9, 10, 11, 15, 16, 17, 21, 22, 23, 24, 28]
def count1078 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count1080 (b : Nat → Bool) : Nat := countLit b [30, 31, 33]
def count1083 (b : Nat → Bool) : Nat := countLit b [38, 39]
def count1085 (b : Nat → Bool) : Nat := countLit b [37, 38, 39]
def count1088 (b : Nat → Bool) : Nat := countLit b [30, 31, 33, 37, 38, 39]
def count1094 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count1096 (b : Nat → Bool) : Nat := countLit b [40, 43, 46]
def count1099 (b : Nat → Bool) : Nat := countLit b [49, 50]
def count1101 (b : Nat → Bool) : Nat := countLit b [51, 54]
def count1103 (b : Nat → Bool) : Nat := countLit b [49, 50, 51, 54]
def count1107 (b : Nat → Bool) : Nat := countLit b [40, 43, 46, 49, 50, 51, 54]
def count1114 (b : Nat → Bool) : Nat := countLit b [30, 31, 33, 37, 38, 39, 40, 43, 46, 49, 50, 51, 54]
def count1127 (b : Nat → Bool) : Nat := countLit b [4, 6, 9, 10, 11, 15, 16, 17, 21, 22, 23, 24, 28, 30, 31, 33, 37, 38, 39, 40, 43, 46, 49, 50, 51, 54]
def count1153 (b : Nat → Bool) : Nat := countLit b [59, 60]
def count1155 (b : Nat → Bool) : Nat := countLit b [56, 59, 60]
def count1158 (b : Nat → Bool) : Nat := countLit b [66, 67]
def count1160 (b : Nat → Bool) : Nat := countLit b [63, 66, 67]
def count1163 (b : Nat → Bool) : Nat := countLit b [56, 59, 60, 63, 66, 67]
def count1169 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count1171 (b : Nat → Bool) : Nat := countLit b [69, 73, 74]
def count1174 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count1176 (b : Nat → Bool) : Nat := countLit b [79, 82]
def count1178 (b : Nat → Bool) : Nat := countLit b [75, 76, 79, 82]
def count1182 (b : Nat → Bool) : Nat := countLit b [69, 73, 74, 75, 76, 79, 82]
def count1189 (b : Nat → Bool) : Nat := countLit b [56, 59, 60, 63, 66, 67, 69, 73, 74, 75, 76, 79, 82]
def count1202 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count1204 (b : Nat → Bool) : Nat := countLit b [84, 85, 86]
def count1207 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count1209 (b : Nat → Bool) : Nat := countLit b [93, 94]
def count1211 (b : Nat → Bool) : Nat := countLit b [88, 90, 93, 94]
def count1215 (b : Nat → Bool) : Nat := countLit b [84, 85, 86, 88, 90, 93, 94]
def count1222 (b : Nat → Bool) : Nat := countLit b [99, 102]
def count1224 (b : Nat → Bool) : Nat := countLit b [97, 99, 102]
def count1227 (b : Nat → Bool) : Nat := countLit b [104, 106]
def count1229 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count1231 (b : Nat → Bool) : Nat := countLit b [104, 106, 107, 108]
def count1235 (b : Nat → Bool) : Nat := countLit b [97, 99, 102, 104, 106, 107, 108]
def count1242 (b : Nat → Bool) : Nat := countLit b [84, 85, 86, 88, 90, 93, 94, 97, 99, 102, 104, 106, 107, 108]
def count1256 (b : Nat → Bool) : Nat := countLit b [56, 59, 60, 63, 66, 67, 69, 73, 74, 75, 76, 79, 82, 84, 85, 86, 88, 90, 93, 94, 97, 99, 102, 104, 106, 107, 108]
def count1283 (b : Nat → Bool) : Nat := countLit b [4, 6, 9, 10, 11, 15, 16, 17, 21, 22, 23, 24, 28, 30, 31, 33, 37, 38, 39, 40, 43, 46, 49, 50, 51, 54, 56, 59, 60, 63, 66, 67, 69, 73, 74, 75, 76, 79, 82, 84, 85, 86, 88, 90, 93, 94, 97, 99, 102, 104, 106, 107, 108]
def count1325 (b : Nat → Bool) : Nat := countLit b [-6, -9]
def count1327 (b : Nat → Bool) : Nat := countLit b [-4, -6, -9]
def count1330 (b : Nat → Bool) : Nat := countLit b [-11, -15]
def count1332 (b : Nat → Bool) : Nat := countLit b [-10, -11, -15]
def count1335 (b : Nat → Bool) : Nat := countLit b [-4, -6, -9, -10, -11, -15]
def count1341 (b : Nat → Bool) : Nat := countLit b [-17, -21]
def count1343 (b : Nat → Bool) : Nat := countLit b [-16, -17, -21]
def count1346 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count1348 (b : Nat → Bool) : Nat := countLit b [-24, -28]
def count1350 (b : Nat → Bool) : Nat := countLit b [-22, -23, -24, -28]
def count1354 (b : Nat → Bool) : Nat := countLit b [-16, -17, -21, -22, -23, -24, -28]
def count1361 (b : Nat → Bool) : Nat := countLit b [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28]
def count1374 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count1376 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33]
def count1379 (b : Nat → Bool) : Nat := countLit b [-38, -39]
def count1381 (b : Nat → Bool) : Nat := countLit b [-37, -38, -39]
def count1384 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33, -37, -38, -39]
def count1390 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count1392 (b : Nat → Bool) : Nat := countLit b [-40, -43, -46]
def count1395 (b : Nat → Bool) : Nat := countLit b [-49, -50]
def count1397 (b : Nat → Bool) : Nat := countLit b [-51, -54]
def count1399 (b : Nat → Bool) : Nat := countLit b [-49, -50, -51, -54]
def count1403 (b : Nat → Bool) : Nat := countLit b [-40, -43, -46, -49, -50, -51, -54]
def count1410 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]
def count1423 (b : Nat → Bool) : Nat := countLit b [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54]
def count1436 (b : Nat → Bool) : Nat := countLit b [-59, -60]
def count1438 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60]
def count1441 (b : Nat → Bool) : Nat := countLit b [-66, -67]
def count1443 (b : Nat → Bool) : Nat := countLit b [-63, -66, -67]
def count1446 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60, -63, -66, -67]
def count1452 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count1454 (b : Nat → Bool) : Nat := countLit b [-69, -73, -74]
def count1457 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count1459 (b : Nat → Bool) : Nat := countLit b [-79, -82]
def count1461 (b : Nat → Bool) : Nat := countLit b [-75, -76, -79, -82]
def count1465 (b : Nat → Bool) : Nat := countLit b [-69, -73, -74, -75, -76, -79, -82]
def count1472 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82]
def count1485 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count1487 (b : Nat → Bool) : Nat := countLit b [-84, -85, -86]
def count1490 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count1492 (b : Nat → Bool) : Nat := countLit b [-93, -94]
def count1494 (b : Nat → Bool) : Nat := countLit b [-88, -90, -93, -94]
def count1498 (b : Nat → Bool) : Nat := countLit b [-84, -85, -86, -88, -90, -93, -94]
def count1505 (b : Nat → Bool) : Nat := countLit b [-99, -102]
def count1507 (b : Nat → Bool) : Nat := countLit b [-97, -99, -102]
def count1510 (b : Nat → Bool) : Nat := countLit b [-104, -106]
def count1512 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1514 (b : Nat → Bool) : Nat := countLit b [-104, -106, -107, -108]
def count1518 (b : Nat → Bool) : Nat := countLit b [-97, -99, -102, -104, -106, -107, -108]
def count1525 (b : Nat → Bool) : Nat := countLit b [-84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]
def count1538 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]
def count1551 (b : Nat → Bool) : Nat := countLit b [-4, -6, -9, -10, -11, -15, -16, -17, -21, -22, -23, -24, -28, -30, -31, -33, -37, -38, -39, -40, -43, -46, -49, -50, -51, -54, -56, -59, -60, -63, -66, -67, -69, -73, -74, -75, -76, -79, -82, -84, -85, -86, -88, -90, -93, -94, -97, -99, -102, -104, -106, -107, -108]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 782 then (if i < 391 then (if i < 195 then (if i < 97 then (if i < 48 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 22 then b 21 else (if i < 23 then b 22 else b 23))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then b 24 else (if i < 26 then b 25 else b 26)) else (if i < 28 then b 27 else (if i < 29 then b 28 else b 29))) else (if i < 33 then (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)))) else (if i < 42 then (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41))) else (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)))))) else (if i < 72 then (if i < 60 then (if i < 54 then (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 52 then b 51 else (if i < 53 then b 52 else b 53))) else (if i < 57 then (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)) else (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)))) else (if i < 66 then (if i < 63 then (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)) else (if i < 64 then b 63 else (if i < 65 then b 64 else b 65))) else (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))))) else (if i < 84 then (if i < 78 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77))) else (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)))) else (if i < 90 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))) else (if i < 93 then (if i < 91 then b 90 else (if i < 92 then b 91 else b 92)) else (if i < 95 then (if i < 94 then b 93 else b 94) else (if i < 96 then b 95 else b 96))))))) else (if i < 146 then (if i < 121 then (if i < 109 then (if i < 103 then (if i < 100 then (if i < 98 then b 97 else (if i < 99 then b 98 else b 99)) else (if i < 101 then b 100 else (if i < 102 then b 101 else b 102))) else (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)))) else (if i < 115 then (if i < 112 then (if i < 110 then b 109 else (if i < 111 then b 110 else b 111)) else (if i < 113 then b 112 else (if i < 114 then b 113 else b 114))) else (if i < 118 then (if i < 116 then b 115 else (if i < 117 then b 116 else b 117)) else (if i < 119 then b 118 else (if i < 120 then b 119 else b 120))))) else (if i < 133 then (if i < 127 then (if i < 124 then (if i < 122 then b 121 else (if i < 123 then b 122 else b 123)) else (if i < 125 then b 124 else (if i < 126 then b 125 else b 126))) else (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)))) else (if i < 139 then (if i < 136 then (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)) else (if i < 137 then b 136 else (if i < 138 then b 137 else b 138))) else (if i < 142 then (if i < 140 then b 139 else (if i < 141 then b 140 else b 141)) else (if i < 144 then (if i < 143 then b 142 else b 143) else (if i < 145 then b 144 else b 145)))))) else (if i < 170 then (if i < 158 then (if i < 152 then (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 150 then b 149 else (if i < 151 then b 150 else b 151))) else (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 156 then b 155 else (if i < 157 then b 156 else b 157)))) else (if i < 164 then (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 162 then b 161 else (if i < 163 then b 162 else b 163))) else (if i < 167 then (if i < 165 then b 164 else (if i < 166 then b 165 else b 166)) else (if i < 168 then b 167 else (if i < 169 then b 168 else b 169))))) else (if i < 182 then (if i < 176 then (if i < 173 then (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)) else (if i < 174 then b 173 else (if i < 175 then b 174 else b 175))) else (if i < 179 then (if i < 177 then b 176 else (if i < 178 then b 177 else b 178)) else (if i < 180 then b 179 else (if i < 181 then b 180 else b 181)))) else (if i < 188 then (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187))) else (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else b 194)))))))) else (if i < 293 then (if i < 244 then (if i < 219 then (if i < 207 then (if i < 201 then (if i < 198 then (if i < 196 then b 195 else (if i < 197 then b 196 else b 197)) else (if i < 199 then b 198 else (if i < 200 then b 199 else b 200))) else (if i < 204 then (if i < 202 then b 201 else (if i < 203 then b 202 else b 203)) else (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)))) else (if i < 213 then (if i < 210 then (if i < 208 then b 207 else (if i < 209 then b 208 else b 209)) else (if i < 211 then b 210 else (if i < 212 then b 211 else b 212))) else (if i < 216 then (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)) else (if i < 217 then b 216 else (if i < 218 then b 217 else b 218))))) else (if i < 231 then (if i < 225 then (if i < 222 then (if i < 220 then b 219 else (if i < 221 then b 220 else decide (1 ≤ count221 b))) else (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b)))) else (if i < 228 then (if i < 226 then decide (1 ≤ count225 b) else (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b))) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b))))) else (if i < 237 then (if i < 234 then (if i < 232 then decide (1 ≤ count231 b) else (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b))) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b)))) else (if i < 240 then (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b))) else (if i < 242 then (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b)) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))))))) else (if i < 268 then (if i < 256 then (if i < 250 then (if i < 247 then (if i < 245 then decide (2 ≤ count243 b) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b))) else (if i < 248 then decide (1 ≤ count247 b) else (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b)))) else (if i < 253 then (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b))) else (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b))))) else (if i < 262 then (if i < 259 then (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))) else (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))) else (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)))))) else (if i < 280 then (if i < 274 then (if i < 271 then (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b))) else (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)))) else (if i < 277 then (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))) else (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))))) else (if i < 286 then (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)))) else (if i < 289 then (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))) else (if i < 291 then (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b)) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)))))))) else (if i < 342 then (if i < 317 then (if i < 305 then (if i < 299 then (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))) else (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))))) else (if i < 311 then (if i < 308 then (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))) else (if i < 309 then decide (2 ≤ count307 b) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)))) else (if i < 314 then (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b))) else (if i < 315 then decide (2 ≤ count313 b) else (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b)))))) else (if i < 329 then (if i < 323 then (if i < 320 then (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b))) else (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)))) else (if i < 326 then (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))) else (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))))) else (if i < 335 then (if i < 332 then (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))) else (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b)))) else (if i < 338 then (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b))) else (if i < 340 then (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b))))))) else (if i < 366 then (if i < 354 then (if i < 348 then (if i < 345 then (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b))) else (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)))) else (if i < 351 then (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b))) else (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))))) else (if i < 360 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b)))) else (if i < 363 then (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b))) else (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)))))) else (if i < 378 then (if i < 372 then (if i < 369 then (if i < 367 then decide (2 ≤ count365 b) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))) else (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b)))) else (if i < 375 then (if i < 373 then decide (2 ≤ count371 b) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b))) else (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))))) else (if i < 384 then (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 382 then decide (1 ≤ count381 b) else (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)))) else (if i < 387 then (if i < 385 then decide (2 ≤ count383 b) else (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b))) else (if i < 389 then (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))))))))) else (if i < 586 then (if i < 488 then (if i < 439 then (if i < 415 then (if i < 403 then (if i < 397 then (if i < 394 then (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 395 then decide (2 ≤ count393 b) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b)))) else (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 401 then decide (2 ≤ count399 b) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))))) else (if i < 409 then (if i < 406 then (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))) else (if i < 407 then decide (2 ≤ count405 b) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)))) else (if i < 412 then (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b))) else (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))))) else (if i < 427 then (if i < 421 then (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b)))) else (if i < 424 then (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))) else (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b))))) else (if i < 433 then (if i < 430 then (if i < 428 then decide (1 ≤ count427 b) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 431 then decide (2 ≤ count429 b) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)))) else (if i < 436 then (if i < 434 then decide (1 ≤ count433 b) else (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b))) else (if i < 437 then decide (2 ≤ count435 b) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b))))))) else (if i < 463 then (if i < 451 then (if i < 445 then (if i < 442 then (if i < 440 then decide (1 ≤ count439 b) else (if i < 441 then decide (2 ≤ count439 b) else decide (3 ≤ count439 b))) else (if i < 443 then decide (1 ≤ count442 b) else (if i < 444 then decide (2 ≤ count442 b) else decide (1 ≤ count444 b)))) else (if i < 448 then (if i < 446 then decide (2 ≤ count444 b) else (if i < 447 then decide (1 ≤ count446 b) else decide (2 ≤ count446 b))) else (if i < 449 then decide (3 ≤ count446 b) else (if i < 450 then decide (4 ≤ count446 b) else decide (1 ≤ count450 b))))) else (if i < 457 then (if i < 454 then (if i < 452 then decide (2 ≤ count450 b) else (if i < 453 then decide (3 ≤ count450 b) else decide (4 ≤ count450 b))) else (if i < 455 then decide (5 ≤ count450 b) else (if i < 456 then decide (6 ≤ count450 b) else decide (7 ≤ count450 b)))) else (if i < 460 then (if i < 458 then decide (1 ≤ count457 b) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b))) else (if i < 461 then decide (2 ≤ count459 b) else (if i < 462 then decide (3 ≤ count459 b) else decide (1 ≤ count462 b)))))) else (if i < 475 then (if i < 469 then (if i < 466 then (if i < 464 then decide (2 ≤ count462 b) else (if i < 465 then decide (1 ≤ count464 b) else decide (2 ≤ count464 b))) else (if i < 467 then decide (1 ≤ count466 b) else (if i < 468 then decide (2 ≤ count466 b) else decide (3 ≤ count466 b)))) else (if i < 472 then (if i < 470 then decide (4 ≤ count466 b) else (if i < 471 then decide (1 ≤ count470 b) else decide (2 ≤ count470 b))) else (if i < 473 then decide (3 ≤ count470 b) else (if i < 474 then decide (4 ≤ count470 b) else decide (5 ≤ count470 b))))) else (if i < 481 then (if i < 478 then (if i < 476 then decide (6 ≤ count470 b) else (if i < 477 then decide (7 ≤ count470 b) else decide (1 ≤ count477 b))) else (if i < 479 then decide (2 ≤ count477 b) else (if i < 480 then decide (3 ≤ count477 b) else decide (4 ≤ count477 b)))) else (if i < 484 then (if i < 482 then decide (5 ≤ count477 b) else (if i < 483 then decide (6 ≤ count477 b) else decide (7 ≤ count477 b))) else (if i < 486 then (if i < 485 then decide (8 ≤ count477 b) else decide (9 ≤ count477 b)) else (if i < 487 then decide (10 ≤ count477 b) else decide (11 ≤ count477 b)))))))) else (if i < 537 then (if i < 512 then (if i < 500 then (if i < 494 then (if i < 491 then (if i < 489 then decide (12 ≤ count477 b) else (if i < 490 then decide (13 ≤ count477 b) else decide (14 ≤ count477 b))) else (if i < 492 then decide (1 ≤ count491 b) else (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b)))) else (if i < 497 then (if i < 495 then decide (2 ≤ count493 b) else (if i < 496 then decide (3 ≤ count493 b) else decide (1 ≤ count496 b))) else (if i < 498 then decide (2 ≤ count496 b) else (if i < 499 then decide (1 ≤ count498 b) else decide (2 ≤ count498 b))))) else (if i < 506 then (if i < 503 then (if i < 501 then decide (1 ≤ count500 b) else (if i < 502 then decide (2 ≤ count500 b) else decide (3 ≤ count500 b))) else (if i < 504 then decide (4 ≤ count500 b) else (if i < 505 then decide (1 ≤ count504 b) else decide (2 ≤ count504 b)))) else (if i < 509 then (if i < 507 then decide (3 ≤ count504 b) else (if i < 508 then decide (4 ≤ count504 b) else decide (5 ≤ count504 b))) else (if i < 510 then decide (6 ≤ count504 b) else (if i < 511 then decide (7 ≤ count504 b) else decide (1 ≤ count511 b)))))) else (if i < 524 then (if i < 518 then (if i < 515 then (if i < 513 then decide (2 ≤ count511 b) else (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b))) else (if i < 516 then decide (3 ≤ count513 b) else (if i < 517 then decide (1 ≤ count516 b) else decide (2 ≤ count516 b)))) else (if i < 521 then (if i < 519 then decide (1 ≤ count518 b) else (if i < 520 then decide (2 ≤ count518 b) else decide (1 ≤ count520 b))) else (if i < 522 then decide (2 ≤ count520 b) else (if i < 523 then decide (3 ≤ count520 b) else decide (4 ≤ count520 b))))) else (if i < 530 then (if i < 527 then (if i < 525 then decide (1 ≤ count524 b) else (if i < 526 then decide (2 ≤ count524 b) else decide (3 ≤ count524 b))) else (if i < 528 then decide (4 ≤ count524 b) else (if i < 529 then decide (5 ≤ count524 b) else decide (6 ≤ count524 b)))) else (if i < 533 then (if i < 531 then decide (7 ≤ count524 b) else (if i < 532 then decide (1 ≤ count531 b) else decide (2 ≤ count531 b))) else (if i < 535 then (if i < 534 then decide (3 ≤ count531 b) else decide (4 ≤ count531 b)) else (if i < 536 then decide (5 ≤ count531 b) else decide (6 ≤ count531 b))))))) else (if i < 561 then (if i < 549 then (if i < 543 then (if i < 540 then (if i < 538 then decide (7 ≤ count531 b) else (if i < 539 then decide (8 ≤ count531 b) else decide (9 ≤ count531 b))) else (if i < 541 then decide (10 ≤ count531 b) else (if i < 542 then decide (11 ≤ count531 b) else decide (12 ≤ count531 b)))) else (if i < 546 then (if i < 544 then decide (13 ≤ count531 b) else (if i < 545 then decide (14 ≤ count531 b) else decide (1 ≤ count545 b))) else (if i < 547 then decide (2 ≤ count545 b) else (if i < 548 then decide (3 ≤ count545 b) else decide (4 ≤ count545 b))))) else (if i < 555 then (if i < 552 then (if i < 550 then decide (5 ≤ count545 b) else (if i < 551 then decide (6 ≤ count545 b) else decide (7 ≤ count545 b))) else (if i < 553 then decide (8 ≤ count545 b) else (if i < 554 then decide (9 ≤ count545 b) else decide (10 ≤ count545 b)))) else (if i < 558 then (if i < 556 then decide (11 ≤ count545 b) else (if i < 557 then decide (12 ≤ count545 b) else decide (13 ≤ count545 b))) else (if i < 559 then decide (14 ≤ count545 b) else (if i < 560 then decide (15 ≤ count545 b) else decide (16 ≤ count545 b)))))) else (if i < 573 then (if i < 567 then (if i < 564 then (if i < 562 then decide (17 ≤ count545 b) else (if i < 563 then decide (18 ≤ count545 b) else decide (19 ≤ count545 b))) else (if i < 565 then decide (20 ≤ count545 b) else (if i < 566 then decide (21 ≤ count545 b) else decide (22 ≤ count545 b)))) else (if i < 570 then (if i < 568 then decide (23 ≤ count545 b) else (if i < 569 then decide (24 ≤ count545 b) else decide (25 ≤ count545 b))) else (if i < 571 then decide (26 ≤ count545 b) else (if i < 572 then decide (27 ≤ count545 b) else decide (28 ≤ count545 b))))) else (if i < 579 then (if i < 576 then (if i < 574 then decide (1 ≤ count573 b) else (if i < 575 then decide (2 ≤ count573 b) else decide (1 ≤ count575 b))) else (if i < 577 then decide (2 ≤ count575 b) else (if i < 578 then decide (3 ≤ count575 b) else decide (1 ≤ count578 b)))) else (if i < 582 then (if i < 580 then decide (2 ≤ count578 b) else (if i < 581 then decide (1 ≤ count580 b) else decide (2 ≤ count580 b))) else (if i < 584 then (if i < 583 then decide (1 ≤ count582 b) else decide (2 ≤ count582 b)) else (if i < 585 then decide (3 ≤ count582 b) else decide (4 ≤ count582 b))))))))) else (if i < 684 then (if i < 635 then (if i < 610 then (if i < 598 then (if i < 592 then (if i < 589 then (if i < 587 then decide (1 ≤ count586 b) else (if i < 588 then decide (2 ≤ count586 b) else decide (3 ≤ count586 b))) else (if i < 590 then decide (4 ≤ count586 b) else (if i < 591 then decide (5 ≤ count586 b) else decide (6 ≤ count586 b)))) else (if i < 595 then (if i < 593 then decide (7 ≤ count586 b) else (if i < 594 then decide (1 ≤ count593 b) else decide (2 ≤ count593 b))) else (if i < 596 then decide (1 ≤ count595 b) else (if i < 597 then decide (2 ≤ count595 b) else decide (3 ≤ count595 b))))) else (if i < 604 then (if i < 601 then (if i < 599 then decide (1 ≤ count598 b) else (if i < 600 then decide (2 ≤ count598 b) else decide (1 ≤ count600 b))) else (if i < 602 then decide (2 ≤ count600 b) else (if i < 603 then decide (1 ≤ count602 b) else decide (2 ≤ count602 b)))) else (if i < 607 then (if i < 605 then decide (3 ≤ count602 b) else (if i < 606 then decide (4 ≤ count602 b) else decide (1 ≤ count606 b))) else (if i < 608 then decide (2 ≤ count606 b) else (if i < 609 then decide (3 ≤ count606 b) else decide (4 ≤ count606 b)))))) else (if i < 622 then (if i < 616 then (if i < 613 then (if i < 611 then decide (5 ≤ count606 b) else (if i < 612 then decide (6 ≤ count606 b) else decide (7 ≤ count606 b))) else (if i < 614 then decide (1 ≤ count613 b) else (if i < 615 then decide (2 ≤ count613 b) else decide (3 ≤ count613 b)))) else (if i < 619 then (if i < 617 then decide (4 ≤ count613 b) else (if i < 618 then decide (5 ≤ count613 b) else decide (6 ≤ count613 b))) else (if i < 620 then decide (7 ≤ count613 b) else (if i < 621 then decide (8 ≤ count613 b) else decide (9 ≤ count613 b))))) else (if i < 628 then (if i < 625 then (if i < 623 then decide (10 ≤ count613 b) else (if i < 624 then decide (11 ≤ count613 b) else decide (12 ≤ count613 b))) else (if i < 626 then decide (13 ≤ count613 b) else (if i < 627 then decide (14 ≤ count613 b) else decide (1 ≤ count627 b)))) else (if i < 631 then (if i < 629 then decide (2 ≤ count627 b) else (if i < 630 then decide (1 ≤ count629 b) else decide (2 ≤ count629 b))) else (if i < 633 then (if i < 632 then decide (3 ≤ count629 b) else decide (1 ≤ count632 b)) else (if i < 634 then decide (2 ≤ count632 b) else decide (1 ≤ count634 b))))))) else (if i < 659 then (if i < 647 then (if i < 641 then (if i < 638 then (if i < 636 then decide (2 ≤ count634 b) else (if i < 637 then decide (1 ≤ count636 b) else decide (2 ≤ count636 b))) else (if i < 639 then decide (3 ≤ count636 b) else (if i < 640 then decide (4 ≤ count636 b) else decide (1 ≤ count640 b)))) else (if i < 644 then (if i < 642 then decide (2 ≤ count640 b) else (if i < 643 then decide (3 ≤ count640 b) else decide (4 ≤ count640 b))) else (if i < 645 then decide (5 ≤ count640 b) else (if i < 646 then decide (6 ≤ count640 b) else decide (7 ≤ count640 b))))) else (if i < 653 then (if i < 650 then (if i < 648 then decide (1 ≤ count647 b) else (if i < 649 then decide (2 ≤ count647 b) else decide (1 ≤ count649 b))) else (if i < 651 then decide (2 ≤ count649 b) else (if i < 652 then decide (1 ≤ count651 b) else decide (2 ≤ count651 b)))) else (if i < 656 then (if i < 654 then decide (3 ≤ count651 b) else (if i < 655 then decide (4 ≤ count651 b) else decide (1 ≤ count655 b))) else (if i < 657 then decide (2 ≤ count655 b) else (if i < 658 then decide (1 ≤ count657 b) else decide (2 ≤ count657 b)))))) else (if i < 671 then (if i < 665 then (if i < 662 then (if i < 660 then decide (1 ≤ count659 b) else (if i < 661 then decide (2 ≤ count659 b) else decide (3 ≤ count659 b))) else (if i < 663 then decide (4 ≤ count659 b) else (if i < 664 then decide (1 ≤ count663 b) else decide (2 ≤ count663 b)))) else (if i < 668 then (if i < 666 then decide (3 ≤ count663 b) else (if i < 667 then decide (4 ≤ count663 b) else decide (5 ≤ count663 b))) else (if i < 669 then decide (6 ≤ count663 b) else (if i < 670 then decide (7 ≤ count663 b) else decide (8 ≤ count663 b))))) else (if i < 677 then (if i < 674 then (if i < 672 then decide (1 ≤ count671 b) else (if i < 673 then decide (2 ≤ count671 b) else decide (3 ≤ count671 b))) else (if i < 675 then decide (4 ≤ count671 b) else (if i < 676 then decide (5 ≤ count671 b) else decide (6 ≤ count671 b)))) else (if i < 680 then (if i < 678 then decide (7 ≤ count671 b) else (if i < 679 then decide (8 ≤ count671 b) else decide (9 ≤ count671 b))) else (if i < 682 then (if i < 681 then decide (10 ≤ count671 b) else decide (11 ≤ count671 b)) else (if i < 683 then decide (12 ≤ count671 b) else decide (13 ≤ count671 b)))))))) else (if i < 733 then (if i < 708 then (if i < 696 then (if i < 690 then (if i < 687 then (if i < 685 then decide (14 ≤ count671 b) else (if i < 686 then decide (15 ≤ count671 b) else decide (1 ≤ count686 b))) else (if i < 688 then decide (2 ≤ count686 b) else (if i < 689 then decide (3 ≤ count686 b) else decide (4 ≤ count686 b)))) else (if i < 693 then (if i < 691 then decide (5 ≤ count686 b) else (if i < 692 then decide (6 ≤ count686 b) else decide (7 ≤ count686 b))) else (if i < 694 then decide (8 ≤ count686 b) else (if i < 695 then decide (9 ≤ count686 b) else decide (10 ≤ count686 b))))) else (if i < 702 then (if i < 699 then (if i < 697 then decide (11 ≤ count686 b) else (if i < 698 then decide (12 ≤ count686 b) else decide (13 ≤ count686 b))) else (if i < 700 then decide (14 ≤ count686 b) else (if i < 701 then decide (15 ≤ count686 b) else decide (16 ≤ count686 b)))) else (if i < 705 then (if i < 703 then decide (17 ≤ count686 b) else (if i < 704 then decide (18 ≤ count686 b) else decide (19 ≤ count686 b))) else (if i < 706 then decide (20 ≤ count686 b) else (if i < 707 then decide (21 ≤ count686 b) else decide (22 ≤ count686 b)))))) else (if i < 720 then (if i < 714 then (if i < 711 then (if i < 709 then decide (23 ≤ count686 b) else (if i < 710 then decide (24 ≤ count686 b) else decide (25 ≤ count686 b))) else (if i < 712 then decide (26 ≤ count686 b) else (if i < 713 then decide (27 ≤ count686 b) else decide (28 ≤ count686 b)))) else (if i < 717 then (if i < 715 then decide (29 ≤ count686 b) else (if i < 716 then decide (1 ≤ count715 b) else decide (2 ≤ count715 b))) else (if i < 718 then decide (3 ≤ count715 b) else (if i < 719 then decide (4 ≤ count715 b) else decide (5 ≤ count715 b))))) else (if i < 726 then (if i < 723 then (if i < 721 then decide (6 ≤ count715 b) else (if i < 722 then decide (7 ≤ count715 b) else decide (8 ≤ count715 b))) else (if i < 724 then decide (9 ≤ count715 b) else (if i < 725 then decide (10 ≤ count715 b) else decide (11 ≤ count715 b)))) else (if i < 729 then (if i < 727 then decide (12 ≤ count715 b) else (if i < 728 then decide (13 ≤ count715 b) else decide (14 ≤ count715 b))) else (if i < 731 then (if i < 730 then decide (15 ≤ count715 b) else decide (16 ≤ count715 b)) else (if i < 732 then decide (17 ≤ count715 b) else decide (18 ≤ count715 b))))))) else (if i < 757 then (if i < 745 then (if i < 739 then (if i < 736 then (if i < 734 then decide (19 ≤ count715 b) else (if i < 735 then decide (20 ≤ count715 b) else decide (21 ≤ count715 b))) else (if i < 737 then decide (22 ≤ count715 b) else (if i < 738 then decide (23 ≤ count715 b) else decide (24 ≤ count715 b)))) else (if i < 742 then (if i < 740 then decide (25 ≤ count715 b) else (if i < 741 then decide (26 ≤ count715 b) else decide (27 ≤ count715 b))) else (if i < 743 then decide (28 ≤ count715 b) else (if i < 744 then decide (29 ≤ count715 b) else decide (30 ≤ count715 b))))) else (if i < 751 then (if i < 748 then (if i < 746 then decide (31 ≤ count715 b) else (if i < 747 then decide (32 ≤ count715 b) else decide (33 ≤ count715 b))) else (if i < 749 then decide (34 ≤ count715 b) else (if i < 750 then decide (35 ≤ count715 b) else decide (36 ≤ count715 b)))) else (if i < 754 then (if i < 752 then decide (37 ≤ count715 b) else (if i < 753 then decide (38 ≤ count715 b) else decide (39 ≤ count715 b))) else (if i < 755 then decide (40 ≤ count715 b) else (if i < 756 then decide (41 ≤ count715 b) else decide (42 ≤ count715 b)))))) else (if i < 769 then (if i < 763 then (if i < 760 then (if i < 758 then decide (1 ≤ count757 b) else (if i < 759 then decide (2 ≤ count757 b) else decide (1 ≤ count759 b))) else (if i < 761 then decide (2 ≤ count759 b) else (if i < 762 then decide (3 ≤ count759 b) else decide (1 ≤ count762 b)))) else (if i < 766 then (if i < 764 then decide (2 ≤ count762 b) else (if i < 765 then decide (1 ≤ count764 b) else decide (2 ≤ count764 b))) else (if i < 767 then decide (1 ≤ count766 b) else (if i < 768 then decide (2 ≤ count766 b) else decide (3 ≤ count766 b))))) else (if i < 775 then (if i < 772 then (if i < 770 then decide (4 ≤ count766 b) else (if i < 771 then decide (1 ≤ count770 b) else decide (2 ≤ count770 b))) else (if i < 773 then decide (3 ≤ count770 b) else (if i < 774 then decide (4 ≤ count770 b) else decide (5 ≤ count770 b)))) else (if i < 778 then (if i < 776 then decide (6 ≤ count770 b) else (if i < 777 then decide (7 ≤ count770 b) else decide (1 ≤ count777 b))) else (if i < 780 then (if i < 779 then decide (2 ≤ count777 b) else decide (1 ≤ count779 b)) else (if i < 781 then decide (2 ≤ count779 b) else decide (3 ≤ count779 b))))))))))) else (if i < 1173 then (if i < 977 then (if i < 879 then (if i < 830 then (if i < 806 then (if i < 794 then (if i < 788 then (if i < 785 then (if i < 783 then decide (1 ≤ count782 b) else (if i < 784 then decide (2 ≤ count782 b) else decide (1 ≤ count784 b))) else (if i < 786 then decide (2 ≤ count784 b) else (if i < 787 then decide (1 ≤ count786 b) else decide (2 ≤ count786 b)))) else (if i < 791 then (if i < 789 then decide (3 ≤ count786 b) else (if i < 790 then decide (4 ≤ count786 b) else decide (1 ≤ count790 b))) else (if i < 792 then decide (2 ≤ count790 b) else (if i < 793 then decide (3 ≤ count790 b) else decide (4 ≤ count790 b))))) else (if i < 800 then (if i < 797 then (if i < 795 then decide (5 ≤ count790 b) else (if i < 796 then decide (6 ≤ count790 b) else decide (7 ≤ count790 b))) else (if i < 798 then decide (1 ≤ count797 b) else (if i < 799 then decide (2 ≤ count797 b) else decide (3 ≤ count797 b)))) else (if i < 803 then (if i < 801 then decide (4 ≤ count797 b) else (if i < 802 then decide (5 ≤ count797 b) else decide (6 ≤ count797 b))) else (if i < 804 then decide (7 ≤ count797 b) else (if i < 805 then decide (8 ≤ count797 b) else decide (9 ≤ count797 b)))))) else (if i < 818 then (if i < 812 then (if i < 809 then (if i < 807 then decide (10 ≤ count797 b) else (if i < 808 then decide (11 ≤ count797 b) else decide (12 ≤ count797 b))) else (if i < 810 then decide (13 ≤ count797 b) else (if i < 811 then decide (14 ≤ count797 b) else decide (1 ≤ count811 b)))) else (if i < 815 then (if i < 813 then decide (2 ≤ count811 b) else (if i < 814 then decide (1 ≤ count813 b) else decide (2 ≤ count813 b))) else (if i < 816 then decide (3 ≤ count813 b) else (if i < 817 then decide (1 ≤ count816 b) else decide (2 ≤ count816 b))))) else (if i < 824 then (if i < 821 then (if i < 819 then decide (1 ≤ count818 b) else (if i < 820 then decide (2 ≤ count818 b) else decide (1 ≤ count820 b))) else (if i < 822 then decide (2 ≤ count820 b) else (if i < 823 then decide (3 ≤ count820 b) else decide (4 ≤ count820 b)))) else (if i < 827 then (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (3 ≤ count824 b))) else (if i < 828 then decide (4 ≤ count824 b) else (if i < 829 then decide (5 ≤ count824 b) else decide (6 ≤ count824 b))))))) else (if i < 854 then (if i < 842 then (if i < 836 then (if i < 833 then (if i < 831 then decide (7 ≤ count824 b) else (if i < 832 then decide (1 ≤ count831 b) else decide (2 ≤ count831 b))) else (if i < 834 then decide (1 ≤ count833 b) else (if i < 835 then decide (2 ≤ count833 b) else decide (3 ≤ count833 b)))) else (if i < 839 then (if i < 837 then decide (1 ≤ count836 b) else (if i < 838 then decide (2 ≤ count836 b) else decide (1 ≤ count838 b))) else (if i < 840 then decide (2 ≤ count838 b) else (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b))))) else (if i < 848 then (if i < 845 then (if i < 843 then decide (3 ≤ count840 b) else (if i < 844 then decide (4 ≤ count840 b) else decide (1 ≤ count844 b))) else (if i < 846 then decide (2 ≤ count844 b) else (if i < 847 then decide (3 ≤ count844 b) else decide (4 ≤ count844 b)))) else (if i < 851 then (if i < 849 then decide (5 ≤ count844 b) else (if i < 850 then decide (6 ≤ count844 b) else decide (7 ≤ count844 b))) else (if i < 852 then decide (1 ≤ count851 b) else (if i < 853 then decide (2 ≤ count851 b) else decide (3 ≤ count851 b)))))) else (if i < 866 then (if i < 860 then (if i < 857 then (if i < 855 then decide (4 ≤ count851 b) else (if i < 856 then decide (5 ≤ count851 b) else decide (6 ≤ count851 b))) else (if i < 858 then decide (7 ≤ count851 b) else (if i < 859 then decide (8 ≤ count851 b) else decide (9 ≤ count851 b)))) else (if i < 863 then (if i < 861 then decide (10 ≤ count851 b) else (if i < 862 then decide (11 ≤ count851 b) else decide (12 ≤ count851 b))) else (if i < 864 then decide (13 ≤ count851 b) else (if i < 865 then decide (14 ≤ count851 b) else decide (1 ≤ count865 b))))) else (if i < 872 then (if i < 869 then (if i < 867 then decide (2 ≤ count865 b) else (if i < 868 then decide (3 ≤ count865 b) else decide (4 ≤ count865 b))) else (if i < 870 then decide (5 ≤ count865 b) else (if i < 871 then decide (6 ≤ count865 b) else decide (7 ≤ count865 b)))) else (if i < 875 then (if i < 873 then decide (8 ≤ count865 b) else (if i < 874 then decide (9 ≤ count865 b) else decide (10 ≤ count865 b))) else (if i < 877 then (if i < 876 then decide (11 ≤ count865 b) else decide (12 ≤ count865 b)) else (if i < 878 then decide (13 ≤ count865 b) else decide (14 ≤ count865 b)))))))) else (if i < 928 then (if i < 903 then (if i < 891 then (if i < 885 then (if i < 882 then (if i < 880 then decide (15 ≤ count865 b) else (if i < 881 then decide (16 ≤ count865 b) else decide (17 ≤ count865 b))) else (if i < 883 then decide (1 ≤ count882 b) else (if i < 884 then decide (2 ≤ count882 b) else decide (1 ≤ count884 b)))) else (if i < 888 then (if i < 886 then decide (2 ≤ count884 b) else (if i < 887 then decide (3 ≤ count884 b) else decide (1 ≤ count887 b))) else (if i < 889 then decide (2 ≤ count887 b) else (if i < 890 then decide (1 ≤ count889 b) else decide (2 ≤ count889 b))))) else (if i < 897 then (if i < 894 then (if i < 892 then decide (1 ≤ count891 b) else (if i < 893 then decide (2 ≤ count891 b) else decide (3 ≤ count891 b))) else (if i < 895 then decide (4 ≤ count891 b) else (if i < 896 then decide (1 ≤ count895 b) else decide (2 ≤ count895 b)))) else (if i < 900 then (if i < 898 then decide (3 ≤ count895 b) else (if i < 899 then decide (4 ≤ count895 b) else decide (5 ≤ count895 b))) else (if i < 901 then decide (6 ≤ count895 b) else (if i < 902 then decide (7 ≤ count895 b) else decide (1 ≤ count902 b)))))) else (if i < 915 then (if i < 909 then (if i < 906 then (if i < 904 then decide (2 ≤ count902 b) else (if i < 905 then decide (1 ≤ count904 b) else decide (2 ≤ count904 b))) else (if i < 907 then decide (3 ≤ count904 b) else (if i < 908 then decide (1 ≤ count907 b) else decide (2 ≤ count907 b)))) else (if i < 912 then (if i < 910 then decide (1 ≤ count909 b) else (if i < 911 then decide (2 ≤ count909 b) else decide (1 ≤ count911 b))) else (if i < 913 then decide (2 ≤ count911 b) else (if i < 914 then decide (3 ≤ count911 b) else decide (4 ≤ count911 b))))) else (if i < 921 then (if i < 918 then (if i < 916 then decide (1 ≤ count915 b) else (if i < 917 then decide (2 ≤ count915 b) else decide (3 ≤ count915 b))) else (if i < 919 then decide (4 ≤ count915 b) else (if i < 920 then decide (5 ≤ count915 b) else decide (6 ≤ count915 b)))) else (if i < 924 then (if i < 922 then decide (7 ≤ count915 b) else (if i < 923 then decide (1 ≤ count922 b) else decide (2 ≤ count922 b))) else (if i < 926 then (if i < 925 then decide (3 ≤ count922 b) else decide (4 ≤ count922 b)) else (if i < 927 then decide (5 ≤ count922 b) else decide (6 ≤ count922 b))))))) else (if i < 952 then (if i < 940 then (if i < 934 then (if i < 931 then (if i < 929 then decide (7 ≤ count922 b) else (if i < 930 then decide (8 ≤ count922 b) else decide (9 ≤ count922 b))) else (if i < 932 then decide (10 ≤ count922 b) else (if i < 933 then decide (11 ≤ count922 b) else decide (12 ≤ count922 b)))) else (if i < 937 then (if i < 935 then decide (13 ≤ count922 b) else (if i < 936 then decide (14 ≤ count922 b) else decide (1 ≤ count936 b))) else (if i < 938 then decide (2 ≤ count936 b) else (if i < 939 then decide (1 ≤ count938 b) else decide (2 ≤ count938 b))))) else (if i < 946 then (if i < 943 then (if i < 941 then decide (3 ≤ count938 b) else (if i < 942 then decide (1 ≤ count941 b) else decide (2 ≤ count941 b))) else (if i < 944 then decide (1 ≤ count943 b) else (if i < 945 then decide (2 ≤ count943 b) else decide (1 ≤ count945 b)))) else (if i < 949 then (if i < 947 then decide (2 ≤ count945 b) else (if i < 948 then decide (3 ≤ count945 b) else decide (4 ≤ count945 b))) else (if i < 950 then decide (1 ≤ count949 b) else (if i < 951 then decide (2 ≤ count949 b) else decide (3 ≤ count949 b)))))) else (if i < 964 then (if i < 958 then (if i < 955 then (if i < 953 then decide (4 ≤ count949 b) else (if i < 954 then decide (5 ≤ count949 b) else decide (6 ≤ count949 b))) else (if i < 956 then decide (7 ≤ count949 b) else (if i < 957 then decide (1 ≤ count956 b) else decide (2 ≤ count956 b)))) else (if i < 961 then (if i < 959 then decide (1 ≤ count958 b) else (if i < 960 then decide (2 ≤ count958 b) else decide (1 ≤ count960 b))) else (if i < 962 then decide (2 ≤ count960 b) else (if i < 963 then decide (3 ≤ count960 b) else decide (4 ≤ count960 b))))) else (if i < 970 then (if i < 967 then (if i < 965 then decide (1 ≤ count964 b) else (if i < 966 then decide (2 ≤ count964 b) else decide (1 ≤ count966 b))) else (if i < 968 then decide (2 ≤ count966 b) else (if i < 969 then decide (1 ≤ count968 b) else decide (2 ≤ count968 b)))) else (if i < 973 then (if i < 971 then decide (3 ≤ count968 b) else (if i < 972 then decide (4 ≤ count968 b) else decide (1 ≤ count972 b))) else (if i < 975 then (if i < 974 then decide (2 ≤ count972 b) else decide (3 ≤ count972 b)) else (if i < 976 then decide (4 ≤ count972 b) else decide (5 ≤ count972 b))))))))) else (if i < 1075 then (if i < 1026 then (if i < 1001 then (if i < 989 then (if i < 983 then (if i < 980 then (if i < 978 then decide (6 ≤ count972 b) else (if i < 979 then decide (7 ≤ count972 b) else decide (8 ≤ count972 b))) else (if i < 981 then decide (1 ≤ count980 b) else (if i < 982 then decide (2 ≤ count980 b) else decide (3 ≤ count980 b)))) else (if i < 986 then (if i < 984 then decide (4 ≤ count980 b) else (if i < 985 then decide (5 ≤ count980 b) else decide (6 ≤ count980 b))) else (if i < 987 then decide (7 ≤ count980 b) else (if i < 988 then decide (8 ≤ count980 b) else decide (9 ≤ count980 b))))) else (if i < 995 then (if i < 992 then (if i < 990 then decide (10 ≤ count980 b) else (if i < 991 then decide (11 ≤ count980 b) else decide (12 ≤ count980 b))) else (if i < 993 then decide (13 ≤ count980 b) else (if i < 994 then decide (14 ≤ count980 b) else decide (15 ≤ count980 b)))) else (if i < 998 then (if i < 996 then decide (1 ≤ count995 b) else (if i < 997 then decide (2 ≤ count995 b) else decide (3 ≤ count995 b))) else (if i < 999 then decide (4 ≤ count995 b) else (if i < 1000 then decide (5 ≤ count995 b) else decide (6 ≤ count995 b)))))) else (if i < 1013 then (if i < 1007 then (if i < 1004 then (if i < 1002 then decide (7 ≤ count995 b) else (if i < 1003 then decide (8 ≤ count995 b) else decide (9 ≤ count995 b))) else (if i < 1005 then decide (10 ≤ count995 b) else (if i < 1006 then decide (11 ≤ count995 b) else decide (12 ≤ count995 b)))) else (if i < 1010 then (if i < 1008 then decide (13 ≤ count995 b) else (if i < 1009 then decide (14 ≤ count995 b) else decide (15 ≤ count995 b))) else (if i < 1011 then decide (16 ≤ count995 b) else (if i < 1012 then decide (17 ≤ count995 b) else decide (1 ≤ count1012 b))))) else (if i < 1019 then (if i < 1016 then (if i < 1014 then decide (2 ≤ count1012 b) else (if i < 1015 then decide (3 ≤ count1012 b) else decide (4 ≤ count1012 b))) else (if i < 1017 then decide (5 ≤ count1012 b) else (if i < 1018 then decide (6 ≤ count1012 b) else decide (7 ≤ count1012 b)))) else (if i < 1022 then (if i < 1020 then decide (8 ≤ count1012 b) else (if i < 1021 then decide (9 ≤ count1012 b) else decide (10 ≤ count1012 b))) else (if i < 1024 then (if i < 1023 then decide (11 ≤ count1012 b) else decide (12 ≤ count1012 b)) else (if i < 1025 then decide (13 ≤ count1012 b) else decide (14 ≤ count1012 b))))))) else (if i < 1050 then (if i < 1038 then (if i < 1032 then (if i < 1029 then (if i < 1027 then decide (15 ≤ count1012 b) else (if i < 1028 then decide (16 ≤ count1012 b) else decide (17 ≤ count1012 b))) else (if i < 1030 then decide (1 ≤ count1029 b) else (if i < 1031 then decide (2 ≤ count1029 b) else decide (1 ≤ count1031 b)))) else (if i < 1035 then (if i < 1033 then decide (2 ≤ count1031 b) else (if i < 1034 then decide (3 ≤ count1031 b) else decide (1 ≤ count1034 b))) else (if i < 1036 then decide (2 ≤ count1034 b) else (if i < 1037 then decide (1 ≤ count1036 b) else decide (2 ≤ count1036 b))))) else (if i < 1044 then (if i < 1041 then (if i < 1039 then decide (3 ≤ count1036 b) else (if i < 1040 then decide (1 ≤ count1039 b) else decide (2 ≤ count1039 b))) else (if i < 1042 then decide (3 ≤ count1039 b) else (if i < 1043 then decide (4 ≤ count1039 b) else decide (5 ≤ count1039 b)))) else (if i < 1047 then (if i < 1045 then decide (6 ≤ count1039 b) else (if i < 1046 then decide (1 ≤ count1045 b) else decide (2 ≤ count1045 b))) else (if i < 1048 then decide (1 ≤ count1047 b) else (if i < 1049 then decide (2 ≤ count1047 b) else decide (3 ≤ count1047 b)))))) else (if i < 1062 then (if i < 1056 then (if i < 1053 then (if i < 1051 then decide (1 ≤ count1050 b) else (if i < 1052 then decide (2 ≤ count1050 b) else decide (1 ≤ count1052 b))) else (if i < 1054 then decide (2 ≤ count1052 b) else (if i < 1055 then decide (1 ≤ count1054 b) else decide (2 ≤ count1054 b)))) else (if i < 1059 then (if i < 1057 then decide (3 ≤ count1054 b) else (if i < 1058 then decide (4 ≤ count1054 b) else decide (1 ≤ count1058 b))) else (if i < 1060 then decide (2 ≤ count1058 b) else (if i < 1061 then decide (3 ≤ count1058 b) else decide (4 ≤ count1058 b))))) else (if i < 1068 then (if i < 1065 then (if i < 1063 then decide (5 ≤ count1058 b) else (if i < 1064 then decide (6 ≤ count1058 b) else decide (7 ≤ count1058 b))) else (if i < 1066 then decide (1 ≤ count1065 b) else (if i < 1067 then decide (2 ≤ count1065 b) else decide (3 ≤ count1065 b)))) else (if i < 1071 then (if i < 1069 then decide (4 ≤ count1065 b) else (if i < 1070 then decide (5 ≤ count1065 b) else decide (6 ≤ count1065 b))) else (if i < 1073 then (if i < 1072 then decide (7 ≤ count1065 b) else decide (8 ≤ count1065 b)) else (if i < 1074 then decide (9 ≤ count1065 b) else decide (10 ≤ count1065 b)))))))) else (if i < 1124 then (if i < 1099 then (if i < 1087 then (if i < 1081 then (if i < 1078 then (if i < 1076 then decide (11 ≤ count1065 b) else (if i < 1077 then decide (12 ≤ count1065 b) else decide (13 ≤ count1065 b))) else (if i < 1079 then decide (1 ≤ count1078 b) else (if i < 1080 then decide (2 ≤ count1078 b) else decide (1 ≤ count1080 b)))) else (if i < 1084 then (if i < 1082 then decide (2 ≤ count1080 b) else (if i < 1083 then decide (3 ≤ count1080 b) else decide (1 ≤ count1083 b))) else (if i < 1085 then decide (2 ≤ count1083 b) else (if i < 1086 then decide (1 ≤ count1085 b) else decide (2 ≤ count1085 b))))) else (if i < 1093 then (if i < 1090 then (if i < 1088 then decide (3 ≤ count1085 b) else (if i < 1089 then decide (1 ≤ count1088 b) else decide (2 ≤ count1088 b))) else (if i < 1091 then decide (3 ≤ count1088 b) else (if i < 1092 then decide (4 ≤ count1088 b) else decide (5 ≤ count1088 b)))) else (if i < 1096 then (if i < 1094 then decide (6 ≤ count1088 b) else (if i < 1095 then decide (1 ≤ count1094 b) else decide (2 ≤ count1094 b))) else (if i < 1097 then decide (1 ≤ count1096 b) else (if i < 1098 then decide (2 ≤ count1096 b) else decide (3 ≤ count1096 b)))))) else (if i < 1111 then (if i < 1105 then (if i < 1102 then (if i < 1100 then decide (1 ≤ count1099 b) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (1 ≤ count1101 b))) else (if i < 1103 then decide (2 ≤ count1101 b) else (if i < 1104 then decide (1 ≤ count1103 b) else decide (2 ≤ count1103 b)))) else (if i < 1108 then (if i < 1106 then decide (3 ≤ count1103 b) else (if i < 1107 then decide (4 ≤ count1103 b) else decide (1 ≤ count1107 b))) else (if i < 1109 then decide (2 ≤ count1107 b) else (if i < 1110 then decide (3 ≤ count1107 b) else decide (4 ≤ count1107 b))))) else (if i < 1117 then (if i < 1114 then (if i < 1112 then decide (5 ≤ count1107 b) else (if i < 1113 then decide (6 ≤ count1107 b) else decide (7 ≤ count1107 b))) else (if i < 1115 then decide (1 ≤ count1114 b) else (if i < 1116 then decide (2 ≤ count1114 b) else decide (3 ≤ count1114 b)))) else (if i < 1120 then (if i < 1118 then decide (4 ≤ count1114 b) else (if i < 1119 then decide (5 ≤ count1114 b) else decide (6 ≤ count1114 b))) else (if i < 1122 then (if i < 1121 then decide (7 ≤ count1114 b) else decide (8 ≤ count1114 b)) else (if i < 1123 then decide (9 ≤ count1114 b) else decide (10 ≤ count1114 b))))))) else (if i < 1148 then (if i < 1136 then (if i < 1130 then (if i < 1127 then (if i < 1125 then decide (11 ≤ count1114 b) else (if i < 1126 then decide (12 ≤ count1114 b) else decide (13 ≤ count1114 b))) else (if i < 1128 then decide (1 ≤ count1127 b) else (if i < 1129 then decide (2 ≤ count1127 b) else decide (3 ≤ count1127 b)))) else (if i < 1133 then (if i < 1131 then decide (4 ≤ count1127 b) else (if i < 1132 then decide (5 ≤ count1127 b) else decide (6 ≤ count1127 b))) else (if i < 1134 then decide (7 ≤ count1127 b) else (if i < 1135 then decide (8 ≤ count1127 b) else decide (9 ≤ count1127 b))))) else (if i < 1142 then (if i < 1139 then (if i < 1137 then decide (10 ≤ count1127 b) else (if i < 1138 then decide (11 ≤ count1127 b) else decide (12 ≤ count1127 b))) else (if i < 1140 then decide (13 ≤ count1127 b) else (if i < 1141 then decide (14 ≤ count1127 b) else decide (15 ≤ count1127 b)))) else (if i < 1145 then (if i < 1143 then decide (16 ≤ count1127 b) else (if i < 1144 then decide (17 ≤ count1127 b) else decide (18 ≤ count1127 b))) else (if i < 1146 then decide (19 ≤ count1127 b) else (if i < 1147 then decide (20 ≤ count1127 b) else decide (21 ≤ count1127 b)))))) else (if i < 1160 then (if i < 1154 then (if i < 1151 then (if i < 1149 then decide (22 ≤ count1127 b) else (if i < 1150 then decide (23 ≤ count1127 b) else decide (24 ≤ count1127 b))) else (if i < 1152 then decide (25 ≤ count1127 b) else (if i < 1153 then decide (26 ≤ count1127 b) else decide (1 ≤ count1153 b)))) else (if i < 1157 then (if i < 1155 then decide (2 ≤ count1153 b) else (if i < 1156 then decide (1 ≤ count1155 b) else decide (2 ≤ count1155 b))) else (if i < 1158 then decide (3 ≤ count1155 b) else (if i < 1159 then decide (1 ≤ count1158 b) else decide (2 ≤ count1158 b))))) else (if i < 1166 then (if i < 1163 then (if i < 1161 then decide (1 ≤ count1160 b) else (if i < 1162 then decide (2 ≤ count1160 b) else decide (3 ≤ count1160 b))) else (if i < 1164 then decide (1 ≤ count1163 b) else (if i < 1165 then decide (2 ≤ count1163 b) else decide (3 ≤ count1163 b)))) else (if i < 1169 then (if i < 1167 then decide (4 ≤ count1163 b) else (if i < 1168 then decide (5 ≤ count1163 b) else decide (6 ≤ count1163 b))) else (if i < 1171 then (if i < 1170 then decide (1 ≤ count1169 b) else decide (2 ≤ count1169 b)) else (if i < 1172 then decide (1 ≤ count1171 b) else decide (2 ≤ count1171 b)))))))))) else (if i < 1368 then (if i < 1270 then (if i < 1221 then (if i < 1197 then (if i < 1185 then (if i < 1179 then (if i < 1176 then (if i < 1174 then decide (3 ≤ count1171 b) else (if i < 1175 then decide (1 ≤ count1174 b) else decide (2 ≤ count1174 b))) else (if i < 1177 then decide (1 ≤ count1176 b) else (if i < 1178 then decide (2 ≤ count1176 b) else decide (1 ≤ count1178 b)))) else (if i < 1182 then (if i < 1180 then decide (2 ≤ count1178 b) else (if i < 1181 then decide (3 ≤ count1178 b) else decide (4 ≤ count1178 b))) else (if i < 1183 then decide (1 ≤ count1182 b) else (if i < 1184 then decide (2 ≤ count1182 b) else decide (3 ≤ count1182 b))))) else (if i < 1191 then (if i < 1188 then (if i < 1186 then decide (4 ≤ count1182 b) else (if i < 1187 then decide (5 ≤ count1182 b) else decide (6 ≤ count1182 b))) else (if i < 1189 then decide (7 ≤ count1182 b) else (if i < 1190 then decide (1 ≤ count1189 b) else decide (2 ≤ count1189 b)))) else (if i < 1194 then (if i < 1192 then decide (3 ≤ count1189 b) else (if i < 1193 then decide (4 ≤ count1189 b) else decide (5 ≤ count1189 b))) else (if i < 1195 then decide (6 ≤ count1189 b) else (if i < 1196 then decide (7 ≤ count1189 b) else decide (8 ≤ count1189 b)))))) else (if i < 1209 then (if i < 1203 then (if i < 1200 then (if i < 1198 then decide (9 ≤ count1189 b) else (if i < 1199 then decide (10 ≤ count1189 b) else decide (11 ≤ count1189 b))) else (if i < 1201 then decide (12 ≤ count1189 b) else (if i < 1202 then decide (13 ≤ count1189 b) else decide (1 ≤ count1202 b)))) else (if i < 1206 then (if i < 1204 then decide (2 ≤ count1202 b) else (if i < 1205 then decide (1 ≤ count1204 b) else decide (2 ≤ count1204 b))) else (if i < 1207 then decide (3 ≤ count1204 b) else (if i < 1208 then decide (1 ≤ count1207 b) else decide (2 ≤ count1207 b))))) else (if i < 1215 then (if i < 1212 then (if i < 1210 then decide (1 ≤ count1209 b) else (if i < 1211 then decide (2 ≤ count1209 b) else decide (1 ≤ count1211 b))) else (if i < 1213 then decide (2 ≤ count1211 b) else (if i < 1214 then decide (3 ≤ count1211 b) else decide (4 ≤ count1211 b)))) else (if i < 1218 then (if i < 1216 then decide (1 ≤ count1215 b) else (if i < 1217 then decide (2 ≤ count1215 b) else decide (3 ≤ count1215 b))) else (if i < 1219 then decide (4 ≤ count1215 b) else (if i < 1220 then decide (5 ≤ count1215 b) else decide (6 ≤ count1215 b))))))) else (if i < 1245 then (if i < 1233 then (if i < 1227 then (if i < 1224 then (if i < 1222 then decide (7 ≤ count1215 b) else (if i < 1223 then decide (1 ≤ count1222 b) else decide (2 ≤ count1222 b))) else (if i < 1225 then decide (1 ≤ count1224 b) else (if i < 1226 then decide (2 ≤ count1224 b) else decide (3 ≤ count1224 b)))) else (if i < 1230 then (if i < 1228 then decide (1 ≤ count1227 b) else (if i < 1229 then decide (2 ≤ count1227 b) else decide (1 ≤ count1229 b))) else (if i < 1231 then decide (2 ≤ count1229 b) else (if i < 1232 then decide (1 ≤ count1231 b) else decide (2 ≤ count1231 b))))) else (if i < 1239 then (if i < 1236 then (if i < 1234 then decide (3 ≤ count1231 b) else (if i < 1235 then decide (4 ≤ count1231 b) else decide (1 ≤ count1235 b))) else (if i < 1237 then decide (2 ≤ count1235 b) else (if i < 1238 then decide (3 ≤ count1235 b) else decide (4 ≤ count1235 b)))) else (if i < 1242 then (if i < 1240 then decide (5 ≤ count1235 b) else (if i < 1241 then decide (6 ≤ count1235 b) else decide (7 ≤ count1235 b))) else (if i < 1243 then decide (1 ≤ count1242 b) else (if i < 1244 then decide (2 ≤ count1242 b) else decide (3 ≤ count1242 b)))))) else (if i < 1257 then (if i < 1251 then (if i < 1248 then (if i < 1246 then decide (4 ≤ count1242 b) else (if i < 1247 then decide (5 ≤ count1242 b) else decide (6 ≤ count1242 b))) else (if i < 1249 then decide (7 ≤ count1242 b) else (if i < 1250 then decide (8 ≤ count1242 b) else decide (9 ≤ count1242 b)))) else (if i < 1254 then (if i < 1252 then decide (10 ≤ count1242 b) else (if i < 1253 then decide (11 ≤ count1242 b) else decide (12 ≤ count1242 b))) else (if i < 1255 then decide (13 ≤ count1242 b) else (if i < 1256 then decide (14 ≤ count1242 b) else decide (1 ≤ count1256 b))))) else (if i < 1263 then (if i < 1260 then (if i < 1258 then decide (2 ≤ count1256 b) else (if i < 1259 then decide (3 ≤ count1256 b) else decide (4 ≤ count1256 b))) else (if i < 1261 then decide (5 ≤ count1256 b) else (if i < 1262 then decide (6 ≤ count1256 b) else decide (7 ≤ count1256 b)))) else (if i < 1266 then (if i < 1264 then decide (8 ≤ count1256 b) else (if i < 1265 then decide (9 ≤ count1256 b) else decide (10 ≤ count1256 b))) else (if i < 1268 then (if i < 1267 then decide (11 ≤ count1256 b) else decide (12 ≤ count1256 b)) else (if i < 1269 then decide (13 ≤ count1256 b) else decide (14 ≤ count1256 b)))))))) else (if i < 1319 then (if i < 1294 then (if i < 1282 then (if i < 1276 then (if i < 1273 then (if i < 1271 then decide (15 ≤ count1256 b) else (if i < 1272 then decide (16 ≤ count1256 b) else decide (17 ≤ count1256 b))) else (if i < 1274 then decide (18 ≤ count1256 b) else (if i < 1275 then decide (19 ≤ count1256 b) else decide (20 ≤ count1256 b)))) else (if i < 1279 then (if i < 1277 then decide (21 ≤ count1256 b) else (if i < 1278 then decide (22 ≤ count1256 b) else decide (23 ≤ count1256 b))) else (if i < 1280 then decide (24 ≤ count1256 b) else (if i < 1281 then decide (25 ≤ count1256 b) else decide (26 ≤ count1256 b))))) else (if i < 1288 then (if i < 1285 then (if i < 1283 then decide (27 ≤ count1256 b) else (if i < 1284 then decide (1 ≤ count1283 b) else decide (2 ≤ count1283 b))) else (if i < 1286 then decide (3 ≤ count1283 b) else (if i < 1287 then decide (4 ≤ count1283 b) else decide (5 ≤ count1283 b)))) else (if i < 1291 then (if i < 1289 then decide (6 ≤ count1283 b) else (if i < 1290 then decide (7 ≤ count1283 b) else decide (8 ≤ count1283 b))) else (if i < 1292 then decide (9 ≤ count1283 b) else (if i < 1293 then decide (10 ≤ count1283 b) else decide (11 ≤ count1283 b)))))) else (if i < 1306 then (if i < 1300 then (if i < 1297 then (if i < 1295 then decide (12 ≤ count1283 b) else (if i < 1296 then decide (13 ≤ count1283 b) else decide (14 ≤ count1283 b))) else (if i < 1298 then decide (15 ≤ count1283 b) else (if i < 1299 then decide (16 ≤ count1283 b) else decide (17 ≤ count1283 b)))) else (if i < 1303 then (if i < 1301 then decide (18 ≤ count1283 b) else (if i < 1302 then decide (19 ≤ count1283 b) else decide (20 ≤ count1283 b))) else (if i < 1304 then decide (21 ≤ count1283 b) else (if i < 1305 then decide (22 ≤ count1283 b) else decide (23 ≤ count1283 b))))) else (if i < 1312 then (if i < 1309 then (if i < 1307 then decide (24 ≤ count1283 b) else (if i < 1308 then decide (25 ≤ count1283 b) else decide (26 ≤ count1283 b))) else (if i < 1310 then decide (27 ≤ count1283 b) else (if i < 1311 then decide (28 ≤ count1283 b) else decide (29 ≤ count1283 b)))) else (if i < 1315 then (if i < 1313 then decide (30 ≤ count1283 b) else (if i < 1314 then decide (31 ≤ count1283 b) else decide (32 ≤ count1283 b))) else (if i < 1317 then (if i < 1316 then decide (33 ≤ count1283 b) else decide (34 ≤ count1283 b)) else (if i < 1318 then decide (35 ≤ count1283 b) else decide (36 ≤ count1283 b))))))) else (if i < 1343 then (if i < 1331 then (if i < 1325 then (if i < 1322 then (if i < 1320 then decide (37 ≤ count1283 b) else (if i < 1321 then decide (38 ≤ count1283 b) else decide (39 ≤ count1283 b))) else (if i < 1323 then decide (40 ≤ count1283 b) else (if i < 1324 then decide (41 ≤ count1283 b) else decide (42 ≤ count1283 b)))) else (if i < 1328 then (if i < 1326 then decide (1 ≤ count1325 b) else (if i < 1327 then decide (2 ≤ count1325 b) else decide (1 ≤ count1327 b))) else (if i < 1329 then decide (2 ≤ count1327 b) else (if i < 1330 then decide (3 ≤ count1327 b) else decide (1 ≤ count1330 b))))) else (if i < 1337 then (if i < 1334 then (if i < 1332 then decide (2 ≤ count1330 b) else (if i < 1333 then decide (1 ≤ count1332 b) else decide (2 ≤ count1332 b))) else (if i < 1335 then decide (3 ≤ count1332 b) else (if i < 1336 then decide (1 ≤ count1335 b) else decide (2 ≤ count1335 b)))) else (if i < 1340 then (if i < 1338 then decide (3 ≤ count1335 b) else (if i < 1339 then decide (4 ≤ count1335 b) else decide (5 ≤ count1335 b))) else (if i < 1341 then decide (6 ≤ count1335 b) else (if i < 1342 then decide (1 ≤ count1341 b) else decide (2 ≤ count1341 b)))))) else (if i < 1355 then (if i < 1349 then (if i < 1346 then (if i < 1344 then decide (1 ≤ count1343 b) else (if i < 1345 then decide (2 ≤ count1343 b) else decide (3 ≤ count1343 b))) else (if i < 1347 then decide (1 ≤ count1346 b) else (if i < 1348 then decide (2 ≤ count1346 b) else decide (1 ≤ count1348 b)))) else (if i < 1352 then (if i < 1350 then decide (2 ≤ count1348 b) else (if i < 1351 then decide (1 ≤ count1350 b) else decide (2 ≤ count1350 b))) else (if i < 1353 then decide (3 ≤ count1350 b) else (if i < 1354 then decide (4 ≤ count1350 b) else decide (1 ≤ count1354 b))))) else (if i < 1361 then (if i < 1358 then (if i < 1356 then decide (2 ≤ count1354 b) else (if i < 1357 then decide (3 ≤ count1354 b) else decide (4 ≤ count1354 b))) else (if i < 1359 then decide (5 ≤ count1354 b) else (if i < 1360 then decide (6 ≤ count1354 b) else decide (7 ≤ count1354 b)))) else (if i < 1364 then (if i < 1362 then decide (1 ≤ count1361 b) else (if i < 1363 then decide (2 ≤ count1361 b) else decide (3 ≤ count1361 b))) else (if i < 1366 then (if i < 1365 then decide (4 ≤ count1361 b) else decide (5 ≤ count1361 b)) else (if i < 1367 then decide (6 ≤ count1361 b) else decide (7 ≤ count1361 b))))))))) else (if i < 1466 then (if i < 1417 then (if i < 1392 then (if i < 1380 then (if i < 1374 then (if i < 1371 then (if i < 1369 then decide (8 ≤ count1361 b) else (if i < 1370 then decide (9 ≤ count1361 b) else decide (10 ≤ count1361 b))) else (if i < 1372 then decide (11 ≤ count1361 b) else (if i < 1373 then decide (12 ≤ count1361 b) else decide (13 ≤ count1361 b)))) else (if i < 1377 then (if i < 1375 then decide (1 ≤ count1374 b) else (if i < 1376 then decide (2 ≤ count1374 b) else decide (1 ≤ count1376 b))) else (if i < 1378 then decide (2 ≤ count1376 b) else (if i < 1379 then decide (3 ≤ count1376 b) else decide (1 ≤ count1379 b))))) else (if i < 1386 then (if i < 1383 then (if i < 1381 then decide (2 ≤ count1379 b) else (if i < 1382 then decide (1 ≤ count1381 b) else decide (2 ≤ count1381 b))) else (if i < 1384 then decide (3 ≤ count1381 b) else (if i < 1385 then decide (1 ≤ count1384 b) else decide (2 ≤ count1384 b)))) else (if i < 1389 then (if i < 1387 then decide (3 ≤ count1384 b) else (if i < 1388 then decide (4 ≤ count1384 b) else decide (5 ≤ count1384 b))) else (if i < 1390 then decide (6 ≤ count1384 b) else (if i < 1391 then decide (1 ≤ count1390 b) else decide (2 ≤ count1390 b)))))) else (if i < 1404 then (if i < 1398 then (if i < 1395 then (if i < 1393 then decide (1 ≤ count1392 b) else (if i < 1394 then decide (2 ≤ count1392 b) else decide (3 ≤ count1392 b))) else (if i < 1396 then decide (1 ≤ count1395 b) else (if i < 1397 then decide (2 ≤ count1395 b) else decide (1 ≤ count1397 b)))) else (if i < 1401 then (if i < 1399 then decide (2 ≤ count1397 b) else (if i < 1400 then decide (1 ≤ count1399 b) else decide (2 ≤ count1399 b))) else (if i < 1402 then decide (3 ≤ count1399 b) else (if i < 1403 then decide (4 ≤ count1399 b) else decide (1 ≤ count1403 b))))) else (if i < 1410 then (if i < 1407 then (if i < 1405 then decide (2 ≤ count1403 b) else (if i < 1406 then decide (3 ≤ count1403 b) else decide (4 ≤ count1403 b))) else (if i < 1408 then decide (5 ≤ count1403 b) else (if i < 1409 then decide (6 ≤ count1403 b) else decide (7 ≤ count1403 b)))) else (if i < 1413 then (if i < 1411 then decide (1 ≤ count1410 b) else (if i < 1412 then decide (2 ≤ count1410 b) else decide (3 ≤ count1410 b))) else (if i < 1415 then (if i < 1414 then decide (4 ≤ count1410 b) else decide (5 ≤ count1410 b)) else (if i < 1416 then decide (6 ≤ count1410 b) else decide (7 ≤ count1410 b))))))) else (if i < 1441 then (if i < 1429 then (if i < 1423 then (if i < 1420 then (if i < 1418 then decide (8 ≤ count1410 b) else (if i < 1419 then decide (9 ≤ count1410 b) else decide (10 ≤ count1410 b))) else (if i < 1421 then decide (11 ≤ count1410 b) else (if i < 1422 then decide (12 ≤ count1410 b) else decide (13 ≤ count1410 b)))) else (if i < 1426 then (if i < 1424 then decide (1 ≤ count1423 b) else (if i < 1425 then decide (2 ≤ count1423 b) else decide (3 ≤ count1423 b))) else (if i < 1427 then decide (4 ≤ count1423 b) else (if i < 1428 then decide (5 ≤ count1423 b) else decide (6 ≤ count1423 b))))) else (if i < 1435 then (if i < 1432 then (if i < 1430 then decide (7 ≤ count1423 b) else (if i < 1431 then decide (8 ≤ count1423 b) else decide (9 ≤ count1423 b))) else (if i < 1433 then decide (10 ≤ count1423 b) else (if i < 1434 then decide (11 ≤ count1423 b) else decide (12 ≤ count1423 b)))) else (if i < 1438 then (if i < 1436 then decide (13 ≤ count1423 b) else (if i < 1437 then decide (1 ≤ count1436 b) else decide (2 ≤ count1436 b))) else (if i < 1439 then decide (1 ≤ count1438 b) else (if i < 1440 then decide (2 ≤ count1438 b) else decide (3 ≤ count1438 b)))))) else (if i < 1453 then (if i < 1447 then (if i < 1444 then (if i < 1442 then decide (1 ≤ count1441 b) else (if i < 1443 then decide (2 ≤ count1441 b) else decide (1 ≤ count1443 b))) else (if i < 1445 then decide (2 ≤ count1443 b) else (if i < 1446 then decide (3 ≤ count1443 b) else decide (1 ≤ count1446 b)))) else (if i < 1450 then (if i < 1448 then decide (2 ≤ count1446 b) else (if i < 1449 then decide (3 ≤ count1446 b) else decide (4 ≤ count1446 b))) else (if i < 1451 then decide (5 ≤ count1446 b) else (if i < 1452 then decide (6 ≤ count1446 b) else decide (1 ≤ count1452 b))))) else (if i < 1459 then (if i < 1456 then (if i < 1454 then decide (2 ≤ count1452 b) else (if i < 1455 then decide (1 ≤ count1454 b) else decide (2 ≤ count1454 b))) else (if i < 1457 then decide (3 ≤ count1454 b) else (if i < 1458 then decide (1 ≤ count1457 b) else decide (2 ≤ count1457 b)))) else (if i < 1462 then (if i < 1460 then decide (1 ≤ count1459 b) else (if i < 1461 then decide (2 ≤ count1459 b) else decide (1 ≤ count1461 b))) else (if i < 1464 then (if i < 1463 then decide (2 ≤ count1461 b) else decide (3 ≤ count1461 b)) else (if i < 1465 then decide (4 ≤ count1461 b) else decide (1 ≤ count1465 b)))))))) else (if i < 1515 then (if i < 1490 then (if i < 1478 then (if i < 1472 then (if i < 1469 then (if i < 1467 then decide (2 ≤ count1465 b) else (if i < 1468 then decide (3 ≤ count1465 b) else decide (4 ≤ count1465 b))) else (if i < 1470 then decide (5 ≤ count1465 b) else (if i < 1471 then decide (6 ≤ count1465 b) else decide (7 ≤ count1465 b)))) else (if i < 1475 then (if i < 1473 then decide (1 ≤ count1472 b) else (if i < 1474 then decide (2 ≤ count1472 b) else decide (3 ≤ count1472 b))) else (if i < 1476 then decide (4 ≤ count1472 b) else (if i < 1477 then decide (5 ≤ count1472 b) else decide (6 ≤ count1472 b))))) else (if i < 1484 then (if i < 1481 then (if i < 1479 then decide (7 ≤ count1472 b) else (if i < 1480 then decide (8 ≤ count1472 b) else decide (9 ≤ count1472 b))) else (if i < 1482 then decide (10 ≤ count1472 b) else (if i < 1483 then decide (11 ≤ count1472 b) else decide (12 ≤ count1472 b)))) else (if i < 1487 then (if i < 1485 then decide (13 ≤ count1472 b) else (if i < 1486 then decide (1 ≤ count1485 b) else decide (2 ≤ count1485 b))) else (if i < 1488 then decide (1 ≤ count1487 b) else (if i < 1489 then decide (2 ≤ count1487 b) else decide (3 ≤ count1487 b)))))) else (if i < 1502 then (if i < 1496 then (if i < 1493 then (if i < 1491 then decide (1 ≤ count1490 b) else (if i < 1492 then decide (2 ≤ count1490 b) else decide (1 ≤ count1492 b))) else (if i < 1494 then decide (2 ≤ count1492 b) else (if i < 1495 then decide (1 ≤ count1494 b) else decide (2 ≤ count1494 b)))) else (if i < 1499 then (if i < 1497 then decide (3 ≤ count1494 b) else (if i < 1498 then decide (4 ≤ count1494 b) else decide (1 ≤ count1498 b))) else (if i < 1500 then decide (2 ≤ count1498 b) else (if i < 1501 then decide (3 ≤ count1498 b) else decide (4 ≤ count1498 b))))) else (if i < 1508 then (if i < 1505 then (if i < 1503 then decide (5 ≤ count1498 b) else (if i < 1504 then decide (6 ≤ count1498 b) else decide (7 ≤ count1498 b))) else (if i < 1506 then decide (1 ≤ count1505 b) else (if i < 1507 then decide (2 ≤ count1505 b) else decide (1 ≤ count1507 b)))) else (if i < 1511 then (if i < 1509 then decide (2 ≤ count1507 b) else (if i < 1510 then decide (3 ≤ count1507 b) else decide (1 ≤ count1510 b))) else (if i < 1513 then (if i < 1512 then decide (2 ≤ count1510 b) else decide (1 ≤ count1512 b)) else (if i < 1514 then decide (2 ≤ count1512 b) else decide (1 ≤ count1514 b))))))) else (if i < 1539 then (if i < 1527 then (if i < 1521 then (if i < 1518 then (if i < 1516 then decide (2 ≤ count1514 b) else (if i < 1517 then decide (3 ≤ count1514 b) else decide (4 ≤ count1514 b))) else (if i < 1519 then decide (1 ≤ count1518 b) else (if i < 1520 then decide (2 ≤ count1518 b) else decide (3 ≤ count1518 b)))) else (if i < 1524 then (if i < 1522 then decide (4 ≤ count1518 b) else (if i < 1523 then decide (5 ≤ count1518 b) else decide (6 ≤ count1518 b))) else (if i < 1525 then decide (7 ≤ count1518 b) else (if i < 1526 then decide (1 ≤ count1525 b) else decide (2 ≤ count1525 b))))) else (if i < 1533 then (if i < 1530 then (if i < 1528 then decide (3 ≤ count1525 b) else (if i < 1529 then decide (4 ≤ count1525 b) else decide (5 ≤ count1525 b))) else (if i < 1531 then decide (6 ≤ count1525 b) else (if i < 1532 then decide (7 ≤ count1525 b) else decide (8 ≤ count1525 b)))) else (if i < 1536 then (if i < 1534 then decide (9 ≤ count1525 b) else (if i < 1535 then decide (10 ≤ count1525 b) else decide (11 ≤ count1525 b))) else (if i < 1537 then decide (12 ≤ count1525 b) else (if i < 1538 then decide (13 ≤ count1525 b) else decide (1 ≤ count1538 b)))))) else (if i < 1551 then (if i < 1545 then (if i < 1542 then (if i < 1540 then decide (2 ≤ count1538 b) else (if i < 1541 then decide (3 ≤ count1538 b) else decide (4 ≤ count1538 b))) else (if i < 1543 then decide (5 ≤ count1538 b) else (if i < 1544 then decide (6 ≤ count1538 b) else decide (7 ≤ count1538 b)))) else (if i < 1548 then (if i < 1546 then decide (8 ≤ count1538 b) else (if i < 1547 then decide (9 ≤ count1538 b) else decide (10 ≤ count1538 b))) else (if i < 1549 then decide (11 ≤ count1538 b) else (if i < 1550 then decide (12 ≤ count1538 b) else decide (13 ≤ count1538 b))))) else (if i < 1557 then (if i < 1554 then (if i < 1552 then decide (1 ≤ count1551 b) else (if i < 1553 then decide (2 ≤ count1551 b) else decide (3 ≤ count1551 b))) else (if i < 1555 then decide (4 ≤ count1551 b) else (if i < 1556 then decide (5 ≤ count1551 b) else decide (6 ≤ count1551 b)))) else (if i < 1560 then (if i < 1558 then decide (7 ≤ count1551 b) else (if i < 1559 then decide (8 ≤ count1551 b) else decide (9 ≤ count1551 b))) else (if i < 1562 then (if i < 1561 then decide (10 ≤ count1551 b) else decide (11 ≤ count1551 b)) else (if i < 1563 then decide (12 ≤ count1551 b) else decide (13 ≤ count1551 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (5 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (9 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (13 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (15 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (16 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (17 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (18 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (22 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (26 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (28 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (29 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (30 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (161 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (167 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (173 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (175 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (177 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (178 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (179 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (182 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (186 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (188 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (189 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (190 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (192 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (193 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (198 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (199 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (200 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (201 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (205 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (207 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (210 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (211 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (214 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (218 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (220 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (221 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (256 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (258 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (260 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (262 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (263 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (264 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (265 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (266 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (268 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (270 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (272 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (276 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (277 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (279 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (281 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (282 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (283 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (285 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (287 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (320 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (321 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (325 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (326 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (327 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (328 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (329 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (333 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (335 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (337 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (338 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (339 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (342 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (346 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (348 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (349 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (350 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (416 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (418 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (420 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (422 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (423 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (425 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (426 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (428 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (430 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (436 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (437 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (439 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (441 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (442 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (443 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (445 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (447 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (454 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (456 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (460 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (462 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (486 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (488 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (489 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (493 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (502 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (506 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (508 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (509 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (510 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (5 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (9 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (16 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (26 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (30 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (167 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (177 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (178 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (188 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (190 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (329 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (418 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (428 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (437 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (439 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (447 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (2 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value260 (q : Snake 81) : valuation q 260 = decide (2 ≤ count259 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value268 (q : Snake 81) : valuation q 268 = decide (2 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value294 (q : Snake 81) : valuation q 294 = decide (2 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value320 (q : Snake 81) : valuation q 320 = decide (2 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value322 (q : Snake 81) : valuation q 322 = decide (2 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value326 (q : Snake 81) : valuation q 326 = decide (2 ≤ count325 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value336 (q : Snake 81) : valuation q 336 = decide (2 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value350 (q : Snake 81) : valuation q 350 = decide (2 ≤ count349 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value422 (q : Snake 81) : valuation q 422 = decide (2 ≤ count421 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value426 (q : Snake 81) : valuation q 426 = decide (2 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value430 (q : Snake 81) : valuation q 430 = decide (2 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value432 (q : Snake 81) : valuation q 432 = decide (2 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value1325 (q : Snake 81) : valuation q 1325 = decide (1 ≤ count1325 (baseVal q)) := rfl
theorem value1326 (q : Snake 81) : valuation q 1326 = decide (2 ≤ count1325 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (1 ≤ count1327 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (2 ≤ count1327 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (3 ≤ count1327 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (1 ≤ count1330 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (2 ≤ count1330 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (1 ≤ count1332 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (2 ≤ count1332 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (3 ≤ count1332 (baseVal q)) := rfl
theorem value1335 (q : Snake 81) : valuation q 1335 = decide (1 ≤ count1335 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (2 ≤ count1335 (baseVal q)) := rfl
theorem value1337 (q : Snake 81) : valuation q 1337 = decide (3 ≤ count1335 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (4 ≤ count1335 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (1 ≤ count1341 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (2 ≤ count1341 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (1 ≤ count1343 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (2 ≤ count1343 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (3 ≤ count1343 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (1 ≤ count1346 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (2 ≤ count1346 (baseVal q)) := rfl
theorem value1348 (q : Snake 81) : valuation q 1348 = decide (1 ≤ count1348 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (2 ≤ count1348 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (1 ≤ count1350 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (2 ≤ count1350 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (3 ≤ count1350 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (1 ≤ count1354 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (2 ≤ count1354 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (3 ≤ count1354 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (4 ≤ count1354 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (1 ≤ count1361 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (2 ≤ count1361 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (3 ≤ count1361 (baseVal q)) := rfl
theorem value1364 (q : Snake 81) : valuation q 1364 = decide (4 ≤ count1361 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (5 ≤ count1361 (baseVal q)) := rfl
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (6 ≤ count1361 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (7 ≤ count1361 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (1 ≤ count1374 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (2 ≤ count1374 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (1 ≤ count1376 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (2 ≤ count1376 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (1 ≤ count1379 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (1 ≤ count1381 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (1 ≤ count1384 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (2 ≤ count1384 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (3 ≤ count1384 (baseVal q)) := rfl
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
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (4 ≤ count1399 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (1 ≤ count1403 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (2 ≤ count1403 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (3 ≤ count1403 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (4 ≤ count1403 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (1 ≤ count1410 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (2 ≤ count1410 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (3 ≤ count1410 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (4 ≤ count1410 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (5 ≤ count1410 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (4 ≤ count1423 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (5 ≤ count1423 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (6 ≤ count1423 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (7 ≤ count1423 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (8 ≤ count1423 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (9 ≤ count1423 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (10 ≤ count1423 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (1 ≤ count1436 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (2 ≤ count1436 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (1 ≤ count1438 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (2 ≤ count1438 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (3 ≤ count1438 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (1 ≤ count1441 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (2 ≤ count1441 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (1 ≤ count1443 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (2 ≤ count1443 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (1 ≤ count1446 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (2 ≤ count1446 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (3 ≤ count1446 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (2 ≤ count1452 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (1 ≤ count1454 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (2 ≤ count1454 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (3 ≤ count1454 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (1 ≤ count1457 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (2 ≤ count1457 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (1 ≤ count1459 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (2 ≤ count1459 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (1 ≤ count1461 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (2 ≤ count1461 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (3 ≤ count1461 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (4 ≤ count1461 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (1 ≤ count1465 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (2 ≤ count1465 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (3 ≤ count1465 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (4 ≤ count1465 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (5 ≤ count1465 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (1 ≤ count1472 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (2 ≤ count1472 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (3 ≤ count1472 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (4 ≤ count1472 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (5 ≤ count1472 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (6 ≤ count1472 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (1 ≤ count1485 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (1 ≤ count1487 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (2 ≤ count1487 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (1 ≤ count1490 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (2 ≤ count1490 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (1 ≤ count1492 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (2 ≤ count1492 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (1 ≤ count1494 (baseVal q)) := rfl
theorem value1495 (q : Snake 81) : valuation q 1495 = decide (2 ≤ count1494 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (3 ≤ count1494 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (1 ≤ count1498 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (2 ≤ count1498 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (3 ≤ count1498 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (4 ≤ count1498 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (1 ≤ count1505 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (2 ≤ count1505 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (1 ≤ count1507 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (2 ≤ count1507 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (3 ≤ count1507 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (1 ≤ count1510 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (2 ≤ count1510 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (1 ≤ count1512 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (1 ≤ count1514 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (2 ≤ count1514 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (1 ≤ count1518 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (2 ≤ count1518 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (3 ≤ count1518 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (4 ≤ count1518 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (2 ≤ count1525 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (3 ≤ count1525 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (4 ≤ count1525 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (5 ≤ count1525 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (6 ≤ count1525 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (3 ≤ count1538 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (4 ≤ count1538 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (5 ≤ count1538 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (6 ≤ count1538 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (7 ≤ count1538 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (8 ≤ count1538 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (9 ≤ count1538 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (13 ≤ count1551 (baseVal q)) := rfl
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
theorem meaningNeg104 (b : Nat → Bool) : literal (valuationOf b) (-104) = decide (1 ≤ countLit b [-104]) := by
  change literal b (-104) = decide (1 ≤ countLit b [-104])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-104) <;> decide
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
theorem meaningNeg76 (b : Nat → Bool) : literal (valuationOf b) (-76) = decide (1 ≤ countLit b [-76]) := by
  change literal b (-76) = decide (1 ≤ countLit b [-76])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-76) <;> decide
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
theorem meaningNeg66 (b : Nat → Bool) : literal (valuationOf b) (-66) = decide (1 ≤ countLit b [-66]) := by
  change literal b (-66) = decide (1 ≤ countLit b [-66])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-66) <;> decide
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
theorem meaningNeg46 (b : Nat → Bool) : literal (valuationOf b) (-46) = decide (1 ≤ countLit b [-46]) := by
  change literal b (-46) = decide (1 ≤ countLit b [-46])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-46) <;> decide
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
theorem meaningNeg6 (b : Nat → Bool) : literal (valuationOf b) (-6) = decide (1 ≤ countLit b [-6]) := by
  change literal b (-6) = decide (1 ≤ countLit b [-6])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-6) <;> decide
theorem meaningNeg4 (b : Nat → Bool) : literal (valuationOf b) (-4) = decide (1 ≤ countLit b [-4]) := by
  change literal b (-4) = decide (1 ≤ countLit b [-4])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-4) <;> decide
theorem meaning114 (b : Nat → Bool) : literal (valuationOf b) (114) = decide (1 ≤ countLit b [114]) := by
  change literal b (114) = decide (1 ≤ countLit b [114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (114) <;> decide
theorem meaning116 (b : Nat → Bool) : literal (valuationOf b) (116) = decide (1 ≤ countLit b [116]) := by
  change literal b (116) = decide (1 ≤ countLit b [116])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (116) <;> decide
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
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
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
theorem meaning131 (b : Nat → Bool) : literal (valuationOf b) (131) = decide (1 ≤ countLit b [131]) := by
  change literal b (131) = decide (1 ≤ countLit b [131])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (131) <;> decide
theorem meaning132 (b : Nat → Bool) : literal (valuationOf b) (132) = decide (1 ≤ countLit b [132]) := by
  change literal b (132) = decide (1 ≤ countLit b [132])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (132) <;> decide
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
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
theorem meaning140 (b : Nat → Bool) : literal (valuationOf b) (140) = decide (1 ≤ countLit b [140]) := by
  change literal b (140) = decide (1 ≤ countLit b [140])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (140) <;> decide
theorem meaning141 (b : Nat → Bool) : literal (valuationOf b) (141) = decide (1 ≤ countLit b [141]) := by
  change literal b (141) = decide (1 ≤ countLit b [141])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (141) <;> decide
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
theorem meaning150 (b : Nat → Bool) : literal (valuationOf b) (150) = decide (1 ≤ countLit b [150]) := by
  change literal b (150) = decide (1 ≤ countLit b [150])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (150) <;> decide
theorem meaning159 (b : Nat → Bool) : literal (valuationOf b) (159) = decide (1 ≤ countLit b [159]) := by
  change literal b (159) = decide (1 ≤ countLit b [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (159) <;> decide
theorem meaning160 (b : Nat → Bool) : literal (valuationOf b) (160) = decide (1 ≤ countLit b [160]) := by
  change literal b (160) = decide (1 ≤ countLit b [160])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (160) <;> decide
theorem meaning161 (b : Nat → Bool) : literal (valuationOf b) (161) = decide (1 ≤ countLit b [161]) := by
  change literal b (161) = decide (1 ≤ countLit b [161])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (161) <;> decide
theorem meaning164 (b : Nat → Bool) : literal (valuationOf b) (164) = decide (1 ≤ countLit b [164]) := by
  change literal b (164) = decide (1 ≤ countLit b [164])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (164) <;> decide
theorem meaning166 (b : Nat → Bool) : literal (valuationOf b) (166) = decide (1 ≤ countLit b [166]) := by
  change literal b (166) = decide (1 ≤ countLit b [166])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (166) <;> decide
theorem meaning169 (b : Nat → Bool) : literal (valuationOf b) (169) = decide (1 ≤ countLit b [169]) := by
  change literal b (169) = decide (1 ≤ countLit b [169])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (169) <;> decide
theorem meaning173 (b : Nat → Bool) : literal (valuationOf b) (173) = decide (1 ≤ countLit b [173]) := by
  change literal b (173) = decide (1 ≤ countLit b [173])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (173) <;> decide
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
theorem meaning179 (b : Nat → Bool) : literal (valuationOf b) (179) = decide (1 ≤ countLit b [179]) := by
  change literal b (179) = decide (1 ≤ countLit b [179])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (179) <;> decide
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
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
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
theorem meaning196 (b : Nat → Bool) : literal (valuationOf b) (196) = decide (1 ≤ countLit b [196]) := by
  change literal b (196) = decide (1 ≤ countLit b [196])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (196) <;> decide
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
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning212 (b : Nat → Bool) : literal (valuationOf b) (212) = decide (1 ≤ countLit b [212]) := by
  change literal b (212) = decide (1 ≤ countLit b [212])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (212) <;> decide
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning217 (b : Nat → Bool) : literal (valuationOf b) (217) = decide (1 ≤ countLit b [217]) := by
  change literal b (217) = decide (1 ≤ countLit b [217])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (217) <;> decide
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) (218) = decide (1 ≤ countLit b [218]) := by
  change literal b (218) = decide (1 ≤ countLit b [218])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (218) <;> decide
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) 244 = decide (2 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning260 (b : Nat → Bool) : literal (valuationOf b) 260 = decide (2 ≤ count259 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning268 (b : Nat → Bool) : literal (valuationOf b) 268 = decide (2 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning294 (b : Nat → Bool) : literal (valuationOf b) 294 = decide (2 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning320 (b : Nat → Bool) : literal (valuationOf b) 320 = decide (2 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning322 (b : Nat → Bool) : literal (valuationOf b) 322 = decide (2 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning326 (b : Nat → Bool) : literal (valuationOf b) 326 = decide (2 ≤ count325 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning336 (b : Nat → Bool) : literal (valuationOf b) 336 = decide (2 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning350 (b : Nat → Bool) : literal (valuationOf b) 350 = decide (2 ≤ count349 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning422 (b : Nat → Bool) : literal (valuationOf b) 422 = decide (2 ≤ count421 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning426 (b : Nat → Bool) : literal (valuationOf b) 426 = decide (2 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning430 (b : Nat → Bool) : literal (valuationOf b) 430 = decide (2 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning432 (b : Nat → Bool) : literal (valuationOf b) 432 = decide (2 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning1325 (b : Nat → Bool) : literal (valuationOf b) 1325 = decide (1 ≤ count1325 b) := rfl
theorem meaning1326 (b : Nat → Bool) : literal (valuationOf b) 1326 = decide (2 ≤ count1325 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (1 ≤ count1327 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (2 ≤ count1327 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (3 ≤ count1327 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (1 ≤ count1330 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (2 ≤ count1330 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (1 ≤ count1332 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (2 ≤ count1332 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (3 ≤ count1332 b) := rfl
theorem meaning1335 (b : Nat → Bool) : literal (valuationOf b) 1335 = decide (1 ≤ count1335 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (2 ≤ count1335 b) := rfl
theorem meaning1337 (b : Nat → Bool) : literal (valuationOf b) 1337 = decide (3 ≤ count1335 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (4 ≤ count1335 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (1 ≤ count1341 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (2 ≤ count1341 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (1 ≤ count1343 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (2 ≤ count1343 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (3 ≤ count1343 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (1 ≤ count1346 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (2 ≤ count1346 b) := rfl
theorem meaning1348 (b : Nat → Bool) : literal (valuationOf b) 1348 = decide (1 ≤ count1348 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (2 ≤ count1348 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (1 ≤ count1350 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (2 ≤ count1350 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (3 ≤ count1350 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (1 ≤ count1354 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (2 ≤ count1354 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (3 ≤ count1354 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (4 ≤ count1354 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (1 ≤ count1361 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (2 ≤ count1361 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (3 ≤ count1361 b) := rfl
theorem meaning1364 (b : Nat → Bool) : literal (valuationOf b) 1364 = decide (4 ≤ count1361 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (5 ≤ count1361 b) := rfl
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (6 ≤ count1361 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (7 ≤ count1361 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (1 ≤ count1374 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (2 ≤ count1374 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (1 ≤ count1376 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (2 ≤ count1376 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (1 ≤ count1379 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (1 ≤ count1381 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (1 ≤ count1384 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (2 ≤ count1384 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (3 ≤ count1384 b) := rfl
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
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (4 ≤ count1399 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (1 ≤ count1403 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (2 ≤ count1403 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (3 ≤ count1403 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (4 ≤ count1403 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (1 ≤ count1410 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (2 ≤ count1410 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (3 ≤ count1410 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (4 ≤ count1410 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (5 ≤ count1410 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (4 ≤ count1423 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (5 ≤ count1423 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (6 ≤ count1423 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (7 ≤ count1423 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (8 ≤ count1423 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (9 ≤ count1423 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (10 ≤ count1423 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (1 ≤ count1436 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (2 ≤ count1436 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (1 ≤ count1438 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (2 ≤ count1438 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (3 ≤ count1438 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (1 ≤ count1441 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (2 ≤ count1441 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (1 ≤ count1443 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (2 ≤ count1443 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (1 ≤ count1446 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (2 ≤ count1446 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (3 ≤ count1446 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (2 ≤ count1452 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (1 ≤ count1454 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (2 ≤ count1454 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (3 ≤ count1454 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (1 ≤ count1457 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (2 ≤ count1457 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (1 ≤ count1459 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (2 ≤ count1459 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (1 ≤ count1461 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (2 ≤ count1461 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (3 ≤ count1461 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (4 ≤ count1461 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (1 ≤ count1465 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (2 ≤ count1465 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (3 ≤ count1465 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (4 ≤ count1465 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (5 ≤ count1465 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (1 ≤ count1472 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (2 ≤ count1472 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (3 ≤ count1472 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (4 ≤ count1472 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (5 ≤ count1472 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (6 ≤ count1472 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (1 ≤ count1485 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (2 ≤ count1485 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (1 ≤ count1487 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (2 ≤ count1487 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (1 ≤ count1490 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (2 ≤ count1490 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (1 ≤ count1492 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (2 ≤ count1492 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (1 ≤ count1494 b) := rfl
theorem meaning1495 (b : Nat → Bool) : literal (valuationOf b) 1495 = decide (2 ≤ count1494 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (3 ≤ count1494 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (1 ≤ count1498 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (2 ≤ count1498 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (3 ≤ count1498 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (4 ≤ count1498 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (1 ≤ count1505 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (2 ≤ count1505 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (1 ≤ count1507 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (2 ≤ count1507 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (3 ≤ count1507 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (1 ≤ count1510 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (2 ≤ count1510 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (1 ≤ count1512 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (1 ≤ count1514 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (2 ≤ count1514 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (1 ≤ count1518 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (2 ≤ count1518 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (3 ≤ count1518 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (4 ≤ count1518 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (2 ≤ count1525 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (3 ≤ count1525 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (4 ≤ count1525 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (5 ≤ count1525 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (6 ≤ count1525 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (3 ≤ count1538 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (4 ≤ count1538 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (5 ≤ count1538 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (6 ≤ count1538 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (7 ≤ count1538 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (8 ≤ count1538 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (9 ≤ count1538 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (13 ≤ count1551 b) := rfl
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
end Snake9.Regrowth.E112107
