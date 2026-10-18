import E112183Data
namespace Snake9.Regrowth.E112183
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 110 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 4 then decide (InPath q (2 : Vertex)) else (if i < 5 then decide (InPath q (3 : Vertex)) else decide (InPath q (5 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (6 : Vertex)) else (if i < 8 then decide (InPath q (11 : Vertex)) else decide (InPath q (13 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (15 : Vertex)) else decide (InPath q (16 : Vertex))) else (if i < 12 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (19 : Vertex)) else (if i < 15 then decide (InPath q (22 : Vertex)) else decide (InPath q (24 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex))) else (if i < 19 then decide (InPath q (30 : Vertex)) else decide (InPath q (31 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (66 : Vertex)) else (if i < 22 then decide (InPath q (67 : Vertex)) else decide (InPath q (68 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (69 : Vertex)) else decide (InPath q (74 : Vertex))) else (if i < 26 then decide (InPath q (75 : Vertex)) else decide (InPath q (76 : Vertex))))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then decide (InPath q (78 : Vertex)) else (if i < 29 then decide (InPath q (80 : Vertex)) else decide (InPath q (84 : Vertex)))) else (if i < 32 then (if i < 31 then decide (InPath q (85 : Vertex)) else decide (InPath q (87 : Vertex))) else (if i < 33 then decide (InPath q (88 : Vertex)) else decide (InPath q (89 : Vertex))))) else (if i < 37 then (if i < 35 then decide (InPath q (90 : Vertex)) else (if i < 36 then decide (InPath q (91 : Vertex)) else decide (InPath q (95 : Vertex)))) else (if i < 39 then (if i < 38 then decide (InPath q (160 : Vertex)) else decide (InPath q (161 : Vertex))) else (if i < 40 then decide (InPath q (165 : Vertex)) else decide (InPath q (171 : Vertex)))))) else (if i < 48 then (if i < 44 then (if i < 42 then decide (InPath q (173 : Vertex)) else (if i < 43 then decide (InPath q (175 : Vertex)) else decide (InPath q (176 : Vertex)))) else (if i < 46 then (if i < 45 then decide (InPath q (177 : Vertex)) else decide (InPath q (178 : Vertex))) else (if i < 47 then decide (InPath q (179 : Vertex)) else decide (InPath q (182 : Vertex))))) else (if i < 51 then (if i < 49 then decide (InPath q (184 : Vertex)) else (if i < 50 then decide (InPath q (188 : Vertex)) else decide (InPath q (189 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (190 : Vertex)) else decide (InPath q (192 : Vertex))) else (if i < 54 then decide (InPath q (195 : Vertex)) else decide (InPath q (208 : Vertex)))))))) else (if i < 82 then (if i < 68 then (if i < 61 then (if i < 58 then (if i < 56 then decide (InPath q (209 : Vertex)) else (if i < 57 then decide (InPath q (211 : Vertex)) else decide (InPath q (227 : Vertex)))) else (if i < 59 then decide (InPath q (229 : Vertex)) else (if i < 60 then decide (InPath q (235 : Vertex)) else decide (InPath q (240 : Vertex))))) else (if i < 64 then (if i < 62 then decide (InPath q (244 : Vertex)) else (if i < 63 then decide (InPath q (245 : Vertex)) else decide (InPath q (247 : Vertex)))) else (if i < 66 then (if i < 65 then decide (InPath q (249 : Vertex)) else decide (InPath q (251 : Vertex))) else (if i < 67 then decide (InPath q (255 : Vertex)) else decide (InPath q (258 : Vertex)))))) else (if i < 75 then (if i < 71 then (if i < 69 then decide (InPath q (261 : Vertex)) else (if i < 70 then decide (InPath q (262 : Vertex)) else decide (InPath q (267 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (276 : Vertex)) else decide (InPath q (277 : Vertex))) else (if i < 74 then decide (InPath q (279 : Vertex)) else decide (InPath q (281 : Vertex))))) else (if i < 78 then (if i < 76 then decide (InPath q (282 : Vertex)) else (if i < 77 then decide (InPath q (283 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 80 then (if i < 79 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex))) else (if i < 81 then decide (InPath q (326 : Vertex)) else decide (InPath q (327 : Vertex))))))) else (if i < 96 then (if i < 89 then (if i < 85 then (if i < 83 then decide (InPath q (329 : Vertex)) else (if i < 84 then decide (InPath q (331 : Vertex)) else decide (InPath q (333 : Vertex)))) else (if i < 87 then (if i < 86 then decide (InPath q (335 : Vertex)) else decide (InPath q (337 : Vertex))) else (if i < 88 then decide (InPath q (338 : Vertex)) else decide (InPath q (339 : Vertex))))) else (if i < 92 then (if i < 90 then decide (InPath q (340 : Vertex)) else (if i < 91 then decide (InPath q (342 : Vertex)) else decide (InPath q (346 : Vertex)))) else (if i < 94 then (if i < 93 then decide (InPath q (348 : Vertex)) else decide (InPath q (349 : Vertex))) else (if i < 95 then decide (InPath q (350 : Vertex)) else decide (InPath q (450 : Vertex)))))) else (if i < 103 then (if i < 99 then (if i < 97 then decide (InPath q (451 : Vertex)) else (if i < 98 then decide (InPath q (452 : Vertex)) else decide (InPath q (453 : Vertex)))) else (if i < 101 then (if i < 100 then decide (InPath q (458 : Vertex)) else decide (InPath q (459 : Vertex))) else (if i < 102 then decide (InPath q (460 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 106 then (if i < 104 then decide (InPath q (464 : Vertex)) else (if i < 105 then decide (InPath q (468 : Vertex)) else decide (InPath q (469 : Vertex)))) else (if i < 108 then (if i < 107 then decide (InPath q (471 : Vertex)) else decide (InPath q (472 : Vertex))) else (if i < 109 then decide (InPath q (473 : Vertex)) else decide (InPath q (475 : Vertex))))))))) else (if i < 165 then (if i < 137 then (if i < 123 then (if i < 116 then (if i < 113 then (if i < 111 then decide (InPath q (479 : Vertex)) else (if i < 112 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 114 then decide (BallClauseLogic.Endpoint q (2 : Vertex)) else (if i < 115 then decide (BallClauseLogic.Endpoint q (3 : Vertex)) else decide (BallClauseLogic.Endpoint q (5 : Vertex))))) else (if i < 119 then (if i < 117 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else (if i < 118 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else decide (BallClauseLogic.Endpoint q (13 : Vertex)))) else (if i < 121 then (if i < 120 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else decide (BallClauseLogic.Endpoint q (16 : Vertex))) else (if i < 122 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex)))))) else (if i < 130 then (if i < 126 then (if i < 124 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else (if i < 125 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (24 : Vertex)))) else (if i < 128 then (if i < 127 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex))) else (if i < 129 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else decide (BallClauseLogic.Endpoint q (31 : Vertex))))) else (if i < 133 then (if i < 131 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else (if i < 132 then decide (BallClauseLogic.Endpoint q (67 : Vertex)) else decide (BallClauseLogic.Endpoint q (68 : Vertex)))) else (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else decide (BallClauseLogic.Endpoint q (74 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (75 : Vertex)) else decide (BallClauseLogic.Endpoint q (76 : Vertex))))))) else (if i < 151 then (if i < 144 then (if i < 140 then (if i < 138 then decide (BallClauseLogic.Endpoint q (78 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else decide (BallClauseLogic.Endpoint q (84 : Vertex)))) else (if i < 142 then (if i < 141 then decide (BallClauseLogic.Endpoint q (85 : Vertex)) else decide (BallClauseLogic.Endpoint q (87 : Vertex))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (88 : Vertex)) else decide (BallClauseLogic.Endpoint q (89 : Vertex))))) else (if i < 147 then (if i < 145 then decide (BallClauseLogic.Endpoint q (90 : Vertex)) else (if i < 146 then decide (BallClauseLogic.Endpoint q (91 : Vertex)) else decide (BallClauseLogic.Endpoint q (95 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (160 : Vertex)) else decide (BallClauseLogic.Endpoint q (161 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (165 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex)))))) else (if i < 158 then (if i < 154 then (if i < 152 then decide (BallClauseLogic.Endpoint q (173 : Vertex)) else (if i < 153 then decide (BallClauseLogic.Endpoint q (175 : Vertex)) else decide (BallClauseLogic.Endpoint q (176 : Vertex)))) else (if i < 156 then (if i < 155 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else decide (BallClauseLogic.Endpoint q (178 : Vertex))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (179 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex))))) else (if i < 161 then (if i < 159 then decide (BallClauseLogic.Endpoint q (184 : Vertex)) else (if i < 160 then decide (BallClauseLogic.Endpoint q (188 : Vertex)) else decide (BallClauseLogic.Endpoint q (189 : Vertex)))) else (if i < 163 then (if i < 162 then decide (BallClauseLogic.Endpoint q (190 : Vertex)) else decide (BallClauseLogic.Endpoint q (192 : Vertex))) else (if i < 164 then decide (BallClauseLogic.Endpoint q (195 : Vertex)) else decide (BallClauseLogic.Endpoint q (208 : Vertex)))))))) else (if i < 193 then (if i < 179 then (if i < 172 then (if i < 168 then (if i < 166 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else (if i < 167 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else decide (BallClauseLogic.Endpoint q (227 : Vertex)))) else (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (235 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (240 : Vertex)) else decide (BallClauseLogic.Endpoint q (244 : Vertex))))) else (if i < 175 then (if i < 173 then decide (BallClauseLogic.Endpoint q (245 : Vertex)) else (if i < 174 then decide (BallClauseLogic.Endpoint q (247 : Vertex)) else decide (BallClauseLogic.Endpoint q (249 : Vertex)))) else (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (251 : Vertex)) else decide (BallClauseLogic.Endpoint q (255 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex)))))) else (if i < 186 then (if i < 182 then (if i < 180 then decide (BallClauseLogic.Endpoint q (262 : Vertex)) else (if i < 181 then decide (BallClauseLogic.Endpoint q (267 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else decide (BallClauseLogic.Endpoint q (279 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex))))) else (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex)))) else (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (329 : Vertex))))))) else (if i < 207 then (if i < 200 then (if i < 196 then (if i < 194 then decide (BallClauseLogic.Endpoint q (331 : Vertex)) else (if i < 195 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (335 : Vertex)))) else (if i < 198 then (if i < 197 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (338 : Vertex))) else (if i < 199 then decide (BallClauseLogic.Endpoint q (339 : Vertex)) else decide (BallClauseLogic.Endpoint q (340 : Vertex))))) else (if i < 203 then (if i < 201 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else (if i < 202 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else decide (BallClauseLogic.Endpoint q (348 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (450 : Vertex)) else decide (BallClauseLogic.Endpoint q (451 : Vertex)))))) else (if i < 214 then (if i < 210 then (if i < 208 then decide (BallClauseLogic.Endpoint q (452 : Vertex)) else (if i < 209 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else decide (BallClauseLogic.Endpoint q (458 : Vertex)))) else (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (459 : Vertex)) else decide (BallClauseLogic.Endpoint q (460 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 217 then (if i < 215 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else (if i < 216 then decide (BallClauseLogic.Endpoint q (469 : Vertex)) else decide (BallClauseLogic.Endpoint q (471 : Vertex)))) else (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
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
def count245 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [124, 125, 126]
def count249 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count265 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143]
def count283 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [144, 145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count291 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]
def count297 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [151, 152, 153]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count305 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154, 155, 156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160, 161]
def count313 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count315 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163, 164, 165]
def count319 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165]
def count321 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]
def count325 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165]
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
def count435 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220]
def count437 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count439 (b : Nat → Bool) : Nat := countLit b [1, 4, 5]
def count442 (b : Nat → Bool) : Nat := countLit b [6, 9]
def count444 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count446 (b : Nat → Bool) : Nat := countLit b [6, 9, 11, 12]
def count450 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12]
def count457 (b : Nat → Bool) : Nat := countLit b [17, 18]
def count459 (b : Nat → Bool) : Nat := countLit b [15, 17, 18]
def count462 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count464 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count466 (b : Nat → Bool) : Nat := countLit b [20, 22, 25, 27]
def count470 (b : Nat → Bool) : Nat := countLit b [15, 17, 18, 20, 22, 25, 27]
def count477 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12, 15, 17, 18, 20, 22, 25, 27]
def count491 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count493 (b : Nat → Bool) : Nat := countLit b [28, 30, 33]
def count496 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count498 (b : Nat → Bool) : Nat := countLit b [37, 39]
def count500 (b : Nat → Bool) : Nat := countLit b [34, 36, 37, 39]
def count504 (b : Nat → Bool) : Nat := countLit b [28, 30, 33, 34, 36, 37, 39]
def count511 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count513 (b : Nat → Bool) : Nat := countLit b [45, 48]
def count515 (b : Nat → Bool) : Nat := countLit b [42, 44, 45, 48]
def count519 (b : Nat → Bool) : Nat := countLit b [50, 51]
def count521 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count523 (b : Nat → Bool) : Nat := countLit b [50, 51, 52, 53]
def count527 (b : Nat → Bool) : Nat := countLit b [42, 44, 45, 48, 50, 51, 52, 53]
def count535 (b : Nat → Bool) : Nat := countLit b [28, 30, 33, 34, 36, 37, 39, 42, 44, 45, 48, 50, 51, 52, 53]
def count550 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12, 15, 17, 18, 20, 22, 25, 27, 28, 30, 33, 34, 36, 37, 39, 42, 44, 45, 48, 50, 51, 52, 53]
def count579 (b : Nat → Bool) : Nat := countLit b [59, 60]
def count581 (b : Nat → Bool) : Nat := countLit b [55, 59, 60]
def count584 (b : Nat → Bool) : Nat := countLit b [62, 64]
def count586 (b : Nat → Bool) : Nat := countLit b [66, 67]
def count588 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 67]
def count592 (b : Nat → Bool) : Nat := countLit b [55, 59, 60, 62, 64, 66, 67]
def count599 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count601 (b : Nat → Bool) : Nat := countLit b [70, 72, 74]
def count604 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count606 (b : Nat → Bool) : Nat := countLit b [78, 80]
def count608 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 80]
def count612 (b : Nat → Bool) : Nat := countLit b [70, 72, 74, 75, 77, 78, 80]
def count619 (b : Nat → Bool) : Nat := countLit b [55, 59, 60, 62, 64, 66, 67, 70, 72, 74, 75, 77, 78, 80]
def count633 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count635 (b : Nat → Bool) : Nat := countLit b [82, 85, 86]
def count638 (b : Nat → Bool) : Nat := countLit b [87, 89]
def count640 (b : Nat → Bool) : Nat := countLit b [93, 94]
def count642 (b : Nat → Bool) : Nat := countLit b [87, 89, 93, 94]
def count646 (b : Nat → Bool) : Nat := countLit b [82, 85, 86, 87, 89, 93, 94]
def count653 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count655 (b : Nat → Bool) : Nat := countLit b [100, 102]
def count657 (b : Nat → Bool) : Nat := countLit b [95, 97, 100, 102]
def count661 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count663 (b : Nat → Bool) : Nat := countLit b [108, 110]
def count665 (b : Nat → Bool) : Nat := countLit b [103, 105, 108, 110]
def count669 (b : Nat → Bool) : Nat := countLit b [95, 97, 100, 102, 103, 105, 108, 110]
def count677 (b : Nat → Bool) : Nat := countLit b [82, 85, 86, 87, 89, 93, 94, 95, 97, 100, 102, 103, 105, 108, 110]
def count692 (b : Nat → Bool) : Nat := countLit b [55, 59, 60, 62, 64, 66, 67, 70, 72, 74, 75, 77, 78, 80, 82, 85, 86, 87, 89, 93, 94, 95, 97, 100, 102, 103, 105, 108, 110]
def count721 (b : Nat → Bool) : Nat := countLit b [1, 4, 5, 6, 9, 11, 12, 15, 17, 18, 20, 22, 25, 27, 28, 30, 33, 34, 36, 37, 39, 42, 44, 45, 48, 50, 51, 52, 53, 55, 59, 60, 62, 64, 66, 67, 70, 72, 74, 75, 77, 78, 80, 82, 85, 86, 87, 89, 93, 94, 95, 97, 100, 102, 103, 105, 108, 110]
def count763 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count765 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5]
def count768 (b : Nat → Bool) : Nat := countLit b [-6, -9]
def count770 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count772 (b : Nat → Bool) : Nat := countLit b [-6, -9, -11, -12]
def count776 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12]
def count783 (b : Nat → Bool) : Nat := countLit b [-17, -18]
def count785 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18]
def count788 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count790 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count792 (b : Nat → Bool) : Nat := countLit b [-20, -22, -25, -27]
def count796 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18, -20, -22, -25, -27]
def count803 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -22, -25, -27]
def count817 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count819 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33]
def count822 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count824 (b : Nat → Bool) : Nat := countLit b [-37, -39]
def count826 (b : Nat → Bool) : Nat := countLit b [-34, -36, -37, -39]
def count830 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33, -34, -36, -37, -39]
def count837 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count839 (b : Nat → Bool) : Nat := countLit b [-45, -48]
def count841 (b : Nat → Bool) : Nat := countLit b [-42, -44, -45, -48]
def count845 (b : Nat → Bool) : Nat := countLit b [-50, -51]
def count847 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count849 (b : Nat → Bool) : Nat := countLit b [-50, -51, -52, -53]
def count853 (b : Nat → Bool) : Nat := countLit b [-42, -44, -45, -48, -50, -51, -52, -53]
def count861 (b : Nat → Bool) : Nat := countLit b [-28, -30, -33, -34, -36, -37, -39, -42, -44, -45, -48, -50, -51, -52, -53]
def count876 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -22, -25, -27, -28, -30, -33, -34, -36, -37, -39, -42, -44, -45, -48, -50, -51, -52, -53]
def count894 (b : Nat → Bool) : Nat := countLit b [-59, -60]
def count896 (b : Nat → Bool) : Nat := countLit b [-55, -59, -60]
def count899 (b : Nat → Bool) : Nat := countLit b [-62, -64]
def count901 (b : Nat → Bool) : Nat := countLit b [-66, -67]
def count903 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -67]
def count907 (b : Nat → Bool) : Nat := countLit b [-55, -59, -60, -62, -64, -66, -67]
def count914 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count916 (b : Nat → Bool) : Nat := countLit b [-70, -72, -74]
def count919 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count921 (b : Nat → Bool) : Nat := countLit b [-78, -80]
def count923 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -80]
def count927 (b : Nat → Bool) : Nat := countLit b [-70, -72, -74, -75, -77, -78, -80]
def count934 (b : Nat → Bool) : Nat := countLit b [-55, -59, -60, -62, -64, -66, -67, -70, -72, -74, -75, -77, -78, -80]
def count948 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count950 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86]
def count953 (b : Nat → Bool) : Nat := countLit b [-87, -89]
def count955 (b : Nat → Bool) : Nat := countLit b [-93, -94]
def count957 (b : Nat → Bool) : Nat := countLit b [-87, -89, -93, -94]
def count961 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86, -87, -89, -93, -94]
def count968 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count970 (b : Nat → Bool) : Nat := countLit b [-100, -102]
def count972 (b : Nat → Bool) : Nat := countLit b [-95, -97, -100, -102]
def count976 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count978 (b : Nat → Bool) : Nat := countLit b [-108, -110]
def count980 (b : Nat → Bool) : Nat := countLit b [-103, -105, -108, -110]
def count984 (b : Nat → Bool) : Nat := countLit b [-95, -97, -100, -102, -103, -105, -108, -110]
def count992 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86, -87, -89, -93, -94, -95, -97, -100, -102, -103, -105, -108, -110]
def count1007 (b : Nat → Bool) : Nat := countLit b [-55, -59, -60, -62, -64, -66, -67, -70, -72, -74, -75, -77, -78, -80, -82, -85, -86, -87, -89, -93, -94, -95, -97, -100, -102, -103, -105, -108, -110]
def count1025 (b : Nat → Bool) : Nat := countLit b [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -22, -25, -27, -28, -30, -33, -34, -36, -37, -39, -42, -44, -45, -48, -50, -51, -52, -53, -55, -59, -60, -62, -64, -66, -67, -70, -72, -74, -75, -77, -78, -80, -82, -85, -86, -87, -89, -93, -94, -95, -97, -100, -102, -103, -105, -108, -110]
def count1043 (b : Nat → Bool) : Nat := countLit b [3, 7]
def count1045 (b : Nat → Bool) : Nat := countLit b [2, 3, 7]
def count1048 (b : Nat → Bool) : Nat := countLit b [10, 13]
def count1050 (b : Nat → Bool) : Nat := countLit b [8, 10, 13]
def count1053 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13]
def count1059 (b : Nat → Bool) : Nat := countLit b [16, 19]
def count1061 (b : Nat → Bool) : Nat := countLit b [14, 16, 19]
def count1064 (b : Nat → Bool) : Nat := countLit b [21, 23]
def count1066 (b : Nat → Bool) : Nat := countLit b [24, 26]
def count1068 (b : Nat → Bool) : Nat := countLit b [21, 23, 24, 26]
def count1072 (b : Nat → Bool) : Nat := countLit b [14, 16, 19, 21, 23, 24, 26]
def count1079 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13, 14, 16, 19, 21, 23, 24, 26]
def count1092 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count1094 (b : Nat → Bool) : Nat := countLit b [29, 31, 32]
def count1097 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count1099 (b : Nat → Bool) : Nat := countLit b [35, 38, 40]
def count1102 (b : Nat → Bool) : Nat := countLit b [29, 31, 32, 35, 38, 40]
def count1108 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count1110 (b : Nat → Bool) : Nat := countLit b [41, 43, 46]
def count1113 (b : Nat → Bool) : Nat := countLit b [47, 49]
def count1115 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count1117 (b : Nat → Bool) : Nat := countLit b [47, 49, 54, 56]
def count1121 (b : Nat → Bool) : Nat := countLit b [41, 43, 46, 47, 49, 54, 56]
def count1128 (b : Nat → Bool) : Nat := countLit b [29, 31, 32, 35, 38, 40, 41, 43, 46, 47, 49, 54, 56]
def count1141 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13, 14, 16, 19, 21, 23, 24, 26, 29, 31, 32, 35, 38, 40, 41, 43, 46, 47, 49, 54, 56]
def count1167 (b : Nat → Bool) : Nat := countLit b [58, 61]
def count1169 (b : Nat → Bool) : Nat := countLit b [57, 58, 61]
def count1172 (b : Nat → Bool) : Nat := countLit b [65, 68]
def count1174 (b : Nat → Bool) : Nat := countLit b [63, 65, 68]
def count1177 (b : Nat → Bool) : Nat := countLit b [57, 58, 61, 63, 65, 68]
def count1183 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count1185 (b : Nat → Bool) : Nat := countLit b [69, 71, 73]
def count1188 (b : Nat → Bool) : Nat := countLit b [76, 79]
def count1190 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count1192 (b : Nat → Bool) : Nat := countLit b [76, 79, 81, 83]
def count1196 (b : Nat → Bool) : Nat := countLit b [69, 71, 73, 76, 79, 81, 83]
def count1203 (b : Nat → Bool) : Nat := countLit b [57, 58, 61, 63, 65, 68, 69, 71, 73, 76, 79, 81, 83]
def count1216 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count1218 (b : Nat → Bool) : Nat := countLit b [84, 88, 90]
def count1221 (b : Nat → Bool) : Nat := countLit b [92, 96]
def count1223 (b : Nat → Bool) : Nat := countLit b [91, 92, 96]
def count1226 (b : Nat → Bool) : Nat := countLit b [84, 88, 90, 91, 92, 96]
def count1232 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count1234 (b : Nat → Bool) : Nat := countLit b [98, 99, 101]
def count1237 (b : Nat → Bool) : Nat := countLit b [104, 106]
def count1239 (b : Nat → Bool) : Nat := countLit b [107, 109]
def count1241 (b : Nat → Bool) : Nat := countLit b [104, 106, 107, 109]
def count1245 (b : Nat → Bool) : Nat := countLit b [98, 99, 101, 104, 106, 107, 109]
def count1252 (b : Nat → Bool) : Nat := countLit b [84, 88, 90, 91, 92, 96, 98, 99, 101, 104, 106, 107, 109]
def count1265 (b : Nat → Bool) : Nat := countLit b [57, 58, 61, 63, 65, 68, 69, 71, 73, 76, 79, 81, 83, 84, 88, 90, 91, 92, 96, 98, 99, 101, 104, 106, 107, 109]
def count1291 (b : Nat → Bool) : Nat := countLit b [2, 3, 7, 8, 10, 13, 14, 16, 19, 21, 23, 24, 26, 29, 31, 32, 35, 38, 40, 41, 43, 46, 47, 49, 54, 56, 57, 58, 61, 63, 65, 68, 69, 71, 73, 76, 79, 81, 83, 84, 88, 90, 91, 92, 96, 98, 99, 101, 104, 106, 107, 109]
def count1333 (b : Nat → Bool) : Nat := countLit b [-3, -7]
def count1335 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7]
def count1338 (b : Nat → Bool) : Nat := countLit b [-10, -13]
def count1340 (b : Nat → Bool) : Nat := countLit b [-8, -10, -13]
def count1343 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13]
def count1349 (b : Nat → Bool) : Nat := countLit b [-16, -19]
def count1351 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19]
def count1354 (b : Nat → Bool) : Nat := countLit b [-21, -23]
def count1356 (b : Nat → Bool) : Nat := countLit b [-24, -26]
def count1358 (b : Nat → Bool) : Nat := countLit b [-21, -23, -24, -26]
def count1362 (b : Nat → Bool) : Nat := countLit b [-14, -16, -19, -21, -23, -24, -26]
def count1369 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26]
def count1381 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count1383 (b : Nat → Bool) : Nat := countLit b [-29, -31, -32]
def count1386 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1388 (b : Nat → Bool) : Nat := countLit b [-35, -38, -40]
def count1391 (b : Nat → Bool) : Nat := countLit b [-29, -31, -32, -35, -38, -40]
def count1397 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count1399 (b : Nat → Bool) : Nat := countLit b [-41, -43, -46]
def count1402 (b : Nat → Bool) : Nat := countLit b [-47, -49]
def count1404 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count1406 (b : Nat → Bool) : Nat := countLit b [-47, -49, -54, -56]
def count1410 (b : Nat → Bool) : Nat := countLit b [-41, -43, -46, -47, -49, -54, -56]
def count1417 (b : Nat → Bool) : Nat := countLit b [-29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]
def count1429 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56]
def count1441 (b : Nat → Bool) : Nat := countLit b [-58, -61]
def count1443 (b : Nat → Bool) : Nat := countLit b [-57, -58, -61]
def count1446 (b : Nat → Bool) : Nat := countLit b [-65, -68]
def count1448 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68]
def count1451 (b : Nat → Bool) : Nat := countLit b [-57, -58, -61, -63, -65, -68]
def count1457 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count1459 (b : Nat → Bool) : Nat := countLit b [-69, -71, -73]
def count1462 (b : Nat → Bool) : Nat := countLit b [-76, -79]
def count1464 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count1466 (b : Nat → Bool) : Nat := countLit b [-76, -79, -81, -83]
def count1470 (b : Nat → Bool) : Nat := countLit b [-69, -71, -73, -76, -79, -81, -83]
def count1477 (b : Nat → Bool) : Nat := countLit b [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83]
def count1489 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count1491 (b : Nat → Bool) : Nat := countLit b [-84, -88, -90]
def count1494 (b : Nat → Bool) : Nat := countLit b [-92, -96]
def count1496 (b : Nat → Bool) : Nat := countLit b [-91, -92, -96]
def count1499 (b : Nat → Bool) : Nat := countLit b [-84, -88, -90, -91, -92, -96]
def count1505 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count1507 (b : Nat → Bool) : Nat := countLit b [-98, -99, -101]
def count1510 (b : Nat → Bool) : Nat := countLit b [-104, -106]
def count1512 (b : Nat → Bool) : Nat := countLit b [-107, -109]
def count1514 (b : Nat → Bool) : Nat := countLit b [-104, -106, -107, -109]
def count1518 (b : Nat → Bool) : Nat := countLit b [-98, -99, -101, -104, -106, -107, -109]
def count1525 (b : Nat → Bool) : Nat := countLit b [-84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]
def count1537 (b : Nat → Bool) : Nat := countLit b [-57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]
def count1549 (b : Nat → Bool) : Nat := countLit b [-2, -3, -7, -8, -10, -13, -14, -16, -19, -21, -23, -24, -26, -29, -31, -32, -35, -38, -40, -41, -43, -46, -47, -49, -54, -56, -57, -58, -61, -63, -65, -68, -69, -71, -73, -76, -79, -81, -83, -84, -88, -90, -91, -92, -96, -98, -99, -101, -104, -106, -107, -109]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 780 then (if i < 390 then (if i < 195 then (if i < 97 then (if i < 48 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 22 then b 21 else (if i < 23 then b 22 else b 23))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then b 24 else (if i < 26 then b 25 else b 26)) else (if i < 28 then b 27 else (if i < 29 then b 28 else b 29))) else (if i < 33 then (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)))) else (if i < 42 then (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41))) else (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)))))) else (if i < 72 then (if i < 60 then (if i < 54 then (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 52 then b 51 else (if i < 53 then b 52 else b 53))) else (if i < 57 then (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)) else (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)))) else (if i < 66 then (if i < 63 then (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)) else (if i < 64 then b 63 else (if i < 65 then b 64 else b 65))) else (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))))) else (if i < 84 then (if i < 78 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77))) else (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)))) else (if i < 90 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))) else (if i < 93 then (if i < 91 then b 90 else (if i < 92 then b 91 else b 92)) else (if i < 95 then (if i < 94 then b 93 else b 94) else (if i < 96 then b 95 else b 96))))))) else (if i < 146 then (if i < 121 then (if i < 109 then (if i < 103 then (if i < 100 then (if i < 98 then b 97 else (if i < 99 then b 98 else b 99)) else (if i < 101 then b 100 else (if i < 102 then b 101 else b 102))) else (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 107 then b 106 else (if i < 108 then b 107 else b 108)))) else (if i < 115 then (if i < 112 then (if i < 110 then b 109 else (if i < 111 then b 110 else b 111)) else (if i < 113 then b 112 else (if i < 114 then b 113 else b 114))) else (if i < 118 then (if i < 116 then b 115 else (if i < 117 then b 116 else b 117)) else (if i < 119 then b 118 else (if i < 120 then b 119 else b 120))))) else (if i < 133 then (if i < 127 then (if i < 124 then (if i < 122 then b 121 else (if i < 123 then b 122 else b 123)) else (if i < 125 then b 124 else (if i < 126 then b 125 else b 126))) else (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)))) else (if i < 139 then (if i < 136 then (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)) else (if i < 137 then b 136 else (if i < 138 then b 137 else b 138))) else (if i < 142 then (if i < 140 then b 139 else (if i < 141 then b 140 else b 141)) else (if i < 144 then (if i < 143 then b 142 else b 143) else (if i < 145 then b 144 else b 145)))))) else (if i < 170 then (if i < 158 then (if i < 152 then (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 150 then b 149 else (if i < 151 then b 150 else b 151))) else (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 156 then b 155 else (if i < 157 then b 156 else b 157)))) else (if i < 164 then (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 162 then b 161 else (if i < 163 then b 162 else b 163))) else (if i < 167 then (if i < 165 then b 164 else (if i < 166 then b 165 else b 166)) else (if i < 168 then b 167 else (if i < 169 then b 168 else b 169))))) else (if i < 182 then (if i < 176 then (if i < 173 then (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)) else (if i < 174 then b 173 else (if i < 175 then b 174 else b 175))) else (if i < 179 then (if i < 177 then b 176 else (if i < 178 then b 177 else b 178)) else (if i < 180 then b 179 else (if i < 181 then b 180 else b 181)))) else (if i < 188 then (if i < 185 then (if i < 183 then b 182 else (if i < 184 then b 183 else b 184)) else (if i < 186 then b 185 else (if i < 187 then b 186 else b 187))) else (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else b 194)))))))) else (if i < 292 then (if i < 243 then (if i < 219 then (if i < 207 then (if i < 201 then (if i < 198 then (if i < 196 then b 195 else (if i < 197 then b 196 else b 197)) else (if i < 199 then b 198 else (if i < 200 then b 199 else b 200))) else (if i < 204 then (if i < 202 then b 201 else (if i < 203 then b 202 else b 203)) else (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)))) else (if i < 213 then (if i < 210 then (if i < 208 then b 207 else (if i < 209 then b 208 else b 209)) else (if i < 211 then b 210 else (if i < 212 then b 211 else b 212))) else (if i < 216 then (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)) else (if i < 217 then b 216 else (if i < 218 then b 217 else b 218))))) else (if i < 231 then (if i < 225 then (if i < 222 then (if i < 220 then b 219 else (if i < 221 then b 220 else decide (1 ≤ count221 b))) else (if i < 223 then decide (2 ≤ count221 b) else (if i < 224 then decide (1 ≤ count223 b) else decide (2 ≤ count223 b)))) else (if i < 228 then (if i < 226 then decide (1 ≤ count225 b) else (if i < 227 then decide (2 ≤ count225 b) else decide (1 ≤ count227 b))) else (if i < 229 then decide (2 ≤ count227 b) else (if i < 230 then decide (1 ≤ count229 b) else decide (2 ≤ count229 b))))) else (if i < 237 then (if i < 234 then (if i < 232 then decide (1 ≤ count231 b) else (if i < 233 then decide (2 ≤ count231 b) else decide (1 ≤ count233 b))) else (if i < 235 then decide (2 ≤ count233 b) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b)))) else (if i < 240 then (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b))) else (if i < 241 then decide (2 ≤ count239 b) else (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b))))))) else (if i < 267 then (if i < 255 then (if i < 249 then (if i < 246 then (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b))) else (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)))) else (if i < 252 then (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))) else (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))))) else (if i < 261 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)))) else (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)))))) else (if i < 279 then (if i < 273 then (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)))) else (if i < 276 then (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))))) else (if i < 285 then (if i < 282 then (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b))) else (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)))) else (if i < 288 then (if i < 286 then decide (1 ≤ count285 b) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))) else (if i < 290 then (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b)))))))) else (if i < 341 then (if i < 316 then (if i < 304 then (if i < 298 then (if i < 295 then (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b))) else (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)))) else (if i < 301 then (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))) else (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))))) else (if i < 310 then (if i < 307 then (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))) else (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)))) else (if i < 313 then (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b))) else (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)))))) else (if i < 328 then (if i < 322 then (if i < 319 then (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))) else (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b)))) else (if i < 325 then (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))) else (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))))) else (if i < 334 then (if i < 331 then (if i < 329 then decide (2 ≤ count327 b) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b))) else (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)))) else (if i < 337 then (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b))) else (if i < 339 then (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b)) else (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b))))))) else (if i < 365 then (if i < 353 then (if i < 347 then (if i < 344 then (if i < 342 then decide (1 ≤ count341 b) else (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b))) else (if i < 345 then decide (2 ≤ count343 b) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))) else (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))))) else (if i < 359 then (if i < 356 then (if i < 354 then decide (1 ≤ count353 b) else (if i < 355 then decide (2 ≤ count353 b) else decide (1 ≤ count355 b))) else (if i < 357 then decide (2 ≤ count355 b) else (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)))) else (if i < 362 then (if i < 360 then decide (1 ≤ count359 b) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b))) else (if i < 363 then decide (2 ≤ count361 b) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b)))))) else (if i < 377 then (if i < 371 then (if i < 368 then (if i < 366 then decide (1 ≤ count365 b) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b))) else (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 375 then decide (2 ≤ count373 b) else (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b))))) else (if i < 383 then (if i < 380 then (if i < 378 then decide (1 ≤ count377 b) else (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b))) else (if i < 381 then decide (2 ≤ count379 b) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))) else (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 388 then (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)) else (if i < 389 then decide (2 ≤ count387 b) else decide (1 ≤ count389 b)))))))))) else (if i < 585 then (if i < 487 then (if i < 438 then (if i < 414 then (if i < 402 then (if i < 396 then (if i < 393 then (if i < 391 then decide (2 ≤ count389 b) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))) else (if i < 394 then decide (1 ≤ count393 b) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)))) else (if i < 399 then (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b))) else (if i < 400 then decide (1 ≤ count399 b) else (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b))))) else (if i < 408 then (if i < 405 then (if i < 403 then decide (2 ≤ count401 b) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b))) else (if i < 406 then decide (1 ≤ count405 b) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b)))) else (if i < 411 then (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))) else (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b)))))) else (if i < 426 then (if i < 420 then (if i < 417 then (if i < 415 then decide (2 ≤ count413 b) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b))) else (if i < 418 then decide (1 ≤ count417 b) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)))) else (if i < 423 then (if i < 421 then decide (2 ≤ count419 b) else (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b))) else (if i < 424 then decide (1 ≤ count423 b) else (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b))))) else (if i < 432 then (if i < 429 then (if i < 427 then decide (2 ≤ count425 b) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b))) else (if i < 430 then decide (1 ≤ count429 b) else (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)))) else (if i < 435 then (if i < 433 then decide (2 ≤ count431 b) else (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b))) else (if i < 436 then decide (1 ≤ count435 b) else (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b))))))) else (if i < 462 then (if i < 450 then (if i < 444 then (if i < 441 then (if i < 439 then decide (2 ≤ count437 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b))) else (if i < 442 then decide (3 ≤ count439 b) else (if i < 443 then decide (1 ≤ count442 b) else decide (2 ≤ count442 b)))) else (if i < 447 then (if i < 445 then decide (1 ≤ count444 b) else (if i < 446 then decide (2 ≤ count444 b) else decide (1 ≤ count446 b))) else (if i < 448 then decide (2 ≤ count446 b) else (if i < 449 then decide (3 ≤ count446 b) else decide (4 ≤ count446 b))))) else (if i < 456 then (if i < 453 then (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (3 ≤ count450 b))) else (if i < 454 then decide (4 ≤ count450 b) else (if i < 455 then decide (5 ≤ count450 b) else decide (6 ≤ count450 b)))) else (if i < 459 then (if i < 457 then decide (7 ≤ count450 b) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b))) else (if i < 460 then decide (1 ≤ count459 b) else (if i < 461 then decide (2 ≤ count459 b) else decide (3 ≤ count459 b)))))) else (if i < 474 then (if i < 468 then (if i < 465 then (if i < 463 then decide (1 ≤ count462 b) else (if i < 464 then decide (2 ≤ count462 b) else decide (1 ≤ count464 b))) else (if i < 466 then decide (2 ≤ count464 b) else (if i < 467 then decide (1 ≤ count466 b) else decide (2 ≤ count466 b)))) else (if i < 471 then (if i < 469 then decide (3 ≤ count466 b) else (if i < 470 then decide (4 ≤ count466 b) else decide (1 ≤ count470 b))) else (if i < 472 then decide (2 ≤ count470 b) else (if i < 473 then decide (3 ≤ count470 b) else decide (4 ≤ count470 b))))) else (if i < 480 then (if i < 477 then (if i < 475 then decide (5 ≤ count470 b) else (if i < 476 then decide (6 ≤ count470 b) else decide (7 ≤ count470 b))) else (if i < 478 then decide (1 ≤ count477 b) else (if i < 479 then decide (2 ≤ count477 b) else decide (3 ≤ count477 b)))) else (if i < 483 then (if i < 481 then decide (4 ≤ count477 b) else (if i < 482 then decide (5 ≤ count477 b) else decide (6 ≤ count477 b))) else (if i < 485 then (if i < 484 then decide (7 ≤ count477 b) else decide (8 ≤ count477 b)) else (if i < 486 then decide (9 ≤ count477 b) else decide (10 ≤ count477 b)))))))) else (if i < 536 then (if i < 511 then (if i < 499 then (if i < 493 then (if i < 490 then (if i < 488 then decide (11 ≤ count477 b) else (if i < 489 then decide (12 ≤ count477 b) else decide (13 ≤ count477 b))) else (if i < 491 then decide (14 ≤ count477 b) else (if i < 492 then decide (1 ≤ count491 b) else decide (2 ≤ count491 b)))) else (if i < 496 then (if i < 494 then decide (1 ≤ count493 b) else (if i < 495 then decide (2 ≤ count493 b) else decide (3 ≤ count493 b))) else (if i < 497 then decide (1 ≤ count496 b) else (if i < 498 then decide (2 ≤ count496 b) else decide (1 ≤ count498 b))))) else (if i < 505 then (if i < 502 then (if i < 500 then decide (2 ≤ count498 b) else (if i < 501 then decide (1 ≤ count500 b) else decide (2 ≤ count500 b))) else (if i < 503 then decide (3 ≤ count500 b) else (if i < 504 then decide (4 ≤ count500 b) else decide (1 ≤ count504 b)))) else (if i < 508 then (if i < 506 then decide (2 ≤ count504 b) else (if i < 507 then decide (3 ≤ count504 b) else decide (4 ≤ count504 b))) else (if i < 509 then decide (5 ≤ count504 b) else (if i < 510 then decide (6 ≤ count504 b) else decide (7 ≤ count504 b)))))) else (if i < 523 then (if i < 517 then (if i < 514 then (if i < 512 then decide (1 ≤ count511 b) else (if i < 513 then decide (2 ≤ count511 b) else decide (1 ≤ count513 b))) else (if i < 515 then decide (2 ≤ count513 b) else (if i < 516 then decide (1 ≤ count515 b) else decide (2 ≤ count515 b)))) else (if i < 520 then (if i < 518 then decide (3 ≤ count515 b) else (if i < 519 then decide (4 ≤ count515 b) else decide (1 ≤ count519 b))) else (if i < 521 then decide (2 ≤ count519 b) else (if i < 522 then decide (1 ≤ count521 b) else decide (2 ≤ count521 b))))) else (if i < 529 then (if i < 526 then (if i < 524 then decide (1 ≤ count523 b) else (if i < 525 then decide (2 ≤ count523 b) else decide (3 ≤ count523 b))) else (if i < 527 then decide (4 ≤ count523 b) else (if i < 528 then decide (1 ≤ count527 b) else decide (2 ≤ count527 b)))) else (if i < 532 then (if i < 530 then decide (3 ≤ count527 b) else (if i < 531 then decide (4 ≤ count527 b) else decide (5 ≤ count527 b))) else (if i < 534 then (if i < 533 then decide (6 ≤ count527 b) else decide (7 ≤ count527 b)) else (if i < 535 then decide (8 ≤ count527 b) else decide (1 ≤ count535 b))))))) else (if i < 560 then (if i < 548 then (if i < 542 then (if i < 539 then (if i < 537 then decide (2 ≤ count535 b) else (if i < 538 then decide (3 ≤ count535 b) else decide (4 ≤ count535 b))) else (if i < 540 then decide (5 ≤ count535 b) else (if i < 541 then decide (6 ≤ count535 b) else decide (7 ≤ count535 b)))) else (if i < 545 then (if i < 543 then decide (8 ≤ count535 b) else (if i < 544 then decide (9 ≤ count535 b) else decide (10 ≤ count535 b))) else (if i < 546 then decide (11 ≤ count535 b) else (if i < 547 then decide (12 ≤ count535 b) else decide (13 ≤ count535 b))))) else (if i < 554 then (if i < 551 then (if i < 549 then decide (14 ≤ count535 b) else (if i < 550 then decide (15 ≤ count535 b) else decide (1 ≤ count550 b))) else (if i < 552 then decide (2 ≤ count550 b) else (if i < 553 then decide (3 ≤ count550 b) else decide (4 ≤ count550 b)))) else (if i < 557 then (if i < 555 then decide (5 ≤ count550 b) else (if i < 556 then decide (6 ≤ count550 b) else decide (7 ≤ count550 b))) else (if i < 558 then decide (8 ≤ count550 b) else (if i < 559 then decide (9 ≤ count550 b) else decide (10 ≤ count550 b)))))) else (if i < 572 then (if i < 566 then (if i < 563 then (if i < 561 then decide (11 ≤ count550 b) else (if i < 562 then decide (12 ≤ count550 b) else decide (13 ≤ count550 b))) else (if i < 564 then decide (14 ≤ count550 b) else (if i < 565 then decide (15 ≤ count550 b) else decide (16 ≤ count550 b)))) else (if i < 569 then (if i < 567 then decide (17 ≤ count550 b) else (if i < 568 then decide (18 ≤ count550 b) else decide (19 ≤ count550 b))) else (if i < 570 then decide (20 ≤ count550 b) else (if i < 571 then decide (21 ≤ count550 b) else decide (22 ≤ count550 b))))) else (if i < 578 then (if i < 575 then (if i < 573 then decide (23 ≤ count550 b) else (if i < 574 then decide (24 ≤ count550 b) else decide (25 ≤ count550 b))) else (if i < 576 then decide (26 ≤ count550 b) else (if i < 577 then decide (27 ≤ count550 b) else decide (28 ≤ count550 b)))) else (if i < 581 then (if i < 579 then decide (29 ≤ count550 b) else (if i < 580 then decide (1 ≤ count579 b) else decide (2 ≤ count579 b))) else (if i < 583 then (if i < 582 then decide (1 ≤ count581 b) else decide (2 ≤ count581 b)) else (if i < 584 then decide (3 ≤ count581 b) else decide (1 ≤ count584 b))))))))) else (if i < 682 then (if i < 633 then (if i < 609 then (if i < 597 then (if i < 591 then (if i < 588 then (if i < 586 then decide (2 ≤ count584 b) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b))) else (if i < 589 then decide (1 ≤ count588 b) else (if i < 590 then decide (2 ≤ count588 b) else decide (3 ≤ count588 b)))) else (if i < 594 then (if i < 592 then decide (4 ≤ count588 b) else (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b))) else (if i < 595 then decide (3 ≤ count592 b) else (if i < 596 then decide (4 ≤ count592 b) else decide (5 ≤ count592 b))))) else (if i < 603 then (if i < 600 then (if i < 598 then decide (6 ≤ count592 b) else (if i < 599 then decide (7 ≤ count592 b) else decide (1 ≤ count599 b))) else (if i < 601 then decide (2 ≤ count599 b) else (if i < 602 then decide (1 ≤ count601 b) else decide (2 ≤ count601 b)))) else (if i < 606 then (if i < 604 then decide (3 ≤ count601 b) else (if i < 605 then decide (1 ≤ count604 b) else decide (2 ≤ count604 b))) else (if i < 607 then decide (1 ≤ count606 b) else (if i < 608 then decide (2 ≤ count606 b) else decide (1 ≤ count608 b)))))) else (if i < 621 then (if i < 615 then (if i < 612 then (if i < 610 then decide (2 ≤ count608 b) else (if i < 611 then decide (3 ≤ count608 b) else decide (4 ≤ count608 b))) else (if i < 613 then decide (1 ≤ count612 b) else (if i < 614 then decide (2 ≤ count612 b) else decide (3 ≤ count612 b)))) else (if i < 618 then (if i < 616 then decide (4 ≤ count612 b) else (if i < 617 then decide (5 ≤ count612 b) else decide (6 ≤ count612 b))) else (if i < 619 then decide (7 ≤ count612 b) else (if i < 620 then decide (1 ≤ count619 b) else decide (2 ≤ count619 b))))) else (if i < 627 then (if i < 624 then (if i < 622 then decide (3 ≤ count619 b) else (if i < 623 then decide (4 ≤ count619 b) else decide (5 ≤ count619 b))) else (if i < 625 then decide (6 ≤ count619 b) else (if i < 626 then decide (7 ≤ count619 b) else decide (8 ≤ count619 b)))) else (if i < 630 then (if i < 628 then decide (9 ≤ count619 b) else (if i < 629 then decide (10 ≤ count619 b) else decide (11 ≤ count619 b))) else (if i < 631 then decide (12 ≤ count619 b) else (if i < 632 then decide (13 ≤ count619 b) else decide (14 ≤ count619 b))))))) else (if i < 657 then (if i < 645 then (if i < 639 then (if i < 636 then (if i < 634 then decide (1 ≤ count633 b) else (if i < 635 then decide (2 ≤ count633 b) else decide (1 ≤ count635 b))) else (if i < 637 then decide (2 ≤ count635 b) else (if i < 638 then decide (3 ≤ count635 b) else decide (1 ≤ count638 b)))) else (if i < 642 then (if i < 640 then decide (2 ≤ count638 b) else (if i < 641 then decide (1 ≤ count640 b) else decide (2 ≤ count640 b))) else (if i < 643 then decide (1 ≤ count642 b) else (if i < 644 then decide (2 ≤ count642 b) else decide (3 ≤ count642 b))))) else (if i < 651 then (if i < 648 then (if i < 646 then decide (4 ≤ count642 b) else (if i < 647 then decide (1 ≤ count646 b) else decide (2 ≤ count646 b))) else (if i < 649 then decide (3 ≤ count646 b) else (if i < 650 then decide (4 ≤ count646 b) else decide (5 ≤ count646 b)))) else (if i < 654 then (if i < 652 then decide (6 ≤ count646 b) else (if i < 653 then decide (7 ≤ count646 b) else decide (1 ≤ count653 b))) else (if i < 655 then decide (2 ≤ count653 b) else (if i < 656 then decide (1 ≤ count655 b) else decide (2 ≤ count655 b)))))) else (if i < 669 then (if i < 663 then (if i < 660 then (if i < 658 then decide (1 ≤ count657 b) else (if i < 659 then decide (2 ≤ count657 b) else decide (3 ≤ count657 b))) else (if i < 661 then decide (4 ≤ count657 b) else (if i < 662 then decide (1 ≤ count661 b) else decide (2 ≤ count661 b)))) else (if i < 666 then (if i < 664 then decide (1 ≤ count663 b) else (if i < 665 then decide (2 ≤ count663 b) else decide (1 ≤ count665 b))) else (if i < 667 then decide (2 ≤ count665 b) else (if i < 668 then decide (3 ≤ count665 b) else decide (4 ≤ count665 b))))) else (if i < 675 then (if i < 672 then (if i < 670 then decide (1 ≤ count669 b) else (if i < 671 then decide (2 ≤ count669 b) else decide (3 ≤ count669 b))) else (if i < 673 then decide (4 ≤ count669 b) else (if i < 674 then decide (5 ≤ count669 b) else decide (6 ≤ count669 b)))) else (if i < 678 then (if i < 676 then decide (7 ≤ count669 b) else (if i < 677 then decide (8 ≤ count669 b) else decide (1 ≤ count677 b))) else (if i < 680 then (if i < 679 then decide (2 ≤ count677 b) else decide (3 ≤ count677 b)) else (if i < 681 then decide (4 ≤ count677 b) else decide (5 ≤ count677 b)))))))) else (if i < 731 then (if i < 706 then (if i < 694 then (if i < 688 then (if i < 685 then (if i < 683 then decide (6 ≤ count677 b) else (if i < 684 then decide (7 ≤ count677 b) else decide (8 ≤ count677 b))) else (if i < 686 then decide (9 ≤ count677 b) else (if i < 687 then decide (10 ≤ count677 b) else decide (11 ≤ count677 b)))) else (if i < 691 then (if i < 689 then decide (12 ≤ count677 b) else (if i < 690 then decide (13 ≤ count677 b) else decide (14 ≤ count677 b))) else (if i < 692 then decide (15 ≤ count677 b) else (if i < 693 then decide (1 ≤ count692 b) else decide (2 ≤ count692 b))))) else (if i < 700 then (if i < 697 then (if i < 695 then decide (3 ≤ count692 b) else (if i < 696 then decide (4 ≤ count692 b) else decide (5 ≤ count692 b))) else (if i < 698 then decide (6 ≤ count692 b) else (if i < 699 then decide (7 ≤ count692 b) else decide (8 ≤ count692 b)))) else (if i < 703 then (if i < 701 then decide (9 ≤ count692 b) else (if i < 702 then decide (10 ≤ count692 b) else decide (11 ≤ count692 b))) else (if i < 704 then decide (12 ≤ count692 b) else (if i < 705 then decide (13 ≤ count692 b) else decide (14 ≤ count692 b)))))) else (if i < 718 then (if i < 712 then (if i < 709 then (if i < 707 then decide (15 ≤ count692 b) else (if i < 708 then decide (16 ≤ count692 b) else decide (17 ≤ count692 b))) else (if i < 710 then decide (18 ≤ count692 b) else (if i < 711 then decide (19 ≤ count692 b) else decide (20 ≤ count692 b)))) else (if i < 715 then (if i < 713 then decide (21 ≤ count692 b) else (if i < 714 then decide (22 ≤ count692 b) else decide (23 ≤ count692 b))) else (if i < 716 then decide (24 ≤ count692 b) else (if i < 717 then decide (25 ≤ count692 b) else decide (26 ≤ count692 b))))) else (if i < 724 then (if i < 721 then (if i < 719 then decide (27 ≤ count692 b) else (if i < 720 then decide (28 ≤ count692 b) else decide (29 ≤ count692 b))) else (if i < 722 then decide (1 ≤ count721 b) else (if i < 723 then decide (2 ≤ count721 b) else decide (3 ≤ count721 b)))) else (if i < 727 then (if i < 725 then decide (4 ≤ count721 b) else (if i < 726 then decide (5 ≤ count721 b) else decide (6 ≤ count721 b))) else (if i < 729 then (if i < 728 then decide (7 ≤ count721 b) else decide (8 ≤ count721 b)) else (if i < 730 then decide (9 ≤ count721 b) else decide (10 ≤ count721 b))))))) else (if i < 755 then (if i < 743 then (if i < 737 then (if i < 734 then (if i < 732 then decide (11 ≤ count721 b) else (if i < 733 then decide (12 ≤ count721 b) else decide (13 ≤ count721 b))) else (if i < 735 then decide (14 ≤ count721 b) else (if i < 736 then decide (15 ≤ count721 b) else decide (16 ≤ count721 b)))) else (if i < 740 then (if i < 738 then decide (17 ≤ count721 b) else (if i < 739 then decide (18 ≤ count721 b) else decide (19 ≤ count721 b))) else (if i < 741 then decide (20 ≤ count721 b) else (if i < 742 then decide (21 ≤ count721 b) else decide (22 ≤ count721 b))))) else (if i < 749 then (if i < 746 then (if i < 744 then decide (23 ≤ count721 b) else (if i < 745 then decide (24 ≤ count721 b) else decide (25 ≤ count721 b))) else (if i < 747 then decide (26 ≤ count721 b) else (if i < 748 then decide (27 ≤ count721 b) else decide (28 ≤ count721 b)))) else (if i < 752 then (if i < 750 then decide (29 ≤ count721 b) else (if i < 751 then decide (30 ≤ count721 b) else decide (31 ≤ count721 b))) else (if i < 753 then decide (32 ≤ count721 b) else (if i < 754 then decide (33 ≤ count721 b) else decide (34 ≤ count721 b)))))) else (if i < 767 then (if i < 761 then (if i < 758 then (if i < 756 then decide (35 ≤ count721 b) else (if i < 757 then decide (36 ≤ count721 b) else decide (37 ≤ count721 b))) else (if i < 759 then decide (38 ≤ count721 b) else (if i < 760 then decide (39 ≤ count721 b) else decide (40 ≤ count721 b)))) else (if i < 764 then (if i < 762 then decide (41 ≤ count721 b) else (if i < 763 then decide (42 ≤ count721 b) else decide (1 ≤ count763 b))) else (if i < 765 then decide (2 ≤ count763 b) else (if i < 766 then decide (1 ≤ count765 b) else decide (2 ≤ count765 b))))) else (if i < 773 then (if i < 770 then (if i < 768 then decide (3 ≤ count765 b) else (if i < 769 then decide (1 ≤ count768 b) else decide (2 ≤ count768 b))) else (if i < 771 then decide (1 ≤ count770 b) else (if i < 772 then decide (2 ≤ count770 b) else decide (1 ≤ count772 b)))) else (if i < 776 then (if i < 774 then decide (2 ≤ count772 b) else (if i < 775 then decide (3 ≤ count772 b) else decide (4 ≤ count772 b))) else (if i < 778 then (if i < 777 then decide (1 ≤ count776 b) else decide (2 ≤ count776 b)) else (if i < 779 then decide (3 ≤ count776 b) else decide (4 ≤ count776 b))))))))))) else (if i < 1170 then (if i < 975 then (if i < 877 then (if i < 828 then (if i < 804 then (if i < 792 then (if i < 786 then (if i < 783 then (if i < 781 then decide (5 ≤ count776 b) else (if i < 782 then decide (6 ≤ count776 b) else decide (7 ≤ count776 b))) else (if i < 784 then decide (1 ≤ count783 b) else (if i < 785 then decide (2 ≤ count783 b) else decide (1 ≤ count785 b)))) else (if i < 789 then (if i < 787 then decide (2 ≤ count785 b) else (if i < 788 then decide (3 ≤ count785 b) else decide (1 ≤ count788 b))) else (if i < 790 then decide (2 ≤ count788 b) else (if i < 791 then decide (1 ≤ count790 b) else decide (2 ≤ count790 b))))) else (if i < 798 then (if i < 795 then (if i < 793 then decide (1 ≤ count792 b) else (if i < 794 then decide (2 ≤ count792 b) else decide (3 ≤ count792 b))) else (if i < 796 then decide (4 ≤ count792 b) else (if i < 797 then decide (1 ≤ count796 b) else decide (2 ≤ count796 b)))) else (if i < 801 then (if i < 799 then decide (3 ≤ count796 b) else (if i < 800 then decide (4 ≤ count796 b) else decide (5 ≤ count796 b))) else (if i < 802 then decide (6 ≤ count796 b) else (if i < 803 then decide (7 ≤ count796 b) else decide (1 ≤ count803 b)))))) else (if i < 816 then (if i < 810 then (if i < 807 then (if i < 805 then decide (2 ≤ count803 b) else (if i < 806 then decide (3 ≤ count803 b) else decide (4 ≤ count803 b))) else (if i < 808 then decide (5 ≤ count803 b) else (if i < 809 then decide (6 ≤ count803 b) else decide (7 ≤ count803 b)))) else (if i < 813 then (if i < 811 then decide (8 ≤ count803 b) else (if i < 812 then decide (9 ≤ count803 b) else decide (10 ≤ count803 b))) else (if i < 814 then decide (11 ≤ count803 b) else (if i < 815 then decide (12 ≤ count803 b) else decide (13 ≤ count803 b))))) else (if i < 822 then (if i < 819 then (if i < 817 then decide (14 ≤ count803 b) else (if i < 818 then decide (1 ≤ count817 b) else decide (2 ≤ count817 b))) else (if i < 820 then decide (1 ≤ count819 b) else (if i < 821 then decide (2 ≤ count819 b) else decide (3 ≤ count819 b)))) else (if i < 825 then (if i < 823 then decide (1 ≤ count822 b) else (if i < 824 then decide (2 ≤ count822 b) else decide (1 ≤ count824 b))) else (if i < 826 then decide (2 ≤ count824 b) else (if i < 827 then decide (1 ≤ count826 b) else decide (2 ≤ count826 b))))))) else (if i < 852 then (if i < 840 then (if i < 834 then (if i < 831 then (if i < 829 then decide (3 ≤ count826 b) else (if i < 830 then decide (4 ≤ count826 b) else decide (1 ≤ count830 b))) else (if i < 832 then decide (2 ≤ count830 b) else (if i < 833 then decide (3 ≤ count830 b) else decide (4 ≤ count830 b)))) else (if i < 837 then (if i < 835 then decide (5 ≤ count830 b) else (if i < 836 then decide (6 ≤ count830 b) else decide (7 ≤ count830 b))) else (if i < 838 then decide (1 ≤ count837 b) else (if i < 839 then decide (2 ≤ count837 b) else decide (1 ≤ count839 b))))) else (if i < 846 then (if i < 843 then (if i < 841 then decide (2 ≤ count839 b) else (if i < 842 then decide (1 ≤ count841 b) else decide (2 ≤ count841 b))) else (if i < 844 then decide (3 ≤ count841 b) else (if i < 845 then decide (4 ≤ count841 b) else decide (1 ≤ count845 b)))) else (if i < 849 then (if i < 847 then decide (2 ≤ count845 b) else (if i < 848 then decide (1 ≤ count847 b) else decide (2 ≤ count847 b))) else (if i < 850 then decide (1 ≤ count849 b) else (if i < 851 then decide (2 ≤ count849 b) else decide (3 ≤ count849 b)))))) else (if i < 864 then (if i < 858 then (if i < 855 then (if i < 853 then decide (4 ≤ count849 b) else (if i < 854 then decide (1 ≤ count853 b) else decide (2 ≤ count853 b))) else (if i < 856 then decide (3 ≤ count853 b) else (if i < 857 then decide (4 ≤ count853 b) else decide (5 ≤ count853 b)))) else (if i < 861 then (if i < 859 then decide (6 ≤ count853 b) else (if i < 860 then decide (7 ≤ count853 b) else decide (8 ≤ count853 b))) else (if i < 862 then decide (1 ≤ count861 b) else (if i < 863 then decide (2 ≤ count861 b) else decide (3 ≤ count861 b))))) else (if i < 870 then (if i < 867 then (if i < 865 then decide (4 ≤ count861 b) else (if i < 866 then decide (5 ≤ count861 b) else decide (6 ≤ count861 b))) else (if i < 868 then decide (7 ≤ count861 b) else (if i < 869 then decide (8 ≤ count861 b) else decide (9 ≤ count861 b)))) else (if i < 873 then (if i < 871 then decide (10 ≤ count861 b) else (if i < 872 then decide (11 ≤ count861 b) else decide (12 ≤ count861 b))) else (if i < 875 then (if i < 874 then decide (13 ≤ count861 b) else decide (14 ≤ count861 b)) else (if i < 876 then decide (15 ≤ count861 b) else decide (1 ≤ count876 b)))))))) else (if i < 926 then (if i < 901 then (if i < 889 then (if i < 883 then (if i < 880 then (if i < 878 then decide (2 ≤ count876 b) else (if i < 879 then decide (3 ≤ count876 b) else decide (4 ≤ count876 b))) else (if i < 881 then decide (5 ≤ count876 b) else (if i < 882 then decide (6 ≤ count876 b) else decide (7 ≤ count876 b)))) else (if i < 886 then (if i < 884 then decide (8 ≤ count876 b) else (if i < 885 then decide (9 ≤ count876 b) else decide (10 ≤ count876 b))) else (if i < 887 then decide (11 ≤ count876 b) else (if i < 888 then decide (12 ≤ count876 b) else decide (13 ≤ count876 b))))) else (if i < 895 then (if i < 892 then (if i < 890 then decide (14 ≤ count876 b) else (if i < 891 then decide (15 ≤ count876 b) else decide (16 ≤ count876 b))) else (if i < 893 then decide (17 ≤ count876 b) else (if i < 894 then decide (18 ≤ count876 b) else decide (1 ≤ count894 b)))) else (if i < 898 then (if i < 896 then decide (2 ≤ count894 b) else (if i < 897 then decide (1 ≤ count896 b) else decide (2 ≤ count896 b))) else (if i < 899 then decide (3 ≤ count896 b) else (if i < 900 then decide (1 ≤ count899 b) else decide (2 ≤ count899 b)))))) else (if i < 913 then (if i < 907 then (if i < 904 then (if i < 902 then decide (1 ≤ count901 b) else (if i < 903 then decide (2 ≤ count901 b) else decide (1 ≤ count903 b))) else (if i < 905 then decide (2 ≤ count903 b) else (if i < 906 then decide (3 ≤ count903 b) else decide (4 ≤ count903 b)))) else (if i < 910 then (if i < 908 then decide (1 ≤ count907 b) else (if i < 909 then decide (2 ≤ count907 b) else decide (3 ≤ count907 b))) else (if i < 911 then decide (4 ≤ count907 b) else (if i < 912 then decide (5 ≤ count907 b) else decide (6 ≤ count907 b))))) else (if i < 919 then (if i < 916 then (if i < 914 then decide (7 ≤ count907 b) else (if i < 915 then decide (1 ≤ count914 b) else decide (2 ≤ count914 b))) else (if i < 917 then decide (1 ≤ count916 b) else (if i < 918 then decide (2 ≤ count916 b) else decide (3 ≤ count916 b)))) else (if i < 922 then (if i < 920 then decide (1 ≤ count919 b) else (if i < 921 then decide (2 ≤ count919 b) else decide (1 ≤ count921 b))) else (if i < 924 then (if i < 923 then decide (2 ≤ count921 b) else decide (1 ≤ count923 b)) else (if i < 925 then decide (2 ≤ count923 b) else decide (3 ≤ count923 b))))))) else (if i < 950 then (if i < 938 then (if i < 932 then (if i < 929 then (if i < 927 then decide (4 ≤ count923 b) else (if i < 928 then decide (1 ≤ count927 b) else decide (2 ≤ count927 b))) else (if i < 930 then decide (3 ≤ count927 b) else (if i < 931 then decide (4 ≤ count927 b) else decide (5 ≤ count927 b)))) else (if i < 935 then (if i < 933 then decide (6 ≤ count927 b) else (if i < 934 then decide (7 ≤ count927 b) else decide (1 ≤ count934 b))) else (if i < 936 then decide (2 ≤ count934 b) else (if i < 937 then decide (3 ≤ count934 b) else decide (4 ≤ count934 b))))) else (if i < 944 then (if i < 941 then (if i < 939 then decide (5 ≤ count934 b) else (if i < 940 then decide (6 ≤ count934 b) else decide (7 ≤ count934 b))) else (if i < 942 then decide (8 ≤ count934 b) else (if i < 943 then decide (9 ≤ count934 b) else decide (10 ≤ count934 b)))) else (if i < 947 then (if i < 945 then decide (11 ≤ count934 b) else (if i < 946 then decide (12 ≤ count934 b) else decide (13 ≤ count934 b))) else (if i < 948 then decide (14 ≤ count934 b) else (if i < 949 then decide (1 ≤ count948 b) else decide (2 ≤ count948 b)))))) else (if i < 962 then (if i < 956 then (if i < 953 then (if i < 951 then decide (1 ≤ count950 b) else (if i < 952 then decide (2 ≤ count950 b) else decide (3 ≤ count950 b))) else (if i < 954 then decide (1 ≤ count953 b) else (if i < 955 then decide (2 ≤ count953 b) else decide (1 ≤ count955 b)))) else (if i < 959 then (if i < 957 then decide (2 ≤ count955 b) else (if i < 958 then decide (1 ≤ count957 b) else decide (2 ≤ count957 b))) else (if i < 960 then decide (3 ≤ count957 b) else (if i < 961 then decide (4 ≤ count957 b) else decide (1 ≤ count961 b))))) else (if i < 968 then (if i < 965 then (if i < 963 then decide (2 ≤ count961 b) else (if i < 964 then decide (3 ≤ count961 b) else decide (4 ≤ count961 b))) else (if i < 966 then decide (5 ≤ count961 b) else (if i < 967 then decide (6 ≤ count961 b) else decide (7 ≤ count961 b)))) else (if i < 971 then (if i < 969 then decide (1 ≤ count968 b) else (if i < 970 then decide (2 ≤ count968 b) else decide (1 ≤ count970 b))) else (if i < 973 then (if i < 972 then decide (2 ≤ count970 b) else decide (1 ≤ count972 b)) else (if i < 974 then decide (2 ≤ count972 b) else decide (3 ≤ count972 b))))))))) else (if i < 1072 then (if i < 1023 then (if i < 999 then (if i < 987 then (if i < 981 then (if i < 978 then (if i < 976 then decide (4 ≤ count972 b) else (if i < 977 then decide (1 ≤ count976 b) else decide (2 ≤ count976 b))) else (if i < 979 then decide (1 ≤ count978 b) else (if i < 980 then decide (2 ≤ count978 b) else decide (1 ≤ count980 b)))) else (if i < 984 then (if i < 982 then decide (2 ≤ count980 b) else (if i < 983 then decide (3 ≤ count980 b) else decide (4 ≤ count980 b))) else (if i < 985 then decide (1 ≤ count984 b) else (if i < 986 then decide (2 ≤ count984 b) else decide (3 ≤ count984 b))))) else (if i < 993 then (if i < 990 then (if i < 988 then decide (4 ≤ count984 b) else (if i < 989 then decide (5 ≤ count984 b) else decide (6 ≤ count984 b))) else (if i < 991 then decide (7 ≤ count984 b) else (if i < 992 then decide (8 ≤ count984 b) else decide (1 ≤ count992 b)))) else (if i < 996 then (if i < 994 then decide (2 ≤ count992 b) else (if i < 995 then decide (3 ≤ count992 b) else decide (4 ≤ count992 b))) else (if i < 997 then decide (5 ≤ count992 b) else (if i < 998 then decide (6 ≤ count992 b) else decide (7 ≤ count992 b)))))) else (if i < 1011 then (if i < 1005 then (if i < 1002 then (if i < 1000 then decide (8 ≤ count992 b) else (if i < 1001 then decide (9 ≤ count992 b) else decide (10 ≤ count992 b))) else (if i < 1003 then decide (11 ≤ count992 b) else (if i < 1004 then decide (12 ≤ count992 b) else decide (13 ≤ count992 b)))) else (if i < 1008 then (if i < 1006 then decide (14 ≤ count992 b) else (if i < 1007 then decide (15 ≤ count992 b) else decide (1 ≤ count1007 b))) else (if i < 1009 then decide (2 ≤ count1007 b) else (if i < 1010 then decide (3 ≤ count1007 b) else decide (4 ≤ count1007 b))))) else (if i < 1017 then (if i < 1014 then (if i < 1012 then decide (5 ≤ count1007 b) else (if i < 1013 then decide (6 ≤ count1007 b) else decide (7 ≤ count1007 b))) else (if i < 1015 then decide (8 ≤ count1007 b) else (if i < 1016 then decide (9 ≤ count1007 b) else decide (10 ≤ count1007 b)))) else (if i < 1020 then (if i < 1018 then decide (11 ≤ count1007 b) else (if i < 1019 then decide (12 ≤ count1007 b) else decide (13 ≤ count1007 b))) else (if i < 1021 then decide (14 ≤ count1007 b) else (if i < 1022 then decide (15 ≤ count1007 b) else decide (16 ≤ count1007 b))))))) else (if i < 1047 then (if i < 1035 then (if i < 1029 then (if i < 1026 then (if i < 1024 then decide (17 ≤ count1007 b) else (if i < 1025 then decide (18 ≤ count1007 b) else decide (1 ≤ count1025 b))) else (if i < 1027 then decide (2 ≤ count1025 b) else (if i < 1028 then decide (3 ≤ count1025 b) else decide (4 ≤ count1025 b)))) else (if i < 1032 then (if i < 1030 then decide (5 ≤ count1025 b) else (if i < 1031 then decide (6 ≤ count1025 b) else decide (7 ≤ count1025 b))) else (if i < 1033 then decide (8 ≤ count1025 b) else (if i < 1034 then decide (9 ≤ count1025 b) else decide (10 ≤ count1025 b))))) else (if i < 1041 then (if i < 1038 then (if i < 1036 then decide (11 ≤ count1025 b) else (if i < 1037 then decide (12 ≤ count1025 b) else decide (13 ≤ count1025 b))) else (if i < 1039 then decide (14 ≤ count1025 b) else (if i < 1040 then decide (15 ≤ count1025 b) else decide (16 ≤ count1025 b)))) else (if i < 1044 then (if i < 1042 then decide (17 ≤ count1025 b) else (if i < 1043 then decide (18 ≤ count1025 b) else decide (1 ≤ count1043 b))) else (if i < 1045 then decide (2 ≤ count1043 b) else (if i < 1046 then decide (1 ≤ count1045 b) else decide (2 ≤ count1045 b)))))) else (if i < 1059 then (if i < 1053 then (if i < 1050 then (if i < 1048 then decide (3 ≤ count1045 b) else (if i < 1049 then decide (1 ≤ count1048 b) else decide (2 ≤ count1048 b))) else (if i < 1051 then decide (1 ≤ count1050 b) else (if i < 1052 then decide (2 ≤ count1050 b) else decide (3 ≤ count1050 b)))) else (if i < 1056 then (if i < 1054 then decide (1 ≤ count1053 b) else (if i < 1055 then decide (2 ≤ count1053 b) else decide (3 ≤ count1053 b))) else (if i < 1057 then decide (4 ≤ count1053 b) else (if i < 1058 then decide (5 ≤ count1053 b) else decide (6 ≤ count1053 b))))) else (if i < 1065 then (if i < 1062 then (if i < 1060 then decide (1 ≤ count1059 b) else (if i < 1061 then decide (2 ≤ count1059 b) else decide (1 ≤ count1061 b))) else (if i < 1063 then decide (2 ≤ count1061 b) else (if i < 1064 then decide (3 ≤ count1061 b) else decide (1 ≤ count1064 b)))) else (if i < 1068 then (if i < 1066 then decide (2 ≤ count1064 b) else (if i < 1067 then decide (1 ≤ count1066 b) else decide (2 ≤ count1066 b))) else (if i < 1070 then (if i < 1069 then decide (1 ≤ count1068 b) else decide (2 ≤ count1068 b)) else (if i < 1071 then decide (3 ≤ count1068 b) else decide (4 ≤ count1068 b)))))))) else (if i < 1121 then (if i < 1096 then (if i < 1084 then (if i < 1078 then (if i < 1075 then (if i < 1073 then decide (1 ≤ count1072 b) else (if i < 1074 then decide (2 ≤ count1072 b) else decide (3 ≤ count1072 b))) else (if i < 1076 then decide (4 ≤ count1072 b) else (if i < 1077 then decide (5 ≤ count1072 b) else decide (6 ≤ count1072 b)))) else (if i < 1081 then (if i < 1079 then decide (7 ≤ count1072 b) else (if i < 1080 then decide (1 ≤ count1079 b) else decide (2 ≤ count1079 b))) else (if i < 1082 then decide (3 ≤ count1079 b) else (if i < 1083 then decide (4 ≤ count1079 b) else decide (5 ≤ count1079 b))))) else (if i < 1090 then (if i < 1087 then (if i < 1085 then decide (6 ≤ count1079 b) else (if i < 1086 then decide (7 ≤ count1079 b) else decide (8 ≤ count1079 b))) else (if i < 1088 then decide (9 ≤ count1079 b) else (if i < 1089 then decide (10 ≤ count1079 b) else decide (11 ≤ count1079 b)))) else (if i < 1093 then (if i < 1091 then decide (12 ≤ count1079 b) else (if i < 1092 then decide (13 ≤ count1079 b) else decide (1 ≤ count1092 b))) else (if i < 1094 then decide (2 ≤ count1092 b) else (if i < 1095 then decide (1 ≤ count1094 b) else decide (2 ≤ count1094 b)))))) else (if i < 1108 then (if i < 1102 then (if i < 1099 then (if i < 1097 then decide (3 ≤ count1094 b) else (if i < 1098 then decide (1 ≤ count1097 b) else decide (2 ≤ count1097 b))) else (if i < 1100 then decide (1 ≤ count1099 b) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (3 ≤ count1099 b)))) else (if i < 1105 then (if i < 1103 then decide (1 ≤ count1102 b) else (if i < 1104 then decide (2 ≤ count1102 b) else decide (3 ≤ count1102 b))) else (if i < 1106 then decide (4 ≤ count1102 b) else (if i < 1107 then decide (5 ≤ count1102 b) else decide (6 ≤ count1102 b))))) else (if i < 1114 then (if i < 1111 then (if i < 1109 then decide (1 ≤ count1108 b) else (if i < 1110 then decide (2 ≤ count1108 b) else decide (1 ≤ count1110 b))) else (if i < 1112 then decide (2 ≤ count1110 b) else (if i < 1113 then decide (3 ≤ count1110 b) else decide (1 ≤ count1113 b)))) else (if i < 1117 then (if i < 1115 then decide (2 ≤ count1113 b) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b))) else (if i < 1119 then (if i < 1118 then decide (1 ≤ count1117 b) else decide (2 ≤ count1117 b)) else (if i < 1120 then decide (3 ≤ count1117 b) else decide (4 ≤ count1117 b))))))) else (if i < 1145 then (if i < 1133 then (if i < 1127 then (if i < 1124 then (if i < 1122 then decide (1 ≤ count1121 b) else (if i < 1123 then decide (2 ≤ count1121 b) else decide (3 ≤ count1121 b))) else (if i < 1125 then decide (4 ≤ count1121 b) else (if i < 1126 then decide (5 ≤ count1121 b) else decide (6 ≤ count1121 b)))) else (if i < 1130 then (if i < 1128 then decide (7 ≤ count1121 b) else (if i < 1129 then decide (1 ≤ count1128 b) else decide (2 ≤ count1128 b))) else (if i < 1131 then decide (3 ≤ count1128 b) else (if i < 1132 then decide (4 ≤ count1128 b) else decide (5 ≤ count1128 b))))) else (if i < 1139 then (if i < 1136 then (if i < 1134 then decide (6 ≤ count1128 b) else (if i < 1135 then decide (7 ≤ count1128 b) else decide (8 ≤ count1128 b))) else (if i < 1137 then decide (9 ≤ count1128 b) else (if i < 1138 then decide (10 ≤ count1128 b) else decide (11 ≤ count1128 b)))) else (if i < 1142 then (if i < 1140 then decide (12 ≤ count1128 b) else (if i < 1141 then decide (13 ≤ count1128 b) else decide (1 ≤ count1141 b))) else (if i < 1143 then decide (2 ≤ count1141 b) else (if i < 1144 then decide (3 ≤ count1141 b) else decide (4 ≤ count1141 b)))))) else (if i < 1157 then (if i < 1151 then (if i < 1148 then (if i < 1146 then decide (5 ≤ count1141 b) else (if i < 1147 then decide (6 ≤ count1141 b) else decide (7 ≤ count1141 b))) else (if i < 1149 then decide (8 ≤ count1141 b) else (if i < 1150 then decide (9 ≤ count1141 b) else decide (10 ≤ count1141 b)))) else (if i < 1154 then (if i < 1152 then decide (11 ≤ count1141 b) else (if i < 1153 then decide (12 ≤ count1141 b) else decide (13 ≤ count1141 b))) else (if i < 1155 then decide (14 ≤ count1141 b) else (if i < 1156 then decide (15 ≤ count1141 b) else decide (16 ≤ count1141 b))))) else (if i < 1163 then (if i < 1160 then (if i < 1158 then decide (17 ≤ count1141 b) else (if i < 1159 then decide (18 ≤ count1141 b) else decide (19 ≤ count1141 b))) else (if i < 1161 then decide (20 ≤ count1141 b) else (if i < 1162 then decide (21 ≤ count1141 b) else decide (22 ≤ count1141 b)))) else (if i < 1166 then (if i < 1164 then decide (23 ≤ count1141 b) else (if i < 1165 then decide (24 ≤ count1141 b) else decide (25 ≤ count1141 b))) else (if i < 1168 then (if i < 1167 then decide (26 ≤ count1141 b) else decide (1 ≤ count1167 b)) else (if i < 1169 then decide (2 ≤ count1167 b) else decide (1 ≤ count1169 b)))))))))) else (if i < 1365 then (if i < 1267 then (if i < 1218 then (if i < 1194 then (if i < 1182 then (if i < 1176 then (if i < 1173 then (if i < 1171 then decide (2 ≤ count1169 b) else (if i < 1172 then decide (3 ≤ count1169 b) else decide (1 ≤ count1172 b))) else (if i < 1174 then decide (2 ≤ count1172 b) else (if i < 1175 then decide (1 ≤ count1174 b) else decide (2 ≤ count1174 b)))) else (if i < 1179 then (if i < 1177 then decide (3 ≤ count1174 b) else (if i < 1178 then decide (1 ≤ count1177 b) else decide (2 ≤ count1177 b))) else (if i < 1180 then decide (3 ≤ count1177 b) else (if i < 1181 then decide (4 ≤ count1177 b) else decide (5 ≤ count1177 b))))) else (if i < 1188 then (if i < 1185 then (if i < 1183 then decide (6 ≤ count1177 b) else (if i < 1184 then decide (1 ≤ count1183 b) else decide (2 ≤ count1183 b))) else (if i < 1186 then decide (1 ≤ count1185 b) else (if i < 1187 then decide (2 ≤ count1185 b) else decide (3 ≤ count1185 b)))) else (if i < 1191 then (if i < 1189 then decide (1 ≤ count1188 b) else (if i < 1190 then decide (2 ≤ count1188 b) else decide (1 ≤ count1190 b))) else (if i < 1192 then decide (2 ≤ count1190 b) else (if i < 1193 then decide (1 ≤ count1192 b) else decide (2 ≤ count1192 b)))))) else (if i < 1206 then (if i < 1200 then (if i < 1197 then (if i < 1195 then decide (3 ≤ count1192 b) else (if i < 1196 then decide (4 ≤ count1192 b) else decide (1 ≤ count1196 b))) else (if i < 1198 then decide (2 ≤ count1196 b) else (if i < 1199 then decide (3 ≤ count1196 b) else decide (4 ≤ count1196 b)))) else (if i < 1203 then (if i < 1201 then decide (5 ≤ count1196 b) else (if i < 1202 then decide (6 ≤ count1196 b) else decide (7 ≤ count1196 b))) else (if i < 1204 then decide (1 ≤ count1203 b) else (if i < 1205 then decide (2 ≤ count1203 b) else decide (3 ≤ count1203 b))))) else (if i < 1212 then (if i < 1209 then (if i < 1207 then decide (4 ≤ count1203 b) else (if i < 1208 then decide (5 ≤ count1203 b) else decide (6 ≤ count1203 b))) else (if i < 1210 then decide (7 ≤ count1203 b) else (if i < 1211 then decide (8 ≤ count1203 b) else decide (9 ≤ count1203 b)))) else (if i < 1215 then (if i < 1213 then decide (10 ≤ count1203 b) else (if i < 1214 then decide (11 ≤ count1203 b) else decide (12 ≤ count1203 b))) else (if i < 1216 then decide (13 ≤ count1203 b) else (if i < 1217 then decide (1 ≤ count1216 b) else decide (2 ≤ count1216 b))))))) else (if i < 1242 then (if i < 1230 then (if i < 1224 then (if i < 1221 then (if i < 1219 then decide (1 ≤ count1218 b) else (if i < 1220 then decide (2 ≤ count1218 b) else decide (3 ≤ count1218 b))) else (if i < 1222 then decide (1 ≤ count1221 b) else (if i < 1223 then decide (2 ≤ count1221 b) else decide (1 ≤ count1223 b)))) else (if i < 1227 then (if i < 1225 then decide (2 ≤ count1223 b) else (if i < 1226 then decide (3 ≤ count1223 b) else decide (1 ≤ count1226 b))) else (if i < 1228 then decide (2 ≤ count1226 b) else (if i < 1229 then decide (3 ≤ count1226 b) else decide (4 ≤ count1226 b))))) else (if i < 1236 then (if i < 1233 then (if i < 1231 then decide (5 ≤ count1226 b) else (if i < 1232 then decide (6 ≤ count1226 b) else decide (1 ≤ count1232 b))) else (if i < 1234 then decide (2 ≤ count1232 b) else (if i < 1235 then decide (1 ≤ count1234 b) else decide (2 ≤ count1234 b)))) else (if i < 1239 then (if i < 1237 then decide (3 ≤ count1234 b) else (if i < 1238 then decide (1 ≤ count1237 b) else decide (2 ≤ count1237 b))) else (if i < 1240 then decide (1 ≤ count1239 b) else (if i < 1241 then decide (2 ≤ count1239 b) else decide (1 ≤ count1241 b)))))) else (if i < 1254 then (if i < 1248 then (if i < 1245 then (if i < 1243 then decide (2 ≤ count1241 b) else (if i < 1244 then decide (3 ≤ count1241 b) else decide (4 ≤ count1241 b))) else (if i < 1246 then decide (1 ≤ count1245 b) else (if i < 1247 then decide (2 ≤ count1245 b) else decide (3 ≤ count1245 b)))) else (if i < 1251 then (if i < 1249 then decide (4 ≤ count1245 b) else (if i < 1250 then decide (5 ≤ count1245 b) else decide (6 ≤ count1245 b))) else (if i < 1252 then decide (7 ≤ count1245 b) else (if i < 1253 then decide (1 ≤ count1252 b) else decide (2 ≤ count1252 b))))) else (if i < 1260 then (if i < 1257 then (if i < 1255 then decide (3 ≤ count1252 b) else (if i < 1256 then decide (4 ≤ count1252 b) else decide (5 ≤ count1252 b))) else (if i < 1258 then decide (6 ≤ count1252 b) else (if i < 1259 then decide (7 ≤ count1252 b) else decide (8 ≤ count1252 b)))) else (if i < 1263 then (if i < 1261 then decide (9 ≤ count1252 b) else (if i < 1262 then decide (10 ≤ count1252 b) else decide (11 ≤ count1252 b))) else (if i < 1265 then (if i < 1264 then decide (12 ≤ count1252 b) else decide (13 ≤ count1252 b)) else (if i < 1266 then decide (1 ≤ count1265 b) else decide (2 ≤ count1265 b)))))))) else (if i < 1316 then (if i < 1291 then (if i < 1279 then (if i < 1273 then (if i < 1270 then (if i < 1268 then decide (3 ≤ count1265 b) else (if i < 1269 then decide (4 ≤ count1265 b) else decide (5 ≤ count1265 b))) else (if i < 1271 then decide (6 ≤ count1265 b) else (if i < 1272 then decide (7 ≤ count1265 b) else decide (8 ≤ count1265 b)))) else (if i < 1276 then (if i < 1274 then decide (9 ≤ count1265 b) else (if i < 1275 then decide (10 ≤ count1265 b) else decide (11 ≤ count1265 b))) else (if i < 1277 then decide (12 ≤ count1265 b) else (if i < 1278 then decide (13 ≤ count1265 b) else decide (14 ≤ count1265 b))))) else (if i < 1285 then (if i < 1282 then (if i < 1280 then decide (15 ≤ count1265 b) else (if i < 1281 then decide (16 ≤ count1265 b) else decide (17 ≤ count1265 b))) else (if i < 1283 then decide (18 ≤ count1265 b) else (if i < 1284 then decide (19 ≤ count1265 b) else decide (20 ≤ count1265 b)))) else (if i < 1288 then (if i < 1286 then decide (21 ≤ count1265 b) else (if i < 1287 then decide (22 ≤ count1265 b) else decide (23 ≤ count1265 b))) else (if i < 1289 then decide (24 ≤ count1265 b) else (if i < 1290 then decide (25 ≤ count1265 b) else decide (26 ≤ count1265 b)))))) else (if i < 1303 then (if i < 1297 then (if i < 1294 then (if i < 1292 then decide (1 ≤ count1291 b) else (if i < 1293 then decide (2 ≤ count1291 b) else decide (3 ≤ count1291 b))) else (if i < 1295 then decide (4 ≤ count1291 b) else (if i < 1296 then decide (5 ≤ count1291 b) else decide (6 ≤ count1291 b)))) else (if i < 1300 then (if i < 1298 then decide (7 ≤ count1291 b) else (if i < 1299 then decide (8 ≤ count1291 b) else decide (9 ≤ count1291 b))) else (if i < 1301 then decide (10 ≤ count1291 b) else (if i < 1302 then decide (11 ≤ count1291 b) else decide (12 ≤ count1291 b))))) else (if i < 1309 then (if i < 1306 then (if i < 1304 then decide (13 ≤ count1291 b) else (if i < 1305 then decide (14 ≤ count1291 b) else decide (15 ≤ count1291 b))) else (if i < 1307 then decide (16 ≤ count1291 b) else (if i < 1308 then decide (17 ≤ count1291 b) else decide (18 ≤ count1291 b)))) else (if i < 1312 then (if i < 1310 then decide (19 ≤ count1291 b) else (if i < 1311 then decide (20 ≤ count1291 b) else decide (21 ≤ count1291 b))) else (if i < 1314 then (if i < 1313 then decide (22 ≤ count1291 b) else decide (23 ≤ count1291 b)) else (if i < 1315 then decide (24 ≤ count1291 b) else decide (25 ≤ count1291 b))))))) else (if i < 1340 then (if i < 1328 then (if i < 1322 then (if i < 1319 then (if i < 1317 then decide (26 ≤ count1291 b) else (if i < 1318 then decide (27 ≤ count1291 b) else decide (28 ≤ count1291 b))) else (if i < 1320 then decide (29 ≤ count1291 b) else (if i < 1321 then decide (30 ≤ count1291 b) else decide (31 ≤ count1291 b)))) else (if i < 1325 then (if i < 1323 then decide (32 ≤ count1291 b) else (if i < 1324 then decide (33 ≤ count1291 b) else decide (34 ≤ count1291 b))) else (if i < 1326 then decide (35 ≤ count1291 b) else (if i < 1327 then decide (36 ≤ count1291 b) else decide (37 ≤ count1291 b))))) else (if i < 1334 then (if i < 1331 then (if i < 1329 then decide (38 ≤ count1291 b) else (if i < 1330 then decide (39 ≤ count1291 b) else decide (40 ≤ count1291 b))) else (if i < 1332 then decide (41 ≤ count1291 b) else (if i < 1333 then decide (42 ≤ count1291 b) else decide (1 ≤ count1333 b)))) else (if i < 1337 then (if i < 1335 then decide (2 ≤ count1333 b) else (if i < 1336 then decide (1 ≤ count1335 b) else decide (2 ≤ count1335 b))) else (if i < 1338 then decide (3 ≤ count1335 b) else (if i < 1339 then decide (1 ≤ count1338 b) else decide (2 ≤ count1338 b)))))) else (if i < 1352 then (if i < 1346 then (if i < 1343 then (if i < 1341 then decide (1 ≤ count1340 b) else (if i < 1342 then decide (2 ≤ count1340 b) else decide (3 ≤ count1340 b))) else (if i < 1344 then decide (1 ≤ count1343 b) else (if i < 1345 then decide (2 ≤ count1343 b) else decide (3 ≤ count1343 b)))) else (if i < 1349 then (if i < 1347 then decide (4 ≤ count1343 b) else (if i < 1348 then decide (5 ≤ count1343 b) else decide (6 ≤ count1343 b))) else (if i < 1350 then decide (1 ≤ count1349 b) else (if i < 1351 then decide (2 ≤ count1349 b) else decide (1 ≤ count1351 b))))) else (if i < 1358 then (if i < 1355 then (if i < 1353 then decide (2 ≤ count1351 b) else (if i < 1354 then decide (3 ≤ count1351 b) else decide (1 ≤ count1354 b))) else (if i < 1356 then decide (2 ≤ count1354 b) else (if i < 1357 then decide (1 ≤ count1356 b) else decide (2 ≤ count1356 b)))) else (if i < 1361 then (if i < 1359 then decide (1 ≤ count1358 b) else (if i < 1360 then decide (2 ≤ count1358 b) else decide (3 ≤ count1358 b))) else (if i < 1363 then (if i < 1362 then decide (4 ≤ count1358 b) else decide (1 ≤ count1362 b)) else (if i < 1364 then decide (2 ≤ count1362 b) else decide (3 ≤ count1362 b))))))))) else (if i < 1463 then (if i < 1414 then (if i < 1389 then (if i < 1377 then (if i < 1371 then (if i < 1368 then (if i < 1366 then decide (4 ≤ count1362 b) else (if i < 1367 then decide (5 ≤ count1362 b) else decide (6 ≤ count1362 b))) else (if i < 1369 then decide (7 ≤ count1362 b) else (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)))) else (if i < 1374 then (if i < 1372 then decide (3 ≤ count1369 b) else (if i < 1373 then decide (4 ≤ count1369 b) else decide (5 ≤ count1369 b))) else (if i < 1375 then decide (6 ≤ count1369 b) else (if i < 1376 then decide (7 ≤ count1369 b) else decide (8 ≤ count1369 b))))) else (if i < 1383 then (if i < 1380 then (if i < 1378 then decide (9 ≤ count1369 b) else (if i < 1379 then decide (10 ≤ count1369 b) else decide (11 ≤ count1369 b))) else (if i < 1381 then decide (12 ≤ count1369 b) else (if i < 1382 then decide (1 ≤ count1381 b) else decide (2 ≤ count1381 b)))) else (if i < 1386 then (if i < 1384 then decide (1 ≤ count1383 b) else (if i < 1385 then decide (2 ≤ count1383 b) else decide (3 ≤ count1383 b))) else (if i < 1387 then decide (1 ≤ count1386 b) else (if i < 1388 then decide (2 ≤ count1386 b) else decide (1 ≤ count1388 b)))))) else (if i < 1401 then (if i < 1395 then (if i < 1392 then (if i < 1390 then decide (2 ≤ count1388 b) else (if i < 1391 then decide (3 ≤ count1388 b) else decide (1 ≤ count1391 b))) else (if i < 1393 then decide (2 ≤ count1391 b) else (if i < 1394 then decide (3 ≤ count1391 b) else decide (4 ≤ count1391 b)))) else (if i < 1398 then (if i < 1396 then decide (5 ≤ count1391 b) else (if i < 1397 then decide (6 ≤ count1391 b) else decide (1 ≤ count1397 b))) else (if i < 1399 then decide (2 ≤ count1397 b) else (if i < 1400 then decide (1 ≤ count1399 b) else decide (2 ≤ count1399 b))))) else (if i < 1407 then (if i < 1404 then (if i < 1402 then decide (3 ≤ count1399 b) else (if i < 1403 then decide (1 ≤ count1402 b) else decide (2 ≤ count1402 b))) else (if i < 1405 then decide (1 ≤ count1404 b) else (if i < 1406 then decide (2 ≤ count1404 b) else decide (1 ≤ count1406 b)))) else (if i < 1410 then (if i < 1408 then decide (2 ≤ count1406 b) else (if i < 1409 then decide (3 ≤ count1406 b) else decide (4 ≤ count1406 b))) else (if i < 1412 then (if i < 1411 then decide (1 ≤ count1410 b) else decide (2 ≤ count1410 b)) else (if i < 1413 then decide (3 ≤ count1410 b) else decide (4 ≤ count1410 b))))))) else (if i < 1438 then (if i < 1426 then (if i < 1420 then (if i < 1417 then (if i < 1415 then decide (5 ≤ count1410 b) else (if i < 1416 then decide (6 ≤ count1410 b) else decide (7 ≤ count1410 b))) else (if i < 1418 then decide (1 ≤ count1417 b) else (if i < 1419 then decide (2 ≤ count1417 b) else decide (3 ≤ count1417 b)))) else (if i < 1423 then (if i < 1421 then decide (4 ≤ count1417 b) else (if i < 1422 then decide (5 ≤ count1417 b) else decide (6 ≤ count1417 b))) else (if i < 1424 then decide (7 ≤ count1417 b) else (if i < 1425 then decide (8 ≤ count1417 b) else decide (9 ≤ count1417 b))))) else (if i < 1432 then (if i < 1429 then (if i < 1427 then decide (10 ≤ count1417 b) else (if i < 1428 then decide (11 ≤ count1417 b) else decide (12 ≤ count1417 b))) else (if i < 1430 then decide (1 ≤ count1429 b) else (if i < 1431 then decide (2 ≤ count1429 b) else decide (3 ≤ count1429 b)))) else (if i < 1435 then (if i < 1433 then decide (4 ≤ count1429 b) else (if i < 1434 then decide (5 ≤ count1429 b) else decide (6 ≤ count1429 b))) else (if i < 1436 then decide (7 ≤ count1429 b) else (if i < 1437 then decide (8 ≤ count1429 b) else decide (9 ≤ count1429 b)))))) else (if i < 1450 then (if i < 1444 then (if i < 1441 then (if i < 1439 then decide (10 ≤ count1429 b) else (if i < 1440 then decide (11 ≤ count1429 b) else decide (12 ≤ count1429 b))) else (if i < 1442 then decide (1 ≤ count1441 b) else (if i < 1443 then decide (2 ≤ count1441 b) else decide (1 ≤ count1443 b)))) else (if i < 1447 then (if i < 1445 then decide (2 ≤ count1443 b) else (if i < 1446 then decide (3 ≤ count1443 b) else decide (1 ≤ count1446 b))) else (if i < 1448 then decide (2 ≤ count1446 b) else (if i < 1449 then decide (1 ≤ count1448 b) else decide (2 ≤ count1448 b))))) else (if i < 1456 then (if i < 1453 then (if i < 1451 then decide (3 ≤ count1448 b) else (if i < 1452 then decide (1 ≤ count1451 b) else decide (2 ≤ count1451 b))) else (if i < 1454 then decide (3 ≤ count1451 b) else (if i < 1455 then decide (4 ≤ count1451 b) else decide (5 ≤ count1451 b)))) else (if i < 1459 then (if i < 1457 then decide (6 ≤ count1451 b) else (if i < 1458 then decide (1 ≤ count1457 b) else decide (2 ≤ count1457 b))) else (if i < 1461 then (if i < 1460 then decide (1 ≤ count1459 b) else decide (2 ≤ count1459 b)) else (if i < 1462 then decide (3 ≤ count1459 b) else decide (1 ≤ count1462 b)))))))) else (if i < 1512 then (if i < 1487 then (if i < 1475 then (if i < 1469 then (if i < 1466 then (if i < 1464 then decide (2 ≤ count1462 b) else (if i < 1465 then decide (1 ≤ count1464 b) else decide (2 ≤ count1464 b))) else (if i < 1467 then decide (1 ≤ count1466 b) else (if i < 1468 then decide (2 ≤ count1466 b) else decide (3 ≤ count1466 b)))) else (if i < 1472 then (if i < 1470 then decide (4 ≤ count1466 b) else (if i < 1471 then decide (1 ≤ count1470 b) else decide (2 ≤ count1470 b))) else (if i < 1473 then decide (3 ≤ count1470 b) else (if i < 1474 then decide (4 ≤ count1470 b) else decide (5 ≤ count1470 b))))) else (if i < 1481 then (if i < 1478 then (if i < 1476 then decide (6 ≤ count1470 b) else (if i < 1477 then decide (7 ≤ count1470 b) else decide (1 ≤ count1477 b))) else (if i < 1479 then decide (2 ≤ count1477 b) else (if i < 1480 then decide (3 ≤ count1477 b) else decide (4 ≤ count1477 b)))) else (if i < 1484 then (if i < 1482 then decide (5 ≤ count1477 b) else (if i < 1483 then decide (6 ≤ count1477 b) else decide (7 ≤ count1477 b))) else (if i < 1485 then decide (8 ≤ count1477 b) else (if i < 1486 then decide (9 ≤ count1477 b) else decide (10 ≤ count1477 b)))))) else (if i < 1499 then (if i < 1493 then (if i < 1490 then (if i < 1488 then decide (11 ≤ count1477 b) else (if i < 1489 then decide (12 ≤ count1477 b) else decide (1 ≤ count1489 b))) else (if i < 1491 then decide (2 ≤ count1489 b) else (if i < 1492 then decide (1 ≤ count1491 b) else decide (2 ≤ count1491 b)))) else (if i < 1496 then (if i < 1494 then decide (3 ≤ count1491 b) else (if i < 1495 then decide (1 ≤ count1494 b) else decide (2 ≤ count1494 b))) else (if i < 1497 then decide (1 ≤ count1496 b) else (if i < 1498 then decide (2 ≤ count1496 b) else decide (3 ≤ count1496 b))))) else (if i < 1505 then (if i < 1502 then (if i < 1500 then decide (1 ≤ count1499 b) else (if i < 1501 then decide (2 ≤ count1499 b) else decide (3 ≤ count1499 b))) else (if i < 1503 then decide (4 ≤ count1499 b) else (if i < 1504 then decide (5 ≤ count1499 b) else decide (6 ≤ count1499 b)))) else (if i < 1508 then (if i < 1506 then decide (1 ≤ count1505 b) else (if i < 1507 then decide (2 ≤ count1505 b) else decide (1 ≤ count1507 b))) else (if i < 1510 then (if i < 1509 then decide (2 ≤ count1507 b) else decide (3 ≤ count1507 b)) else (if i < 1511 then decide (1 ≤ count1510 b) else decide (2 ≤ count1510 b))))))) else (if i < 1536 then (if i < 1524 then (if i < 1518 then (if i < 1515 then (if i < 1513 then decide (1 ≤ count1512 b) else (if i < 1514 then decide (2 ≤ count1512 b) else decide (1 ≤ count1514 b))) else (if i < 1516 then decide (2 ≤ count1514 b) else (if i < 1517 then decide (3 ≤ count1514 b) else decide (4 ≤ count1514 b)))) else (if i < 1521 then (if i < 1519 then decide (1 ≤ count1518 b) else (if i < 1520 then decide (2 ≤ count1518 b) else decide (3 ≤ count1518 b))) else (if i < 1522 then decide (4 ≤ count1518 b) else (if i < 1523 then decide (5 ≤ count1518 b) else decide (6 ≤ count1518 b))))) else (if i < 1530 then (if i < 1527 then (if i < 1525 then decide (7 ≤ count1518 b) else (if i < 1526 then decide (1 ≤ count1525 b) else decide (2 ≤ count1525 b))) else (if i < 1528 then decide (3 ≤ count1525 b) else (if i < 1529 then decide (4 ≤ count1525 b) else decide (5 ≤ count1525 b)))) else (if i < 1533 then (if i < 1531 then decide (6 ≤ count1525 b) else (if i < 1532 then decide (7 ≤ count1525 b) else decide (8 ≤ count1525 b))) else (if i < 1534 then decide (9 ≤ count1525 b) else (if i < 1535 then decide (10 ≤ count1525 b) else decide (11 ≤ count1525 b)))))) else (if i < 1548 then (if i < 1542 then (if i < 1539 then (if i < 1537 then decide (12 ≤ count1525 b) else (if i < 1538 then decide (1 ≤ count1537 b) else decide (2 ≤ count1537 b))) else (if i < 1540 then decide (3 ≤ count1537 b) else (if i < 1541 then decide (4 ≤ count1537 b) else decide (5 ≤ count1537 b)))) else (if i < 1545 then (if i < 1543 then decide (6 ≤ count1537 b) else (if i < 1544 then decide (7 ≤ count1537 b) else decide (8 ≤ count1537 b))) else (if i < 1546 then decide (9 ≤ count1537 b) else (if i < 1547 then decide (10 ≤ count1537 b) else decide (11 ≤ count1537 b))))) else (if i < 1554 then (if i < 1551 then (if i < 1549 then decide (12 ≤ count1537 b) else (if i < 1550 then decide (1 ≤ count1549 b) else decide (2 ≤ count1549 b))) else (if i < 1552 then decide (3 ≤ count1549 b) else (if i < 1553 then decide (4 ≤ count1549 b) else decide (5 ≤ count1549 b)))) else (if i < 1557 then (if i < 1555 then decide (6 ≤ count1549 b) else (if i < 1556 then decide (7 ≤ count1549 b) else decide (8 ≤ count1549 b))) else (if i < 1559 then (if i < 1558 then decide (9 ≤ count1549 b) else decide (10 ≤ count1549 b)) else (if i < 1560 then decide (11 ≤ count1549 b) else decide (12 ≤ count1549 b))))))))))))
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
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (67 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (68 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (69 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (74 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (75 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (76 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (78 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (80 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (84 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (85 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (87 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (88 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (89 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (90 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (91 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (95 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (160 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (161 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (165 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (171 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (173 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (175 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (176 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (177 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (178 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (179 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (182 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (184 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (188 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (189 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (190 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (195 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (208 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (209 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (211 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (227 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (229 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (235 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (240 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (244 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (245 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (247 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (249 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (251 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (255 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (258 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (261 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (262 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (267 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (276 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (277 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (279 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (281 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (282 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (283 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (287 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (320 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (321 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (326 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (327 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (329 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (331 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (333 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (335 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (337 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (338 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (339 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (340 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (342 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (346 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (348 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (349 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (350 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (450 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (451 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (452 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (453 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (458 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (459 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (460 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (462 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (464 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (468 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (469 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (471 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (472 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (473 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (475 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (479 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (5 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (31 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (67 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (68 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (74 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (85 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (89 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (91 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (160 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (161 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (171 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (175 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (179 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (184 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (189 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (195 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (227 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (235 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (244 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (247 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (249 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (251 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (255 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (262 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (326 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (329 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (340 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (450 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (452 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (471 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (473 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (479 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (2 ≤ count247 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value266 (q : Snake 81) : valuation q 266 = decide (2 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value268 (q : Snake 81) : valuation q 268 = decide (2 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value280 (q : Snake 81) : valuation q 280 = decide (2 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value322 (q : Snake 81) : valuation q 322 = decide (2 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value326 (q : Snake 81) : valuation q 326 = decide (2 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value336 (q : Snake 81) : valuation q 336 = decide (2 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value350 (q : Snake 81) : valuation q 350 = decide (2 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value432 (q : Snake 81) : valuation q 432 = decide (2 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (1 ≤ count1333 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (2 ≤ count1333 (baseVal q)) := rfl
theorem value1335 (q : Snake 81) : valuation q 1335 = decide (1 ≤ count1335 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (2 ≤ count1335 (baseVal q)) := rfl
theorem value1337 (q : Snake 81) : valuation q 1337 = decide (3 ≤ count1335 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (1 ≤ count1338 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (2 ≤ count1338 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (2 ≤ count1340 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (1 ≤ count1343 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (2 ≤ count1343 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (3 ≤ count1343 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (4 ≤ count1343 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (2 ≤ count1349 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (1 ≤ count1351 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (2 ≤ count1351 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (1 ≤ count1354 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (2 ≤ count1354 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (1 ≤ count1356 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (2 ≤ count1356 (baseVal q)) := rfl
theorem value1358 (q : Snake 81) : valuation q 1358 = decide (1 ≤ count1358 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (2 ≤ count1358 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (3 ≤ count1358 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (4 ≤ count1358 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (1 ≤ count1362 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (2 ≤ count1362 (baseVal q)) := rfl
theorem value1364 (q : Snake 81) : valuation q 1364 = decide (3 ≤ count1362 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (4 ≤ count1362 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (1 ≤ count1369 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (2 ≤ count1369 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (3 ≤ count1369 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (4 ≤ count1369 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (5 ≤ count1369 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (6 ≤ count1369 (baseVal q)) := rfl
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
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (1 ≤ count1404 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (2 ≤ count1404 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (1 ≤ count1406 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (2 ≤ count1406 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (3 ≤ count1406 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (1 ≤ count1410 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (2 ≤ count1410 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (3 ≤ count1410 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (1 ≤ count1417 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (2 ≤ count1417 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (3 ≤ count1417 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (4 ≤ count1417 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (5 ≤ count1417 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (6 ≤ count1417 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (4 ≤ count1429 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (5 ≤ count1429 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (6 ≤ count1429 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (7 ≤ count1429 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (8 ≤ count1429 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (9 ≤ count1429 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (1 ≤ count1441 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (2 ≤ count1441 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (1 ≤ count1443 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (2 ≤ count1443 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (3 ≤ count1443 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (1 ≤ count1446 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (2 ≤ count1446 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (1 ≤ count1448 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (2 ≤ count1448 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (3 ≤ count1448 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (1 ≤ count1451 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (2 ≤ count1451 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (3 ≤ count1451 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (4 ≤ count1451 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (1 ≤ count1457 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (2 ≤ count1457 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (1 ≤ count1459 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (2 ≤ count1459 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (3 ≤ count1459 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (1 ≤ count1462 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (2 ≤ count1462 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (1 ≤ count1464 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (2 ≤ count1464 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (1 ≤ count1466 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (2 ≤ count1466 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (1 ≤ count1470 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (2 ≤ count1470 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (3 ≤ count1470 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (4 ≤ count1470 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (2 ≤ count1477 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (3 ≤ count1477 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (4 ≤ count1477 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (5 ≤ count1477 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (6 ≤ count1477 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (7 ≤ count1477 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (1 ≤ count1489 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (2 ≤ count1489 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (1 ≤ count1491 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (2 ≤ count1491 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (3 ≤ count1491 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (1 ≤ count1494 (baseVal q)) := rfl
theorem value1495 (q : Snake 81) : valuation q 1495 = decide (2 ≤ count1494 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (1 ≤ count1496 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (2 ≤ count1496 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (3 ≤ count1496 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (1 ≤ count1499 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (2 ≤ count1499 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (3 ≤ count1499 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (4 ≤ count1499 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (1 ≤ count1505 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (2 ≤ count1505 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (1 ≤ count1507 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (2 ≤ count1507 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (3 ≤ count1507 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (1 ≤ count1510 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (2 ≤ count1510 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (1 ≤ count1512 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (2 ≤ count1512 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (1 ≤ count1514 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (2 ≤ count1514 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (3 ≤ count1514 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (1 ≤ count1518 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (2 ≤ count1518 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (3 ≤ count1518 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (1 ≤ count1525 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (2 ≤ count1525 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (3 ≤ count1525 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (4 ≤ count1525 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (5 ≤ count1525 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (6 ≤ count1525 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (3 ≤ count1537 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (4 ≤ count1537 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (5 ≤ count1537 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (6 ≤ count1537 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (7 ≤ count1537 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (8 ≤ count1537 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (12 ≤ count1549 (baseVal q)) := rfl
theorem meaningNeg109 (b : Nat → Bool) : literal (valuationOf b) (-109) = decide (1 ≤ countLit b [-109]) := by
  change literal b (-109) = decide (1 ≤ countLit b [-109])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-109) <;> decide
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
theorem meaningNeg101 (b : Nat → Bool) : literal (valuationOf b) (-101) = decide (1 ≤ countLit b [-101]) := by
  change literal b (-101) = decide (1 ≤ countLit b [-101])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-101) <;> decide
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
theorem meaningNeg96 (b : Nat → Bool) : literal (valuationOf b) (-96) = decide (1 ≤ countLit b [-96]) := by
  change literal b (-96) = decide (1 ≤ countLit b [-96])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-96) <;> decide
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
theorem meaningNeg65 (b : Nat → Bool) : literal (valuationOf b) (-65) = decide (1 ≤ countLit b [-65]) := by
  change literal b (-65) = decide (1 ≤ countLit b [-65])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-65) <;> decide
theorem meaningNeg63 (b : Nat → Bool) : literal (valuationOf b) (-63) = decide (1 ≤ countLit b [-63]) := by
  change literal b (-63) = decide (1 ≤ countLit b [-63])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-63) <;> decide
theorem meaningNeg61 (b : Nat → Bool) : literal (valuationOf b) (-61) = decide (1 ≤ countLit b [-61]) := by
  change literal b (-61) = decide (1 ≤ countLit b [-61])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-61) <;> decide
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
theorem meaningNeg54 (b : Nat → Bool) : literal (valuationOf b) (-54) = decide (1 ≤ countLit b [-54]) := by
  change literal b (-54) = decide (1 ≤ countLit b [-54])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-54) <;> decide
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
theorem meaningNeg19 (b : Nat → Bool) : literal (valuationOf b) (-19) = decide (1 ≤ countLit b [-19]) := by
  change literal b (-19) = decide (1 ≤ countLit b [-19])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-19) <;> decide
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
theorem meaning112 (b : Nat → Bool) : literal (valuationOf b) (112) = decide (1 ≤ countLit b [112]) := by
  change literal b (112) = decide (1 ≤ countLit b [112])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (112) <;> decide
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
theorem meaning123 (b : Nat → Bool) : literal (valuationOf b) (123) = decide (1 ≤ countLit b [123]) := by
  change literal b (123) = decide (1 ≤ countLit b [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (123) <;> decide
theorem meaning124 (b : Nat → Bool) : literal (valuationOf b) (124) = decide (1 ≤ countLit b [124]) := by
  change literal b (124) = decide (1 ≤ countLit b [124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (124) <;> decide
theorem meaning126 (b : Nat → Bool) : literal (valuationOf b) (126) = decide (1 ≤ countLit b [126]) := by
  change literal b (126) = decide (1 ≤ countLit b [126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (126) <;> decide
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
theorem meaning141 (b : Nat → Bool) : literal (valuationOf b) (141) = decide (1 ≤ countLit b [141]) := by
  change literal b (141) = decide (1 ≤ countLit b [141])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (141) <;> decide
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
theorem meaning148 (b : Nat → Bool) : literal (valuationOf b) (148) = decide (1 ≤ countLit b [148]) := by
  change literal b (148) = decide (1 ≤ countLit b [148])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (148) <;> decide
theorem meaning150 (b : Nat → Bool) : literal (valuationOf b) (150) = decide (1 ≤ countLit b [150]) := by
  change literal b (150) = decide (1 ≤ countLit b [150])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (150) <;> decide
theorem meaning151 (b : Nat → Bool) : literal (valuationOf b) (151) = decide (1 ≤ countLit b [151]) := by
  change literal b (151) = decide (1 ≤ countLit b [151])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (151) <;> decide
theorem meaning156 (b : Nat → Bool) : literal (valuationOf b) (156) = decide (1 ≤ countLit b [156]) := by
  change literal b (156) = decide (1 ≤ countLit b [156])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (156) <;> decide
theorem meaning157 (b : Nat → Bool) : literal (valuationOf b) (157) = decide (1 ≤ countLit b [157]) := by
  change literal b (157) = decide (1 ≤ countLit b [157])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (157) <;> decide
theorem meaning166 (b : Nat → Bool) : literal (valuationOf b) (166) = decide (1 ≤ countLit b [166]) := by
  change literal b (166) = decide (1 ≤ countLit b [166])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (166) <;> decide
theorem meaning167 (b : Nat → Bool) : literal (valuationOf b) (167) = decide (1 ≤ countLit b [167]) := by
  change literal b (167) = decide (1 ≤ countLit b [167])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (167) <;> decide
theorem meaning168 (b : Nat → Bool) : literal (valuationOf b) (168) = decide (1 ≤ countLit b [168]) := by
  change literal b (168) = decide (1 ≤ countLit b [168])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (168) <;> decide
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
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
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
theorem meaning202 (b : Nat → Bool) : literal (valuationOf b) (202) = decide (1 ≤ countLit b [202]) := by
  change literal b (202) = decide (1 ≤ countLit b [202])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (202) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning208 (b : Nat → Bool) : literal (valuationOf b) (208) = decide (1 ≤ countLit b [208]) := by
  change literal b (208) = decide (1 ≤ countLit b [208])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (208) <;> decide
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) (211) = decide (1 ≤ countLit b [211]) := by
  change literal b (211) = decide (1 ≤ countLit b [211])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (211) <;> decide
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
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) (219) = decide (1 ≤ countLit b [219]) := by
  change literal b (219) = decide (1 ≤ countLit b [219])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (219) <;> decide
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning248 (b : Nat → Bool) : literal (valuationOf b) 248 = decide (2 ≤ count247 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning266 (b : Nat → Bool) : literal (valuationOf b) 266 = decide (2 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning268 (b : Nat → Bool) : literal (valuationOf b) 268 = decide (2 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning280 (b : Nat → Bool) : literal (valuationOf b) 280 = decide (2 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning322 (b : Nat → Bool) : literal (valuationOf b) 322 = decide (2 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning326 (b : Nat → Bool) : literal (valuationOf b) 326 = decide (2 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning336 (b : Nat → Bool) : literal (valuationOf b) 336 = decide (2 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning350 (b : Nat → Bool) : literal (valuationOf b) 350 = decide (2 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning402 (b : Nat → Bool) : literal (valuationOf b) 402 = decide (2 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning432 (b : Nat → Bool) : literal (valuationOf b) 432 = decide (2 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (1 ≤ count1333 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (2 ≤ count1333 b) := rfl
theorem meaning1335 (b : Nat → Bool) : literal (valuationOf b) 1335 = decide (1 ≤ count1335 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (2 ≤ count1335 b) := rfl
theorem meaning1337 (b : Nat → Bool) : literal (valuationOf b) 1337 = decide (3 ≤ count1335 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (1 ≤ count1338 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (2 ≤ count1338 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (2 ≤ count1340 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (1 ≤ count1343 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (2 ≤ count1343 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (3 ≤ count1343 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (4 ≤ count1343 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (2 ≤ count1349 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (1 ≤ count1351 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (2 ≤ count1351 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (1 ≤ count1354 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (2 ≤ count1354 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (1 ≤ count1356 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (2 ≤ count1356 b) := rfl
theorem meaning1358 (b : Nat → Bool) : literal (valuationOf b) 1358 = decide (1 ≤ count1358 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (2 ≤ count1358 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (3 ≤ count1358 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (4 ≤ count1358 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (1 ≤ count1362 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (2 ≤ count1362 b) := rfl
theorem meaning1364 (b : Nat → Bool) : literal (valuationOf b) 1364 = decide (3 ≤ count1362 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (4 ≤ count1362 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (1 ≤ count1369 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (2 ≤ count1369 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (3 ≤ count1369 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (4 ≤ count1369 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (5 ≤ count1369 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (6 ≤ count1369 b) := rfl
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
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (1 ≤ count1404 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (2 ≤ count1404 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (1 ≤ count1406 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (2 ≤ count1406 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (3 ≤ count1406 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (1 ≤ count1410 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (2 ≤ count1410 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (3 ≤ count1410 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (1 ≤ count1417 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (2 ≤ count1417 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (3 ≤ count1417 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (4 ≤ count1417 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (5 ≤ count1417 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (6 ≤ count1417 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (4 ≤ count1429 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (5 ≤ count1429 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (6 ≤ count1429 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (7 ≤ count1429 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (8 ≤ count1429 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (9 ≤ count1429 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (1 ≤ count1441 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (2 ≤ count1441 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (1 ≤ count1443 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (2 ≤ count1443 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (3 ≤ count1443 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (1 ≤ count1446 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (2 ≤ count1446 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (1 ≤ count1448 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (2 ≤ count1448 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (3 ≤ count1448 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (1 ≤ count1451 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (2 ≤ count1451 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (3 ≤ count1451 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (4 ≤ count1451 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (1 ≤ count1457 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (2 ≤ count1457 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (1 ≤ count1459 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (2 ≤ count1459 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (3 ≤ count1459 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (1 ≤ count1462 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (2 ≤ count1462 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (1 ≤ count1464 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (2 ≤ count1464 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (1 ≤ count1466 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (2 ≤ count1466 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (1 ≤ count1470 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (2 ≤ count1470 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (3 ≤ count1470 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (4 ≤ count1470 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (2 ≤ count1477 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (3 ≤ count1477 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (4 ≤ count1477 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (5 ≤ count1477 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (6 ≤ count1477 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (7 ≤ count1477 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (1 ≤ count1489 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (2 ≤ count1489 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (1 ≤ count1491 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (2 ≤ count1491 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (3 ≤ count1491 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (1 ≤ count1494 b) := rfl
theorem meaning1495 (b : Nat → Bool) : literal (valuationOf b) 1495 = decide (2 ≤ count1494 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (1 ≤ count1496 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (2 ≤ count1496 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (3 ≤ count1496 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (1 ≤ count1499 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (2 ≤ count1499 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (3 ≤ count1499 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (4 ≤ count1499 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (1 ≤ count1505 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (2 ≤ count1505 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (1 ≤ count1507 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (2 ≤ count1507 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (3 ≤ count1507 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (1 ≤ count1510 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (2 ≤ count1510 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (1 ≤ count1512 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (2 ≤ count1512 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (1 ≤ count1514 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (2 ≤ count1514 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (3 ≤ count1514 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (1 ≤ count1518 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (2 ≤ count1518 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (3 ≤ count1518 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (1 ≤ count1525 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (2 ≤ count1525 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (3 ≤ count1525 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (4 ≤ count1525 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (5 ≤ count1525 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (6 ≤ count1525 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (3 ≤ count1537 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (4 ≤ count1537 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (5 ≤ count1537 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (6 ≤ count1537 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (7 ≤ count1537 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (8 ≤ count1537 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (12 ≤ count1549 b) := rfl
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
end Snake9.Regrowth.E112183
