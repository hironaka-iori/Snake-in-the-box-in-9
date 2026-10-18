import E112166Data
namespace Snake9.Regrowth.E112166
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 109 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (5 : Vertex)) else decide (InPath q (11 : Vertex)))) else (if i < 4 then decide (InPath q (13 : Vertex)) else (if i < 5 then decide (InPath q (17 : Vertex)) else decide (InPath q (21 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (23 : Vertex)) else (if i < 8 then decide (InPath q (25 : Vertex)) else decide (InPath q (26 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (27 : Vertex)) else decide (InPath q (45 : Vertex))) else (if i < 12 then decide (InPath q (109 : Vertex)) else decide (InPath q (160 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (162 : Vertex)) else (if i < 15 then decide (InPath q (164 : Vertex)) else decide (InPath q (165 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (170 : Vertex)) else decide (InPath q (171 : Vertex))) else (if i < 19 then decide (InPath q (172 : Vertex)) else decide (InPath q (173 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (177 : Vertex)) else (if i < 22 then decide (InPath q (181 : Vertex)) else decide (InPath q (182 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (183 : Vertex)) else decide (InPath q (185 : Vertex))) else (if i < 26 then decide (InPath q (186 : Vertex)) else decide (InPath q (187 : Vertex))))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then decide (InPath q (192 : Vertex)) else (if i < 29 then decide (InPath q (194 : Vertex)) else decide (InPath q (196 : Vertex)))) else (if i < 31 then decide (InPath q (197 : Vertex)) else (if i < 32 then decide (InPath q (202 : Vertex)) else decide (InPath q (203 : Vertex))))) else (if i < 36 then (if i < 34 then decide (InPath q (204 : Vertex)) else (if i < 35 then decide (InPath q (205 : Vertex)) else decide (InPath q (209 : Vertex)))) else (if i < 38 then (if i < 37 then decide (InPath q (213 : Vertex)) else decide (InPath q (214 : Vertex))) else (if i < 39 then decide (InPath q (215 : Vertex)) else decide (InPath q (217 : Vertex)))))) else (if i < 47 then (if i < 43 then (if i < 41 then decide (InPath q (218 : Vertex)) else (if i < 42 then decide (InPath q (219 : Vertex)) else decide (InPath q (222 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (257 : Vertex)) else decide (InPath q (259 : Vertex))) else (if i < 46 then decide (InPath q (261 : Vertex)) else decide (InPath q (267 : Vertex))))) else (if i < 50 then (if i < 48 then decide (InPath q (268 : Vertex)) else (if i < 49 then decide (InPath q (269 : Vertex)) else decide (InPath q (270 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (271 : Vertex)) else decide (InPath q (272 : Vertex))) else (if i < 53 then decide (InPath q (273 : Vertex)) else decide (InPath q (274 : Vertex)))))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then decide (InPath q (275 : Vertex)) else (if i < 56 then decide (InPath q (278 : Vertex)) else decide (InPath q (280 : Vertex)))) else (if i < 58 then decide (InPath q (284 : Vertex)) else (if i < 59 then decide (InPath q (285 : Vertex)) else decide (InPath q (286 : Vertex))))) else (if i < 63 then (if i < 61 then decide (InPath q (287 : Vertex)) else (if i < 62 then decide (InPath q (320 : Vertex)) else decide (InPath q (322 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (324 : Vertex)) else decide (InPath q (325 : Vertex))) else (if i < 66 then decide (InPath q (330 : Vertex)) else decide (InPath q (331 : Vertex)))))) else (if i < 74 then (if i < 70 then (if i < 68 then decide (InPath q (332 : Vertex)) else (if i < 69 then decide (InPath q (333 : Vertex)) else decide (InPath q (337 : Vertex)))) else (if i < 72 then (if i < 71 then decide (InPath q (341 : Vertex)) else decide (InPath q (342 : Vertex))) else (if i < 73 then decide (InPath q (343 : Vertex)) else decide (InPath q (345 : Vertex))))) else (if i < 77 then (if i < 75 then decide (InPath q (346 : Vertex)) else (if i < 76 then decide (InPath q (347 : Vertex)) else decide (InPath q (350 : Vertex)))) else (if i < 79 then (if i < 78 then decide (InPath q (417 : Vertex)) else decide (InPath q (419 : Vertex))) else (if i < 80 then decide (InPath q (421 : Vertex)) else decide (InPath q (427 : Vertex))))))) else (if i < 95 then (if i < 88 then (if i < 84 then (if i < 82 then decide (InPath q (428 : Vertex)) else (if i < 83 then decide (InPath q (429 : Vertex)) else decide (InPath q (430 : Vertex)))) else (if i < 86 then (if i < 85 then decide (InPath q (431 : Vertex)) else decide (InPath q (432 : Vertex))) else (if i < 87 then decide (InPath q (433 : Vertex)) else decide (InPath q (434 : Vertex))))) else (if i < 91 then (if i < 89 then decide (InPath q (435 : Vertex)) else (if i < 90 then decide (InPath q (438 : Vertex)) else decide (InPath q (440 : Vertex)))) else (if i < 93 then (if i < 92 then decide (InPath q (444 : Vertex)) else decide (InPath q (445 : Vertex))) else (if i < 94 then decide (InPath q (446 : Vertex)) else decide (InPath q (447 : Vertex)))))) else (if i < 102 then (if i < 98 then (if i < 96 then decide (InPath q (461 : Vertex)) else (if i < 97 then decide (InPath q (462 : Vertex)) else decide (InPath q (477 : Vertex)))) else (if i < 100 then (if i < 99 then decide (InPath q (478 : Vertex)) else decide (InPath q (479 : Vertex))) else (if i < 101 then decide (InPath q (485 : Vertex)) else decide (InPath q (491 : Vertex))))) else (if i < 105 then (if i < 103 then decide (InPath q (493 : Vertex)) else (if i < 104 then decide (InPath q (497 : Vertex)) else decide (InPath q (501 : Vertex)))) else (if i < 107 then (if i < 106 then decide (InPath q (503 : Vertex)) else decide (InPath q (505 : Vertex))) else (if i < 108 then decide (InPath q (506 : Vertex)) else decide (InPath q (507 : Vertex))))))))) else (if i < 164 then (if i < 136 then (if i < 122 then (if i < 115 then (if i < 112 then (if i < 110 then decide (InPath q (510 : Vertex)) else (if i < 111 then decide (BallClauseLogic.Endpoint q (5 : Vertex)) else decide (BallClauseLogic.Endpoint q (11 : Vertex)))) else (if i < 113 then decide (BallClauseLogic.Endpoint q (13 : Vertex)) else (if i < 114 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (21 : Vertex))))) else (if i < 118 then (if i < 116 then decide (BallClauseLogic.Endpoint q (23 : Vertex)) else (if i < 117 then decide (BallClauseLogic.Endpoint q (25 : Vertex)) else decide (BallClauseLogic.Endpoint q (26 : Vertex)))) else (if i < 120 then (if i < 119 then decide (BallClauseLogic.Endpoint q (27 : Vertex)) else decide (BallClauseLogic.Endpoint q (45 : Vertex))) else (if i < 121 then decide (BallClauseLogic.Endpoint q (109 : Vertex)) else decide (BallClauseLogic.Endpoint q (160 : Vertex)))))) else (if i < 129 then (if i < 125 then (if i < 123 then decide (BallClauseLogic.Endpoint q (162 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (164 : Vertex)) else decide (BallClauseLogic.Endpoint q (165 : Vertex)))) else (if i < 127 then (if i < 126 then decide (BallClauseLogic.Endpoint q (170 : Vertex)) else decide (BallClauseLogic.Endpoint q (171 : Vertex))) else (if i < 128 then decide (BallClauseLogic.Endpoint q (172 : Vertex)) else decide (BallClauseLogic.Endpoint q (173 : Vertex))))) else (if i < 132 then (if i < 130 then decide (BallClauseLogic.Endpoint q (177 : Vertex)) else (if i < 131 then decide (BallClauseLogic.Endpoint q (181 : Vertex)) else decide (BallClauseLogic.Endpoint q (182 : Vertex)))) else (if i < 134 then (if i < 133 then decide (BallClauseLogic.Endpoint q (183 : Vertex)) else decide (BallClauseLogic.Endpoint q (185 : Vertex))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (186 : Vertex)) else decide (BallClauseLogic.Endpoint q (187 : Vertex))))))) else (if i < 150 then (if i < 143 then (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (194 : Vertex)) else decide (BallClauseLogic.Endpoint q (196 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (197 : Vertex)) else decide (BallClauseLogic.Endpoint q (202 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (203 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex))))) else (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (205 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else decide (BallClauseLogic.Endpoint q (213 : Vertex)))) else (if i < 148 then (if i < 147 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (215 : Vertex))) else (if i < 149 then decide (BallClauseLogic.Endpoint q (217 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex)))))) else (if i < 157 then (if i < 153 then (if i < 151 then decide (BallClauseLogic.Endpoint q (219 : Vertex)) else (if i < 152 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else decide (BallClauseLogic.Endpoint q (257 : Vertex)))) else (if i < 155 then (if i < 154 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (267 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex))))) else (if i < 160 then (if i < 158 then decide (BallClauseLogic.Endpoint q (269 : Vertex)) else (if i < 159 then decide (BallClauseLogic.Endpoint q (270 : Vertex)) else decide (BallClauseLogic.Endpoint q (271 : Vertex)))) else (if i < 162 then (if i < 161 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (273 : Vertex))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (274 : Vertex)) else decide (BallClauseLogic.Endpoint q (275 : Vertex)))))))) else (if i < 191 then (if i < 177 then (if i < 170 then (if i < 167 then (if i < 165 then decide (BallClauseLogic.Endpoint q (278 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else decide (BallClauseLogic.Endpoint q (284 : Vertex)))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (285 : Vertex)) else (if i < 169 then decide (BallClauseLogic.Endpoint q (286 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex))))) else (if i < 173 then (if i < 171 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else (if i < 172 then decide (BallClauseLogic.Endpoint q (322 : Vertex)) else decide (BallClauseLogic.Endpoint q (324 : Vertex)))) else (if i < 175 then (if i < 174 then decide (BallClauseLogic.Endpoint q (325 : Vertex)) else decide (BallClauseLogic.Endpoint q (330 : Vertex))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (331 : Vertex)) else decide (BallClauseLogic.Endpoint q (332 : Vertex)))))) else (if i < 184 then (if i < 180 then (if i < 178 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else (if i < 179 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (341 : Vertex)))) else (if i < 182 then (if i < 181 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (343 : Vertex))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (345 : Vertex)) else decide (BallClauseLogic.Endpoint q (346 : Vertex))))) else (if i < 187 then (if i < 185 then decide (BallClauseLogic.Endpoint q (347 : Vertex)) else (if i < 186 then decide (BallClauseLogic.Endpoint q (350 : Vertex)) else decide (BallClauseLogic.Endpoint q (417 : Vertex)))) else (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (419 : Vertex)) else decide (BallClauseLogic.Endpoint q (421 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (427 : Vertex)) else decide (BallClauseLogic.Endpoint q (428 : Vertex))))))) else (if i < 205 then (if i < 198 then (if i < 194 then (if i < 192 then decide (BallClauseLogic.Endpoint q (429 : Vertex)) else (if i < 193 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (431 : Vertex)))) else (if i < 196 then (if i < 195 then decide (BallClauseLogic.Endpoint q (432 : Vertex)) else decide (BallClauseLogic.Endpoint q (433 : Vertex))) else (if i < 197 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex))))) else (if i < 201 then (if i < 199 then decide (BallClauseLogic.Endpoint q (438 : Vertex)) else (if i < 200 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (444 : Vertex)))) else (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (445 : Vertex)) else decide (BallClauseLogic.Endpoint q (446 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (447 : Vertex)) else decide (BallClauseLogic.Endpoint q (461 : Vertex)))))) else (if i < 212 then (if i < 208 then (if i < 206 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else (if i < 207 then decide (BallClauseLogic.Endpoint q (477 : Vertex)) else decide (BallClauseLogic.Endpoint q (478 : Vertex)))) else (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (479 : Vertex)) else decide (BallClauseLogic.Endpoint q (485 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))))) else (if i < 215 then (if i < 213 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else (if i < 214 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else decide (BallClauseLogic.Endpoint q (503 : Vertex)))) else (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (505 : Vertex)) else decide (BallClauseLogic.Endpoint q (506 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (507 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count219 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count221 (b : Nat → Bool) : Nat := countLit b [110, 111, 112]
def count223 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count225 (b : Nat → Bool) : Nat := countLit b [113, 114, 115]
def count227 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115]
def count229 (b : Nat → Bool) : Nat := countLit b [117, 118]
def count231 (b : Nat → Bool) : Nat := countLit b [116, 117, 118]
def count233 (b : Nat → Bool) : Nat := countLit b [119, 121]
def count235 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count237 (b : Nat → Bool) : Nat := countLit b [119, 121, 122, 123]
def count239 (b : Nat → Bool) : Nat := countLit b [116, 117, 118, 119, 121, 122, 123]
def count241 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123]
def count243 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count245 (b : Nat → Bool) : Nat := countLit b [124, 125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count249 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count251 (b : Nat → Bool) : Nat := countLit b [127, 128, 129, 130]
def count253 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130]
def count255 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count257 (b : Nat → Bool) : Nat := countLit b [131, 132, 133]
def count259 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count261 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137]
def count265 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134, 135, 136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count277 (b : Nat → Bool) : Nat := countLit b [141, 142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count283 (b : Nat → Bool) : Nat := countLit b [144, 145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count287 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count289 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150]
def count291 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count303 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157]
def count305 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154, 155, 156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 159, 160]
def count311 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count313 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count315 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164]
def count317 (b : Nat → Bool) : Nat := countLit b [158, 159, 160, 161, 162, 163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
def count325 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [171, 172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count343 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [178, 179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184]
def count359 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [185, 186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count367 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191]
def count371 (b : Nat → Bool) : Nat := countLit b [185, 186, 187, 188, 189, 190, 191]
def count373 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]
def count377 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [192, 193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count383 (b : Nat → Bool) : Nat := countLit b [195, 196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count389 (b : Nat → Bool) : Nat := countLit b [198, 199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count393 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count395 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count403 (b : Nat → Bool) : Nat := countLit b [205, 206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count409 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211]
def count411 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count415 (b : Nat → Bool) : Nat := countLit b [212, 213, 214]
def count417 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count419 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count421 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218]
def count423 (b : Nat → Bool) : Nat := countLit b [212, 213, 214, 215, 216, 217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count429 (b : Nat → Bool) : Nat := countLit b [165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count431 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count433 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count435 (b : Nat → Bool) : Nat := countLit b [1, 4, 6]
def count438 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count440 (b : Nat → Bool) : Nat := countLit b [9, 10, 12]
def count443 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 9, 10, 12]
def count449 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count451 (b : Nat → Bool) : Nat := countLit b [15, 16, 18]
def count454 (b : Nat → Bool) : Nat := countLit b [20, 23]
def count456 (b : Nat → Bool) : Nat := countLit b [26, 27]
def count458 (b : Nat → Bool) : Nat := countLit b [20, 23, 26, 27]
def count462 (b : Nat → Bool) : Nat := countLit b [15, 16, 18, 20, 23, 26, 27]
def count469 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 9, 10, 12, 15, 16, 18, 20, 23, 26, 27]
def count482 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count484 (b : Nat → Bool) : Nat := countLit b [30, 31, 33]
def count487 (b : Nat → Bool) : Nat := countLit b [35, 38]
def count489 (b : Nat → Bool) : Nat := countLit b [41, 42]
def count491 (b : Nat → Bool) : Nat := countLit b [35, 38, 41, 42]
def count495 (b : Nat → Bool) : Nat := countLit b [30, 31, 33, 35, 38, 41, 42]
def count502 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count504 (b : Nat → Bool) : Nat := countLit b [43, 46, 48]
def count507 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count509 (b : Nat → Bool) : Nat := countLit b [54, 55]
def count511 (b : Nat → Bool) : Nat := countLit b [49, 51, 54, 55]
def count515 (b : Nat → Bool) : Nat := countLit b [43, 46, 48, 49, 51, 54, 55]
def count522 (b : Nat → Bool) : Nat := countLit b [30, 31, 33, 35, 38, 41, 42, 43, 46, 48, 49, 51, 54, 55]
def count536 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 9, 10, 12, 15, 16, 18, 20, 23, 26, 27, 30, 31, 33, 35, 38, 41, 42, 43, 46, 48, 49, 51, 54, 55]
def count563 (b : Nat → Bool) : Nat := countLit b [60, 61]
def count565 (b : Nat → Bool) : Nat := countLit b [57, 60, 61]
def count568 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count570 (b : Nat → Bool) : Nat := countLit b [64, 65, 67]
def count573 (b : Nat → Bool) : Nat := countLit b [57, 60, 61, 64, 65, 67]
def count579 (b : Nat → Bool) : Nat := countLit b [72, 75]
def count581 (b : Nat → Bool) : Nat := countLit b [69, 72, 75]
def count584 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count586 (b : Nat → Bool) : Nat := countLit b [80, 82]
def count588 (b : Nat → Bool) : Nat := countLit b [76, 77, 80, 82]
def count592 (b : Nat → Bool) : Nat := countLit b [69, 72, 75, 76, 77, 80, 82]
def count599 (b : Nat → Bool) : Nat := countLit b [57, 60, 61, 64, 65, 67, 69, 72, 75, 76, 77, 80, 82]
def count612 (b : Nat → Bool) : Nat := countLit b [85, 88]
def count614 (b : Nat → Bool) : Nat := countLit b [83, 85, 88]
def count617 (b : Nat → Bool) : Nat := countLit b [89, 91]
def count619 (b : Nat → Bool) : Nat := countLit b [94, 95]
def count621 (b : Nat → Bool) : Nat := countLit b [89, 91, 94, 95]
def count625 (b : Nat → Bool) : Nat := countLit b [83, 85, 88, 89, 91, 94, 95]
def count632 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count634 (b : Nat → Bool) : Nat := countLit b [96, 99, 100]
def count637 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count639 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count641 (b : Nat → Bool) : Nat := countLit b [103, 105, 108, 109]
def count645 (b : Nat → Bool) : Nat := countLit b [96, 99, 100, 103, 105, 108, 109]
def count652 (b : Nat → Bool) : Nat := countLit b [83, 85, 88, 89, 91, 94, 95, 96, 99, 100, 103, 105, 108, 109]
def count666 (b : Nat → Bool) : Nat := countLit b [57, 60, 61, 64, 65, 67, 69, 72, 75, 76, 77, 80, 82, 83, 85, 88, 89, 91, 94, 95, 96, 99, 100, 103, 105, 108, 109]
def count693 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 9, 10, 12, 15, 16, 18, 20, 23, 26, 27, 30, 31, 33, 35, 38, 41, 42, 43, 46, 48, 49, 51, 54, 55, 57, 60, 61, 64, 65, 67, 69, 72, 75, 76, 77, 80, 82, 83, 85, 88, 89, 91, 94, 95, 96, 99, 100, 103, 105, 108, 109]
def count735 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count737 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6]
def count740 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count742 (b : Nat → Bool) : Nat := countLit b [-9, -10, -12]
def count745 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -9, -10, -12]
def count751 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count753 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18]
def count756 (b : Nat → Bool) : Nat := countLit b [-20, -23]
def count758 (b : Nat → Bool) : Nat := countLit b [-26, -27]
def count760 (b : Nat → Bool) : Nat := countLit b [-20, -23, -26, -27]
def count764 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18, -20, -23, -26, -27]
def count771 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -9, -10, -12, -15, -16, -18, -20, -23, -26, -27]
def count784 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count786 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33]
def count789 (b : Nat → Bool) : Nat := countLit b [-35, -38]
def count791 (b : Nat → Bool) : Nat := countLit b [-41, -42]
def count793 (b : Nat → Bool) : Nat := countLit b [-35, -38, -41, -42]
def count797 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33, -35, -38, -41, -42]
def count804 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count806 (b : Nat → Bool) : Nat := countLit b [-43, -46, -48]
def count809 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count811 (b : Nat → Bool) : Nat := countLit b [-54, -55]
def count813 (b : Nat → Bool) : Nat := countLit b [-49, -51, -54, -55]
def count817 (b : Nat → Bool) : Nat := countLit b [-43, -46, -48, -49, -51, -54, -55]
def count824 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33, -35, -38, -41, -42, -43, -46, -48, -49, -51, -54, -55]
def count838 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -9, -10, -12, -15, -16, -18, -20, -23, -26, -27, -30, -31, -33, -35, -38, -41, -42, -43, -46, -48, -49, -51, -54, -55]
def count852 (b : Nat → Bool) : Nat := countLit b [-60, -61]
def count854 (b : Nat → Bool) : Nat := countLit b [-57, -60, -61]
def count857 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count859 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67]
def count862 (b : Nat → Bool) : Nat := countLit b [-57, -60, -61, -64, -65, -67]
def count868 (b : Nat → Bool) : Nat := countLit b [-72, -75]
def count870 (b : Nat → Bool) : Nat := countLit b [-69, -72, -75]
def count873 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count875 (b : Nat → Bool) : Nat := countLit b [-80, -82]
def count877 (b : Nat → Bool) : Nat := countLit b [-76, -77, -80, -82]
def count881 (b : Nat → Bool) : Nat := countLit b [-69, -72, -75, -76, -77, -80, -82]
def count888 (b : Nat → Bool) : Nat := countLit b [-57, -60, -61, -64, -65, -67, -69, -72, -75, -76, -77, -80, -82]
def count901 (b : Nat → Bool) : Nat := countLit b [-85, -88]
def count903 (b : Nat → Bool) : Nat := countLit b [-83, -85, -88]
def count906 (b : Nat → Bool) : Nat := countLit b [-89, -91]
def count908 (b : Nat → Bool) : Nat := countLit b [-94, -95]
def count910 (b : Nat → Bool) : Nat := countLit b [-89, -91, -94, -95]
def count914 (b : Nat → Bool) : Nat := countLit b [-83, -85, -88, -89, -91, -94, -95]
def count921 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count923 (b : Nat → Bool) : Nat := countLit b [-96, -99, -100]
def count926 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count928 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count930 (b : Nat → Bool) : Nat := countLit b [-103, -105, -108, -109]
def count934 (b : Nat → Bool) : Nat := countLit b [-96, -99, -100, -103, -105, -108, -109]
def count941 (b : Nat → Bool) : Nat := countLit b [-83, -85, -88, -89, -91, -94, -95, -96, -99, -100, -103, -105, -108, -109]
def count955 (b : Nat → Bool) : Nat := countLit b [-57, -60, -61, -64, -65, -67, -69, -72, -75, -76, -77, -80, -82, -83, -85, -88, -89, -91, -94, -95, -96, -99, -100, -103, -105, -108, -109]
def count969 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -9, -10, -12, -15, -16, -18, -20, -23, -26, -27, -30, -31, -33, -35, -38, -41, -42, -43, -46, -48, -49, -51, -54, -55, -57, -60, -61, -64, -65, -67, -69, -72, -75, -76, -77, -80, -82, -83, -85, -88, -89, -91, -94, -95, -96, -99, -100, -103, -105, -108, -109]
def count983 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count985 (b : Nat → Bool) : Nat := countLit b [2, 3, 5]
def count988 (b : Nat → Bool) : Nat := countLit b [8, 11]
def count990 (b : Nat → Bool) : Nat := countLit b [7, 8, 11]
def count993 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 8, 11]
def count999 (b : Nat → Bool) : Nat := countLit b [14, 17]
def count1001 (b : Nat → Bool) : Nat := countLit b [13, 14, 17]
def count1004 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count1006 (b : Nat → Bool) : Nat := countLit b [22, 24]
def count1008 (b : Nat → Bool) : Nat := countLit b [19, 21, 22, 24]
def count1012 (b : Nat → Bool) : Nat := countLit b [13, 14, 17, 19, 21, 22, 24]
def count1019 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 8, 11, 13, 14, 17, 19, 21, 22, 24]
def count1032 (b : Nat → Bool) : Nat := countLit b [28, 29]
def count1034 (b : Nat → Bool) : Nat := countLit b [25, 28, 29]
def count1037 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count1039 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count1041 (b : Nat → Bool) : Nat := countLit b [32, 34, 36, 37]
def count1045 (b : Nat → Bool) : Nat := countLit b [25, 28, 29, 32, 34, 36, 37]
def count1052 (b : Nat → Bool) : Nat := countLit b [40, 44]
def count1054 (b : Nat → Bool) : Nat := countLit b [39, 40, 44]
def count1057 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count1059 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count1061 (b : Nat → Bool) : Nat := countLit b [45, 47, 50, 52]
def count1065 (b : Nat → Bool) : Nat := countLit b [39, 40, 44, 45, 47, 50, 52]
def count1072 (b : Nat → Bool) : Nat := countLit b [25, 28, 29, 32, 34, 36, 37, 39, 40, 44, 45, 47, 50, 52]
def count1086 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 8, 11, 13, 14, 17, 19, 21, 22, 24, 25, 28, 29, 32, 34, 36, 37, 39, 40, 44, 45, 47, 50, 52]
def count1113 (b : Nat → Bool) : Nat := countLit b [56, 58]
def count1115 (b : Nat → Bool) : Nat := countLit b [53, 56, 58]
def count1118 (b : Nat → Bool) : Nat := countLit b [59, 62]
def count1120 (b : Nat → Bool) : Nat := countLit b [63, 66]
def count1122 (b : Nat → Bool) : Nat := countLit b [59, 62, 63, 66]
def count1126 (b : Nat → Bool) : Nat := countLit b [53, 56, 58, 59, 62, 63, 66]
def count1133 (b : Nat → Bool) : Nat := countLit b [70, 71]
def count1135 (b : Nat → Bool) : Nat := countLit b [68, 70, 71]
def count1138 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count1140 (b : Nat → Bool) : Nat := countLit b [78, 79]
def count1142 (b : Nat → Bool) : Nat := countLit b [73, 74, 78, 79]
def count1146 (b : Nat → Bool) : Nat := countLit b [68, 70, 71, 73, 74, 78, 79]
def count1153 (b : Nat → Bool) : Nat := countLit b [53, 56, 58, 59, 62, 63, 66, 68, 70, 71, 73, 74, 78, 79]
def count1167 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count1169 (b : Nat → Bool) : Nat := countLit b [81, 84, 86]
def count1172 (b : Nat → Bool) : Nat := countLit b [87, 90]
def count1174 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count1176 (b : Nat → Bool) : Nat := countLit b [87, 90, 92, 93]
def count1180 (b : Nat → Bool) : Nat := countLit b [81, 84, 86, 87, 90, 92, 93]
def count1187 (b : Nat → Bool) : Nat := countLit b [98, 101]
def count1189 (b : Nat → Bool) : Nat := countLit b [97, 98, 101]
def count1192 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count1194 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count1196 (b : Nat → Bool) : Nat := countLit b [102, 104, 106, 107]
def count1200 (b : Nat → Bool) : Nat := countLit b [97, 98, 101, 102, 104, 106, 107]
def count1207 (b : Nat → Bool) : Nat := countLit b [81, 84, 86, 87, 90, 92, 93, 97, 98, 101, 102, 104, 106, 107]
def count1221 (b : Nat → Bool) : Nat := countLit b [53, 56, 58, 59, 62, 63, 66, 68, 70, 71, 73, 74, 78, 79, 81, 84, 86, 87, 90, 92, 93, 97, 98, 101, 102, 104, 106, 107]
def count1249 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 7, 8, 11, 13, 14, 17, 19, 21, 22, 24, 25, 28, 29, 32, 34, 36, 37, 39, 40, 44, 45, 47, 50, 52, 53, 56, 58, 59, 62, 63, 66, 68, 70, 71, 73, 74, 78, 79, 81, 84, 86, 87, 90, 92, 93, 97, 98, 101, 102, 104, 106, 107]
def count1291 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1293 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5]
def count1296 (b : Nat → Bool) : Nat := countLit b [-8, -11]
def count1298 (b : Nat → Bool) : Nat := countLit b [-7, -8, -11]
def count1301 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -8, -11]
def count1307 (b : Nat → Bool) : Nat := countLit b [-14, -17]
def count1309 (b : Nat → Bool) : Nat := countLit b [-13, -14, -17]
def count1312 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count1314 (b : Nat → Bool) : Nat := countLit b [-22, -24]
def count1316 (b : Nat → Bool) : Nat := countLit b [-19, -21, -22, -24]
def count1320 (b : Nat → Bool) : Nat := countLit b [-13, -14, -17, -19, -21, -22, -24]
def count1327 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]
def count1340 (b : Nat → Bool) : Nat := countLit b [-28, -29]
def count1342 (b : Nat → Bool) : Nat := countLit b [-25, -28, -29]
def count1345 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count1347 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count1349 (b : Nat → Bool) : Nat := countLit b [-32, -34, -36, -37]
def count1353 (b : Nat → Bool) : Nat := countLit b [-25, -28, -29, -32, -34, -36, -37]
def count1360 (b : Nat → Bool) : Nat := countLit b [-40, -44]
def count1362 (b : Nat → Bool) : Nat := countLit b [-39, -40, -44]
def count1365 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count1367 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count1369 (b : Nat → Bool) : Nat := countLit b [-45, -47, -50, -52]
def count1373 (b : Nat → Bool) : Nat := countLit b [-39, -40, -44, -45, -47, -50, -52]
def count1380 (b : Nat → Bool) : Nat := countLit b [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]
def count1394 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]
def count1409 (b : Nat → Bool) : Nat := countLit b [-56, -58]
def count1411 (b : Nat → Bool) : Nat := countLit b [-53, -56, -58]
def count1414 (b : Nat → Bool) : Nat := countLit b [-59, -62]
def count1416 (b : Nat → Bool) : Nat := countLit b [-63, -66]
def count1418 (b : Nat → Bool) : Nat := countLit b [-59, -62, -63, -66]
def count1422 (b : Nat → Bool) : Nat := countLit b [-53, -56, -58, -59, -62, -63, -66]
def count1429 (b : Nat → Bool) : Nat := countLit b [-70, -71]
def count1431 (b : Nat → Bool) : Nat := countLit b [-68, -70, -71]
def count1434 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count1436 (b : Nat → Bool) : Nat := countLit b [-78, -79]
def count1438 (b : Nat → Bool) : Nat := countLit b [-73, -74, -78, -79]
def count1442 (b : Nat → Bool) : Nat := countLit b [-68, -70, -71, -73, -74, -78, -79]
def count1449 (b : Nat → Bool) : Nat := countLit b [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79]
def count1463 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count1465 (b : Nat → Bool) : Nat := countLit b [-81, -84, -86]
def count1468 (b : Nat → Bool) : Nat := countLit b [-87, -90]
def count1470 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1472 (b : Nat → Bool) : Nat := countLit b [-87, -90, -92, -93]
def count1476 (b : Nat → Bool) : Nat := countLit b [-81, -84, -86, -87, -90, -92, -93]
def count1483 (b : Nat → Bool) : Nat := countLit b [-98, -101]
def count1485 (b : Nat → Bool) : Nat := countLit b [-97, -98, -101]
def count1488 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count1490 (b : Nat → Bool) : Nat := countLit b [-106, -107]
def count1492 (b : Nat → Bool) : Nat := countLit b [-102, -104, -106, -107]
def count1496 (b : Nat → Bool) : Nat := countLit b [-97, -98, -101, -102, -104, -106, -107]
def count1503 (b : Nat → Bool) : Nat := countLit b [-81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]
def count1517 (b : Nat → Bool) : Nat := countLit b [-53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]
def count1532 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24, -25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52, -53, -56, -58, -59, -62, -63, -66, -68, -70, -71, -73, -74, -78, -79, -81, -84, -86, -87, -90, -92, -93, -97, -98, -101, -102, -104, -106, -107]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 773 then (if i < 386 then (if i < 193 then (if i < 96 then (if i < 48 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 22 then b 21 else (if i < 23 then b 22 else b 23))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then b 24 else (if i < 26 then b 25 else b 26)) else (if i < 28 then b 27 else (if i < 29 then b 28 else b 29))) else (if i < 33 then (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)))) else (if i < 42 then (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41))) else (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)))))) else (if i < 72 then (if i < 60 then (if i < 54 then (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 52 then b 51 else (if i < 53 then b 52 else b 53))) else (if i < 57 then (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)) else (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)))) else (if i < 66 then (if i < 63 then (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)) else (if i < 64 then b 63 else (if i < 65 then b 64 else b 65))) else (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))))) else (if i < 84 then (if i < 78 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77))) else (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)))) else (if i < 90 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))) else (if i < 93 then (if i < 91 then b 90 else (if i < 92 then b 91 else b 92)) else (if i < 94 then b 93 else (if i < 95 then b 94 else b 95))))))) else (if i < 144 then (if i < 120 then (if i < 108 then (if i < 102 then (if i < 99 then (if i < 97 then b 96 else (if i < 98 then b 97 else b 98)) else (if i < 100 then b 99 else (if i < 101 then b 100 else b 101))) else (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 106 then b 105 else (if i < 107 then b 106 else b 107)))) else (if i < 114 then (if i < 111 then (if i < 109 then b 108 else (if i < 110 then b 109 else b 110)) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113))) else (if i < 117 then (if i < 115 then b 114 else (if i < 116 then b 115 else b 116)) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119))))) else (if i < 132 then (if i < 126 then (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 124 then b 123 else (if i < 125 then b 124 else b 125))) else (if i < 129 then (if i < 127 then b 126 else (if i < 128 then b 127 else b 128)) else (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)))) else (if i < 138 then (if i < 135 then (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)) else (if i < 136 then b 135 else (if i < 137 then b 136 else b 137))) else (if i < 141 then (if i < 139 then b 138 else (if i < 140 then b 139 else b 140)) else (if i < 142 then b 141 else (if i < 143 then b 142 else b 143)))))) else (if i < 168 then (if i < 156 then (if i < 150 then (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 148 then b 147 else (if i < 149 then b 148 else b 149))) else (if i < 153 then (if i < 151 then b 150 else (if i < 152 then b 151 else b 152)) else (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)))) else (if i < 162 then (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167))))) else (if i < 180 then (if i < 174 then (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 172 then b 171 else (if i < 173 then b 172 else b 173))) else (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)))) else (if i < 186 then (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185))) else (if i < 189 then (if i < 187 then b 186 else (if i < 188 then b 187 else b 188)) else (if i < 191 then (if i < 190 then b 189 else b 190) else (if i < 192 then b 191 else b 192)))))))) else (if i < 289 then (if i < 241 then (if i < 217 then (if i < 205 then (if i < 199 then (if i < 196 then (if i < 194 then b 193 else (if i < 195 then b 194 else b 195)) else (if i < 197 then b 196 else (if i < 198 then b 197 else b 198))) else (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)))) else (if i < 211 then (if i < 208 then (if i < 206 then b 205 else (if i < 207 then b 206 else b 207)) else (if i < 209 then b 208 else (if i < 210 then b 209 else b 210))) else (if i < 214 then (if i < 212 then b 211 else (if i < 213 then b 212 else b 213)) else (if i < 215 then b 214 else (if i < 216 then b 215 else b 216))))) else (if i < 229 then (if i < 223 then (if i < 220 then (if i < 218 then b 217 else (if i < 219 then b 218 else decide (1 ≤ count219 b))) else (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b)))) else (if i < 226 then (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b))) else (if i < 227 then decide (2 ≤ count225 b) else (if i < 228 then decide (1 ≤ count227 b) else decide (2 ≤ count227 b))))) else (if i < 235 then (if i < 232 then (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b))) else (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))) else (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b))))))) else (if i < 265 then (if i < 253 then (if i < 247 then (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 245 then decide (2 ≤ count243 b) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)))) else (if i < 250 then (if i < 248 then decide (1 ≤ count247 b) else (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b))) else (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b))))) else (if i < 259 then (if i < 256 then (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b))) else (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)))) else (if i < 262 then (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))) else (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))))) else (if i < 277 then (if i < 271 then (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)))) else (if i < 274 then (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))) else (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))))) else (if i < 283 then (if i < 280 then (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))) else (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)))) else (if i < 286 then (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b))) else (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)))))))) else (if i < 337 then (if i < 313 then (if i < 301 then (if i < 295 then (if i < 292 then (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b))) else (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)))) else (if i < 298 then (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))) else (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))))) else (if i < 307 then (if i < 304 then (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))) else (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)))) else (if i < 310 then (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b))) else (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))))) else (if i < 325 then (if i < 319 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))) else (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))) else (if i < 331 then (if i < 328 then (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))) else (if i < 329 then decide (2 ≤ count327 b) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)))) else (if i < 334 then (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b))) else (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b))))))) else (if i < 361 then (if i < 349 then (if i < 343 then (if i < 340 then (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))) else (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))) else (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 347 then decide (2 ≤ count345 b) else (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b))))) else (if i < 355 then (if i < 352 then (if i < 350 then decide (1 ≤ count349 b) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b))) else (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)))) else (if i < 358 then (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b))) else (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))))) else (if i < 373 then (if i < 367 then (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)))) else (if i < 370 then (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))) else (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))))) else (if i < 379 then (if i < 376 then (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b))) else (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)))) else (if i < 382 then (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))) else (if i < 384 then (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)))))))))) else (if i < 579 then (if i < 482 then (if i < 434 then (if i < 410 then (if i < 398 then (if i < 392 then (if i < 389 then (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))) else (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b)))) else (if i < 395 then (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b))) else (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))))) else (if i < 404 then (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))) else (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 408 then decide (1 ≤ count407 b) else (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)))))) else (if i < 422 then (if i < 416 then (if i < 413 then (if i < 411 then decide (2 ≤ count409 b) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))) else (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)))) else (if i < 419 then (if i < 417 then decide (2 ≤ count415 b) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b))) else (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))))) else (if i < 428 then (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b)))) else (if i < 431 then (if i < 429 then decide (2 ≤ count427 b) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))) else (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))))))) else (if i < 458 then (if i < 446 then (if i < 440 then (if i < 437 then (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b))) else (if i < 438 then decide (3 ≤ count435 b) else (if i < 439 then decide (1 ≤ count438 b) else decide (2 ≤ count438 b)))) else (if i < 443 then (if i < 441 then decide (1 ≤ count440 b) else (if i < 442 then decide (2 ≤ count440 b) else decide (3 ≤ count440 b))) else (if i < 444 then decide (1 ≤ count443 b) else (if i < 445 then decide (2 ≤ count443 b) else decide (3 ≤ count443 b))))) else (if i < 452 then (if i < 449 then (if i < 447 then decide (4 ≤ count443 b) else (if i < 448 then decide (5 ≤ count443 b) else decide (6 ≤ count443 b))) else (if i < 450 then decide (1 ≤ count449 b) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)))) else (if i < 455 then (if i < 453 then decide (2 ≤ count451 b) else (if i < 454 then decide (3 ≤ count451 b) else decide (1 ≤ count454 b))) else (if i < 456 then decide (2 ≤ count454 b) else (if i < 457 then decide (1 ≤ count456 b) else decide (2 ≤ count456 b)))))) else (if i < 470 then (if i < 464 then (if i < 461 then (if i < 459 then decide (1 ≤ count458 b) else (if i < 460 then decide (2 ≤ count458 b) else decide (3 ≤ count458 b))) else (if i < 462 then decide (4 ≤ count458 b) else (if i < 463 then decide (1 ≤ count462 b) else decide (2 ≤ count462 b)))) else (if i < 467 then (if i < 465 then decide (3 ≤ count462 b) else (if i < 466 then decide (4 ≤ count462 b) else decide (5 ≤ count462 b))) else (if i < 468 then decide (6 ≤ count462 b) else (if i < 469 then decide (7 ≤ count462 b) else decide (1 ≤ count469 b))))) else (if i < 476 then (if i < 473 then (if i < 471 then decide (2 ≤ count469 b) else (if i < 472 then decide (3 ≤ count469 b) else decide (4 ≤ count469 b))) else (if i < 474 then decide (5 ≤ count469 b) else (if i < 475 then decide (6 ≤ count469 b) else decide (7 ≤ count469 b)))) else (if i < 479 then (if i < 477 then decide (8 ≤ count469 b) else (if i < 478 then decide (9 ≤ count469 b) else decide (10 ≤ count469 b))) else (if i < 480 then decide (11 ≤ count469 b) else (if i < 481 then decide (12 ≤ count469 b) else decide (13 ≤ count469 b)))))))) else (if i < 530 then (if i < 506 then (if i < 494 then (if i < 488 then (if i < 485 then (if i < 483 then decide (1 ≤ count482 b) else (if i < 484 then decide (2 ≤ count482 b) else decide (1 ≤ count484 b))) else (if i < 486 then decide (2 ≤ count484 b) else (if i < 487 then decide (3 ≤ count484 b) else decide (1 ≤ count487 b)))) else (if i < 491 then (if i < 489 then decide (2 ≤ count487 b) else (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b))) else (if i < 492 then decide (1 ≤ count491 b) else (if i < 493 then decide (2 ≤ count491 b) else decide (3 ≤ count491 b))))) else (if i < 500 then (if i < 497 then (if i < 495 then decide (4 ≤ count491 b) else (if i < 496 then decide (1 ≤ count495 b) else decide (2 ≤ count495 b))) else (if i < 498 then decide (3 ≤ count495 b) else (if i < 499 then decide (4 ≤ count495 b) else decide (5 ≤ count495 b)))) else (if i < 503 then (if i < 501 then decide (6 ≤ count495 b) else (if i < 502 then decide (7 ≤ count495 b) else decide (1 ≤ count502 b))) else (if i < 504 then decide (2 ≤ count502 b) else (if i < 505 then decide (1 ≤ count504 b) else decide (2 ≤ count504 b)))))) else (if i < 518 then (if i < 512 then (if i < 509 then (if i < 507 then decide (3 ≤ count504 b) else (if i < 508 then decide (1 ≤ count507 b) else decide (2 ≤ count507 b))) else (if i < 510 then decide (1 ≤ count509 b) else (if i < 511 then decide (2 ≤ count509 b) else decide (1 ≤ count511 b)))) else (if i < 515 then (if i < 513 then decide (2 ≤ count511 b) else (if i < 514 then decide (3 ≤ count511 b) else decide (4 ≤ count511 b))) else (if i < 516 then decide (1 ≤ count515 b) else (if i < 517 then decide (2 ≤ count515 b) else decide (3 ≤ count515 b))))) else (if i < 524 then (if i < 521 then (if i < 519 then decide (4 ≤ count515 b) else (if i < 520 then decide (5 ≤ count515 b) else decide (6 ≤ count515 b))) else (if i < 522 then decide (7 ≤ count515 b) else (if i < 523 then decide (1 ≤ count522 b) else decide (2 ≤ count522 b)))) else (if i < 527 then (if i < 525 then decide (3 ≤ count522 b) else (if i < 526 then decide (4 ≤ count522 b) else decide (5 ≤ count522 b))) else (if i < 528 then decide (6 ≤ count522 b) else (if i < 529 then decide (7 ≤ count522 b) else decide (8 ≤ count522 b))))))) else (if i < 554 then (if i < 542 then (if i < 536 then (if i < 533 then (if i < 531 then decide (9 ≤ count522 b) else (if i < 532 then decide (10 ≤ count522 b) else decide (11 ≤ count522 b))) else (if i < 534 then decide (12 ≤ count522 b) else (if i < 535 then decide (13 ≤ count522 b) else decide (14 ≤ count522 b)))) else (if i < 539 then (if i < 537 then decide (1 ≤ count536 b) else (if i < 538 then decide (2 ≤ count536 b) else decide (3 ≤ count536 b))) else (if i < 540 then decide (4 ≤ count536 b) else (if i < 541 then decide (5 ≤ count536 b) else decide (6 ≤ count536 b))))) else (if i < 548 then (if i < 545 then (if i < 543 then decide (7 ≤ count536 b) else (if i < 544 then decide (8 ≤ count536 b) else decide (9 ≤ count536 b))) else (if i < 546 then decide (10 ≤ count536 b) else (if i < 547 then decide (11 ≤ count536 b) else decide (12 ≤ count536 b)))) else (if i < 551 then (if i < 549 then decide (13 ≤ count536 b) else (if i < 550 then decide (14 ≤ count536 b) else decide (15 ≤ count536 b))) else (if i < 552 then decide (16 ≤ count536 b) else (if i < 553 then decide (17 ≤ count536 b) else decide (18 ≤ count536 b)))))) else (if i < 566 then (if i < 560 then (if i < 557 then (if i < 555 then decide (19 ≤ count536 b) else (if i < 556 then decide (20 ≤ count536 b) else decide (21 ≤ count536 b))) else (if i < 558 then decide (22 ≤ count536 b) else (if i < 559 then decide (23 ≤ count536 b) else decide (24 ≤ count536 b)))) else (if i < 563 then (if i < 561 then decide (25 ≤ count536 b) else (if i < 562 then decide (26 ≤ count536 b) else decide (27 ≤ count536 b))) else (if i < 564 then decide (1 ≤ count563 b) else (if i < 565 then decide (2 ≤ count563 b) else decide (1 ≤ count565 b))))) else (if i < 572 then (if i < 569 then (if i < 567 then decide (2 ≤ count565 b) else (if i < 568 then decide (3 ≤ count565 b) else decide (1 ≤ count568 b))) else (if i < 570 then decide (2 ≤ count568 b) else (if i < 571 then decide (1 ≤ count570 b) else decide (2 ≤ count570 b)))) else (if i < 575 then (if i < 573 then decide (3 ≤ count570 b) else (if i < 574 then decide (1 ≤ count573 b) else decide (2 ≤ count573 b))) else (if i < 577 then (if i < 576 then decide (3 ≤ count573 b) else decide (4 ≤ count573 b)) else (if i < 578 then decide (5 ≤ count573 b) else decide (6 ≤ count573 b))))))))) else (if i < 676 then (if i < 627 then (if i < 603 then (if i < 591 then (if i < 585 then (if i < 582 then (if i < 580 then decide (1 ≤ count579 b) else (if i < 581 then decide (2 ≤ count579 b) else decide (1 ≤ count581 b))) else (if i < 583 then decide (2 ≤ count581 b) else (if i < 584 then decide (3 ≤ count581 b) else decide (1 ≤ count584 b)))) else (if i < 588 then (if i < 586 then decide (2 ≤ count584 b) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b))) else (if i < 589 then decide (1 ≤ count588 b) else (if i < 590 then decide (2 ≤ count588 b) else decide (3 ≤ count588 b))))) else (if i < 597 then (if i < 594 then (if i < 592 then decide (4 ≤ count588 b) else (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b))) else (if i < 595 then decide (3 ≤ count592 b) else (if i < 596 then decide (4 ≤ count592 b) else decide (5 ≤ count592 b)))) else (if i < 600 then (if i < 598 then decide (6 ≤ count592 b) else (if i < 599 then decide (7 ≤ count592 b) else decide (1 ≤ count599 b))) else (if i < 601 then decide (2 ≤ count599 b) else (if i < 602 then decide (3 ≤ count599 b) else decide (4 ≤ count599 b)))))) else (if i < 615 then (if i < 609 then (if i < 606 then (if i < 604 then decide (5 ≤ count599 b) else (if i < 605 then decide (6 ≤ count599 b) else decide (7 ≤ count599 b))) else (if i < 607 then decide (8 ≤ count599 b) else (if i < 608 then decide (9 ≤ count599 b) else decide (10 ≤ count599 b)))) else (if i < 612 then (if i < 610 then decide (11 ≤ count599 b) else (if i < 611 then decide (12 ≤ count599 b) else decide (13 ≤ count599 b))) else (if i < 613 then decide (1 ≤ count612 b) else (if i < 614 then decide (2 ≤ count612 b) else decide (1 ≤ count614 b))))) else (if i < 621 then (if i < 618 then (if i < 616 then decide (2 ≤ count614 b) else (if i < 617 then decide (3 ≤ count614 b) else decide (1 ≤ count617 b))) else (if i < 619 then decide (2 ≤ count617 b) else (if i < 620 then decide (1 ≤ count619 b) else decide (2 ≤ count619 b)))) else (if i < 624 then (if i < 622 then decide (1 ≤ count621 b) else (if i < 623 then decide (2 ≤ count621 b) else decide (3 ≤ count621 b))) else (if i < 625 then decide (4 ≤ count621 b) else (if i < 626 then decide (1 ≤ count625 b) else decide (2 ≤ count625 b))))))) else (if i < 651 then (if i < 639 then (if i < 633 then (if i < 630 then (if i < 628 then decide (3 ≤ count625 b) else (if i < 629 then decide (4 ≤ count625 b) else decide (5 ≤ count625 b))) else (if i < 631 then decide (6 ≤ count625 b) else (if i < 632 then decide (7 ≤ count625 b) else decide (1 ≤ count632 b)))) else (if i < 636 then (if i < 634 then decide (2 ≤ count632 b) else (if i < 635 then decide (1 ≤ count634 b) else decide (2 ≤ count634 b))) else (if i < 637 then decide (3 ≤ count634 b) else (if i < 638 then decide (1 ≤ count637 b) else decide (2 ≤ count637 b))))) else (if i < 645 then (if i < 642 then (if i < 640 then decide (1 ≤ count639 b) else (if i < 641 then decide (2 ≤ count639 b) else decide (1 ≤ count641 b))) else (if i < 643 then decide (2 ≤ count641 b) else (if i < 644 then decide (3 ≤ count641 b) else decide (4 ≤ count641 b)))) else (if i < 648 then (if i < 646 then decide (1 ≤ count645 b) else (if i < 647 then decide (2 ≤ count645 b) else decide (3 ≤ count645 b))) else (if i < 649 then decide (4 ≤ count645 b) else (if i < 650 then decide (5 ≤ count645 b) else decide (6 ≤ count645 b)))))) else (if i < 663 then (if i < 657 then (if i < 654 then (if i < 652 then decide (7 ≤ count645 b) else (if i < 653 then decide (1 ≤ count652 b) else decide (2 ≤ count652 b))) else (if i < 655 then decide (3 ≤ count652 b) else (if i < 656 then decide (4 ≤ count652 b) else decide (5 ≤ count652 b)))) else (if i < 660 then (if i < 658 then decide (6 ≤ count652 b) else (if i < 659 then decide (7 ≤ count652 b) else decide (8 ≤ count652 b))) else (if i < 661 then decide (9 ≤ count652 b) else (if i < 662 then decide (10 ≤ count652 b) else decide (11 ≤ count652 b))))) else (if i < 669 then (if i < 666 then (if i < 664 then decide (12 ≤ count652 b) else (if i < 665 then decide (13 ≤ count652 b) else decide (14 ≤ count652 b))) else (if i < 667 then decide (1 ≤ count666 b) else (if i < 668 then decide (2 ≤ count666 b) else decide (3 ≤ count666 b)))) else (if i < 672 then (if i < 670 then decide (4 ≤ count666 b) else (if i < 671 then decide (5 ≤ count666 b) else decide (6 ≤ count666 b))) else (if i < 674 then (if i < 673 then decide (7 ≤ count666 b) else decide (8 ≤ count666 b)) else (if i < 675 then decide (9 ≤ count666 b) else decide (10 ≤ count666 b)))))))) else (if i < 724 then (if i < 700 then (if i < 688 then (if i < 682 then (if i < 679 then (if i < 677 then decide (11 ≤ count666 b) else (if i < 678 then decide (12 ≤ count666 b) else decide (13 ≤ count666 b))) else (if i < 680 then decide (14 ≤ count666 b) else (if i < 681 then decide (15 ≤ count666 b) else decide (16 ≤ count666 b)))) else (if i < 685 then (if i < 683 then decide (17 ≤ count666 b) else (if i < 684 then decide (18 ≤ count666 b) else decide (19 ≤ count666 b))) else (if i < 686 then decide (20 ≤ count666 b) else (if i < 687 then decide (21 ≤ count666 b) else decide (22 ≤ count666 b))))) else (if i < 694 then (if i < 691 then (if i < 689 then decide (23 ≤ count666 b) else (if i < 690 then decide (24 ≤ count666 b) else decide (25 ≤ count666 b))) else (if i < 692 then decide (26 ≤ count666 b) else (if i < 693 then decide (27 ≤ count666 b) else decide (1 ≤ count693 b)))) else (if i < 697 then (if i < 695 then decide (2 ≤ count693 b) else (if i < 696 then decide (3 ≤ count693 b) else decide (4 ≤ count693 b))) else (if i < 698 then decide (5 ≤ count693 b) else (if i < 699 then decide (6 ≤ count693 b) else decide (7 ≤ count693 b)))))) else (if i < 712 then (if i < 706 then (if i < 703 then (if i < 701 then decide (8 ≤ count693 b) else (if i < 702 then decide (9 ≤ count693 b) else decide (10 ≤ count693 b))) else (if i < 704 then decide (11 ≤ count693 b) else (if i < 705 then decide (12 ≤ count693 b) else decide (13 ≤ count693 b)))) else (if i < 709 then (if i < 707 then decide (14 ≤ count693 b) else (if i < 708 then decide (15 ≤ count693 b) else decide (16 ≤ count693 b))) else (if i < 710 then decide (17 ≤ count693 b) else (if i < 711 then decide (18 ≤ count693 b) else decide (19 ≤ count693 b))))) else (if i < 718 then (if i < 715 then (if i < 713 then decide (20 ≤ count693 b) else (if i < 714 then decide (21 ≤ count693 b) else decide (22 ≤ count693 b))) else (if i < 716 then decide (23 ≤ count693 b) else (if i < 717 then decide (24 ≤ count693 b) else decide (25 ≤ count693 b)))) else (if i < 721 then (if i < 719 then decide (26 ≤ count693 b) else (if i < 720 then decide (27 ≤ count693 b) else decide (28 ≤ count693 b))) else (if i < 722 then decide (29 ≤ count693 b) else (if i < 723 then decide (30 ≤ count693 b) else decide (31 ≤ count693 b))))))) else (if i < 748 then (if i < 736 then (if i < 730 then (if i < 727 then (if i < 725 then decide (32 ≤ count693 b) else (if i < 726 then decide (33 ≤ count693 b) else decide (34 ≤ count693 b))) else (if i < 728 then decide (35 ≤ count693 b) else (if i < 729 then decide (36 ≤ count693 b) else decide (37 ≤ count693 b)))) else (if i < 733 then (if i < 731 then decide (38 ≤ count693 b) else (if i < 732 then decide (39 ≤ count693 b) else decide (40 ≤ count693 b))) else (if i < 734 then decide (41 ≤ count693 b) else (if i < 735 then decide (42 ≤ count693 b) else decide (1 ≤ count735 b))))) else (if i < 742 then (if i < 739 then (if i < 737 then decide (2 ≤ count735 b) else (if i < 738 then decide (1 ≤ count737 b) else decide (2 ≤ count737 b))) else (if i < 740 then decide (3 ≤ count737 b) else (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b)))) else (if i < 745 then (if i < 743 then decide (1 ≤ count742 b) else (if i < 744 then decide (2 ≤ count742 b) else decide (3 ≤ count742 b))) else (if i < 746 then decide (1 ≤ count745 b) else (if i < 747 then decide (2 ≤ count745 b) else decide (3 ≤ count745 b)))))) else (if i < 760 then (if i < 754 then (if i < 751 then (if i < 749 then decide (4 ≤ count745 b) else (if i < 750 then decide (5 ≤ count745 b) else decide (6 ≤ count745 b))) else (if i < 752 then decide (1 ≤ count751 b) else (if i < 753 then decide (2 ≤ count751 b) else decide (1 ≤ count753 b)))) else (if i < 757 then (if i < 755 then decide (2 ≤ count753 b) else (if i < 756 then decide (3 ≤ count753 b) else decide (1 ≤ count756 b))) else (if i < 758 then decide (2 ≤ count756 b) else (if i < 759 then decide (1 ≤ count758 b) else decide (2 ≤ count758 b))))) else (if i < 766 then (if i < 763 then (if i < 761 then decide (1 ≤ count760 b) else (if i < 762 then decide (2 ≤ count760 b) else decide (3 ≤ count760 b))) else (if i < 764 then decide (4 ≤ count760 b) else (if i < 765 then decide (1 ≤ count764 b) else decide (2 ≤ count764 b)))) else (if i < 769 then (if i < 767 then decide (3 ≤ count764 b) else (if i < 768 then decide (4 ≤ count764 b) else decide (5 ≤ count764 b))) else (if i < 771 then (if i < 770 then decide (6 ≤ count764 b) else decide (7 ≤ count764 b)) else (if i < 772 then decide (1 ≤ count771 b) else decide (2 ≤ count771 b))))))))))) else (if i < 1160 then (if i < 966 then (if i < 869 then (if i < 821 then (if i < 797 then (if i < 785 then (if i < 779 then (if i < 776 then (if i < 774 then decide (3 ≤ count771 b) else (if i < 775 then decide (4 ≤ count771 b) else decide (5 ≤ count771 b))) else (if i < 777 then decide (6 ≤ count771 b) else (if i < 778 then decide (7 ≤ count771 b) else decide (8 ≤ count771 b)))) else (if i < 782 then (if i < 780 then decide (9 ≤ count771 b) else (if i < 781 then decide (10 ≤ count771 b) else decide (11 ≤ count771 b))) else (if i < 783 then decide (12 ≤ count771 b) else (if i < 784 then decide (13 ≤ count771 b) else decide (1 ≤ count784 b))))) else (if i < 791 then (if i < 788 then (if i < 786 then decide (2 ≤ count784 b) else (if i < 787 then decide (1 ≤ count786 b) else decide (2 ≤ count786 b))) else (if i < 789 then decide (3 ≤ count786 b) else (if i < 790 then decide (1 ≤ count789 b) else decide (2 ≤ count789 b)))) else (if i < 794 then (if i < 792 then decide (1 ≤ count791 b) else (if i < 793 then decide (2 ≤ count791 b) else decide (1 ≤ count793 b))) else (if i < 795 then decide (2 ≤ count793 b) else (if i < 796 then decide (3 ≤ count793 b) else decide (4 ≤ count793 b)))))) else (if i < 809 then (if i < 803 then (if i < 800 then (if i < 798 then decide (1 ≤ count797 b) else (if i < 799 then decide (2 ≤ count797 b) else decide (3 ≤ count797 b))) else (if i < 801 then decide (4 ≤ count797 b) else (if i < 802 then decide (5 ≤ count797 b) else decide (6 ≤ count797 b)))) else (if i < 806 then (if i < 804 then decide (7 ≤ count797 b) else (if i < 805 then decide (1 ≤ count804 b) else decide (2 ≤ count804 b))) else (if i < 807 then decide (1 ≤ count806 b) else (if i < 808 then decide (2 ≤ count806 b) else decide (3 ≤ count806 b))))) else (if i < 815 then (if i < 812 then (if i < 810 then decide (1 ≤ count809 b) else (if i < 811 then decide (2 ≤ count809 b) else decide (1 ≤ count811 b))) else (if i < 813 then decide (2 ≤ count811 b) else (if i < 814 then decide (1 ≤ count813 b) else decide (2 ≤ count813 b)))) else (if i < 818 then (if i < 816 then decide (3 ≤ count813 b) else (if i < 817 then decide (4 ≤ count813 b) else decide (1 ≤ count817 b))) else (if i < 819 then decide (2 ≤ count817 b) else (if i < 820 then decide (3 ≤ count817 b) else decide (4 ≤ count817 b))))))) else (if i < 845 then (if i < 833 then (if i < 827 then (if i < 824 then (if i < 822 then decide (5 ≤ count817 b) else (if i < 823 then decide (6 ≤ count817 b) else decide (7 ≤ count817 b))) else (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (3 ≤ count824 b)))) else (if i < 830 then (if i < 828 then decide (4 ≤ count824 b) else (if i < 829 then decide (5 ≤ count824 b) else decide (6 ≤ count824 b))) else (if i < 831 then decide (7 ≤ count824 b) else (if i < 832 then decide (8 ≤ count824 b) else decide (9 ≤ count824 b))))) else (if i < 839 then (if i < 836 then (if i < 834 then decide (10 ≤ count824 b) else (if i < 835 then decide (11 ≤ count824 b) else decide (12 ≤ count824 b))) else (if i < 837 then decide (13 ≤ count824 b) else (if i < 838 then decide (14 ≤ count824 b) else decide (1 ≤ count838 b)))) else (if i < 842 then (if i < 840 then decide (2 ≤ count838 b) else (if i < 841 then decide (3 ≤ count838 b) else decide (4 ≤ count838 b))) else (if i < 843 then decide (5 ≤ count838 b) else (if i < 844 then decide (6 ≤ count838 b) else decide (7 ≤ count838 b)))))) else (if i < 857 then (if i < 851 then (if i < 848 then (if i < 846 then decide (8 ≤ count838 b) else (if i < 847 then decide (9 ≤ count838 b) else decide (10 ≤ count838 b))) else (if i < 849 then decide (11 ≤ count838 b) else (if i < 850 then decide (12 ≤ count838 b) else decide (13 ≤ count838 b)))) else (if i < 854 then (if i < 852 then decide (14 ≤ count838 b) else (if i < 853 then decide (1 ≤ count852 b) else decide (2 ≤ count852 b))) else (if i < 855 then decide (1 ≤ count854 b) else (if i < 856 then decide (2 ≤ count854 b) else decide (3 ≤ count854 b))))) else (if i < 863 then (if i < 860 then (if i < 858 then decide (1 ≤ count857 b) else (if i < 859 then decide (2 ≤ count857 b) else decide (1 ≤ count859 b))) else (if i < 861 then decide (2 ≤ count859 b) else (if i < 862 then decide (3 ≤ count859 b) else decide (1 ≤ count862 b)))) else (if i < 866 then (if i < 864 then decide (2 ≤ count862 b) else (if i < 865 then decide (3 ≤ count862 b) else decide (4 ≤ count862 b))) else (if i < 867 then decide (5 ≤ count862 b) else (if i < 868 then decide (6 ≤ count862 b) else decide (1 ≤ count868 b)))))))) else (if i < 917 then (if i < 893 then (if i < 881 then (if i < 875 then (if i < 872 then (if i < 870 then decide (2 ≤ count868 b) else (if i < 871 then decide (1 ≤ count870 b) else decide (2 ≤ count870 b))) else (if i < 873 then decide (3 ≤ count870 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b)))) else (if i < 878 then (if i < 876 then decide (1 ≤ count875 b) else (if i < 877 then decide (2 ≤ count875 b) else decide (1 ≤ count877 b))) else (if i < 879 then decide (2 ≤ count877 b) else (if i < 880 then decide (3 ≤ count877 b) else decide (4 ≤ count877 b))))) else (if i < 887 then (if i < 884 then (if i < 882 then decide (1 ≤ count881 b) else (if i < 883 then decide (2 ≤ count881 b) else decide (3 ≤ count881 b))) else (if i < 885 then decide (4 ≤ count881 b) else (if i < 886 then decide (5 ≤ count881 b) else decide (6 ≤ count881 b)))) else (if i < 890 then (if i < 888 then decide (7 ≤ count881 b) else (if i < 889 then decide (1 ≤ count888 b) else decide (2 ≤ count888 b))) else (if i < 891 then decide (3 ≤ count888 b) else (if i < 892 then decide (4 ≤ count888 b) else decide (5 ≤ count888 b)))))) else (if i < 905 then (if i < 899 then (if i < 896 then (if i < 894 then decide (6 ≤ count888 b) else (if i < 895 then decide (7 ≤ count888 b) else decide (8 ≤ count888 b))) else (if i < 897 then decide (9 ≤ count888 b) else (if i < 898 then decide (10 ≤ count888 b) else decide (11 ≤ count888 b)))) else (if i < 902 then (if i < 900 then decide (12 ≤ count888 b) else (if i < 901 then decide (13 ≤ count888 b) else decide (1 ≤ count901 b))) else (if i < 903 then decide (2 ≤ count901 b) else (if i < 904 then decide (1 ≤ count903 b) else decide (2 ≤ count903 b))))) else (if i < 911 then (if i < 908 then (if i < 906 then decide (3 ≤ count903 b) else (if i < 907 then decide (1 ≤ count906 b) else decide (2 ≤ count906 b))) else (if i < 909 then decide (1 ≤ count908 b) else (if i < 910 then decide (2 ≤ count908 b) else decide (1 ≤ count910 b)))) else (if i < 914 then (if i < 912 then decide (2 ≤ count910 b) else (if i < 913 then decide (3 ≤ count910 b) else decide (4 ≤ count910 b))) else (if i < 915 then decide (1 ≤ count914 b) else (if i < 916 then decide (2 ≤ count914 b) else decide (3 ≤ count914 b))))))) else (if i < 941 then (if i < 929 then (if i < 923 then (if i < 920 then (if i < 918 then decide (4 ≤ count914 b) else (if i < 919 then decide (5 ≤ count914 b) else decide (6 ≤ count914 b))) else (if i < 921 then decide (7 ≤ count914 b) else (if i < 922 then decide (1 ≤ count921 b) else decide (2 ≤ count921 b)))) else (if i < 926 then (if i < 924 then decide (1 ≤ count923 b) else (if i < 925 then decide (2 ≤ count923 b) else decide (3 ≤ count923 b))) else (if i < 927 then decide (1 ≤ count926 b) else (if i < 928 then decide (2 ≤ count926 b) else decide (1 ≤ count928 b))))) else (if i < 935 then (if i < 932 then (if i < 930 then decide (2 ≤ count928 b) else (if i < 931 then decide (1 ≤ count930 b) else decide (2 ≤ count930 b))) else (if i < 933 then decide (3 ≤ count930 b) else (if i < 934 then decide (4 ≤ count930 b) else decide (1 ≤ count934 b)))) else (if i < 938 then (if i < 936 then decide (2 ≤ count934 b) else (if i < 937 then decide (3 ≤ count934 b) else decide (4 ≤ count934 b))) else (if i < 939 then decide (5 ≤ count934 b) else (if i < 940 then decide (6 ≤ count934 b) else decide (7 ≤ count934 b)))))) else (if i < 953 then (if i < 947 then (if i < 944 then (if i < 942 then decide (1 ≤ count941 b) else (if i < 943 then decide (2 ≤ count941 b) else decide (3 ≤ count941 b))) else (if i < 945 then decide (4 ≤ count941 b) else (if i < 946 then decide (5 ≤ count941 b) else decide (6 ≤ count941 b)))) else (if i < 950 then (if i < 948 then decide (7 ≤ count941 b) else (if i < 949 then decide (8 ≤ count941 b) else decide (9 ≤ count941 b))) else (if i < 951 then decide (10 ≤ count941 b) else (if i < 952 then decide (11 ≤ count941 b) else decide (12 ≤ count941 b))))) else (if i < 959 then (if i < 956 then (if i < 954 then decide (13 ≤ count941 b) else (if i < 955 then decide (14 ≤ count941 b) else decide (1 ≤ count955 b))) else (if i < 957 then decide (2 ≤ count955 b) else (if i < 958 then decide (3 ≤ count955 b) else decide (4 ≤ count955 b)))) else (if i < 962 then (if i < 960 then decide (5 ≤ count955 b) else (if i < 961 then decide (6 ≤ count955 b) else decide (7 ≤ count955 b))) else (if i < 964 then (if i < 963 then decide (8 ≤ count955 b) else decide (9 ≤ count955 b)) else (if i < 965 then decide (10 ≤ count955 b) else decide (11 ≤ count955 b))))))))) else (if i < 1063 then (if i < 1014 then (if i < 990 then (if i < 978 then (if i < 972 then (if i < 969 then (if i < 967 then decide (12 ≤ count955 b) else (if i < 968 then decide (13 ≤ count955 b) else decide (14 ≤ count955 b))) else (if i < 970 then decide (1 ≤ count969 b) else (if i < 971 then decide (2 ≤ count969 b) else decide (3 ≤ count969 b)))) else (if i < 975 then (if i < 973 then decide (4 ≤ count969 b) else (if i < 974 then decide (5 ≤ count969 b) else decide (6 ≤ count969 b))) else (if i < 976 then decide (7 ≤ count969 b) else (if i < 977 then decide (8 ≤ count969 b) else decide (9 ≤ count969 b))))) else (if i < 984 then (if i < 981 then (if i < 979 then decide (10 ≤ count969 b) else (if i < 980 then decide (11 ≤ count969 b) else decide (12 ≤ count969 b))) else (if i < 982 then decide (13 ≤ count969 b) else (if i < 983 then decide (14 ≤ count969 b) else decide (1 ≤ count983 b)))) else (if i < 987 then (if i < 985 then decide (2 ≤ count983 b) else (if i < 986 then decide (1 ≤ count985 b) else decide (2 ≤ count985 b))) else (if i < 988 then decide (3 ≤ count985 b) else (if i < 989 then decide (1 ≤ count988 b) else decide (2 ≤ count988 b)))))) else (if i < 1002 then (if i < 996 then (if i < 993 then (if i < 991 then decide (1 ≤ count990 b) else (if i < 992 then decide (2 ≤ count990 b) else decide (3 ≤ count990 b))) else (if i < 994 then decide (1 ≤ count993 b) else (if i < 995 then decide (2 ≤ count993 b) else decide (3 ≤ count993 b)))) else (if i < 999 then (if i < 997 then decide (4 ≤ count993 b) else (if i < 998 then decide (5 ≤ count993 b) else decide (6 ≤ count993 b))) else (if i < 1000 then decide (1 ≤ count999 b) else (if i < 1001 then decide (2 ≤ count999 b) else decide (1 ≤ count1001 b))))) else (if i < 1008 then (if i < 1005 then (if i < 1003 then decide (2 ≤ count1001 b) else (if i < 1004 then decide (3 ≤ count1001 b) else decide (1 ≤ count1004 b))) else (if i < 1006 then decide (2 ≤ count1004 b) else (if i < 1007 then decide (1 ≤ count1006 b) else decide (2 ≤ count1006 b)))) else (if i < 1011 then (if i < 1009 then decide (1 ≤ count1008 b) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (3 ≤ count1008 b))) else (if i < 1012 then decide (4 ≤ count1008 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b))))))) else (if i < 1038 then (if i < 1026 then (if i < 1020 then (if i < 1017 then (if i < 1015 then decide (3 ≤ count1012 b) else (if i < 1016 then decide (4 ≤ count1012 b) else decide (5 ≤ count1012 b))) else (if i < 1018 then decide (6 ≤ count1012 b) else (if i < 1019 then decide (7 ≤ count1012 b) else decide (1 ≤ count1019 b)))) else (if i < 1023 then (if i < 1021 then decide (2 ≤ count1019 b) else (if i < 1022 then decide (3 ≤ count1019 b) else decide (4 ≤ count1019 b))) else (if i < 1024 then decide (5 ≤ count1019 b) else (if i < 1025 then decide (6 ≤ count1019 b) else decide (7 ≤ count1019 b))))) else (if i < 1032 then (if i < 1029 then (if i < 1027 then decide (8 ≤ count1019 b) else (if i < 1028 then decide (9 ≤ count1019 b) else decide (10 ≤ count1019 b))) else (if i < 1030 then decide (11 ≤ count1019 b) else (if i < 1031 then decide (12 ≤ count1019 b) else decide (13 ≤ count1019 b)))) else (if i < 1035 then (if i < 1033 then decide (1 ≤ count1032 b) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (1 ≤ count1034 b))) else (if i < 1036 then decide (2 ≤ count1034 b) else (if i < 1037 then decide (3 ≤ count1034 b) else decide (1 ≤ count1037 b)))))) else (if i < 1050 then (if i < 1044 then (if i < 1041 then (if i < 1039 then decide (2 ≤ count1037 b) else (if i < 1040 then decide (1 ≤ count1039 b) else decide (2 ≤ count1039 b))) else (if i < 1042 then decide (1 ≤ count1041 b) else (if i < 1043 then decide (2 ≤ count1041 b) else decide (3 ≤ count1041 b)))) else (if i < 1047 then (if i < 1045 then decide (4 ≤ count1041 b) else (if i < 1046 then decide (1 ≤ count1045 b) else decide (2 ≤ count1045 b))) else (if i < 1048 then decide (3 ≤ count1045 b) else (if i < 1049 then decide (4 ≤ count1045 b) else decide (5 ≤ count1045 b))))) else (if i < 1056 then (if i < 1053 then (if i < 1051 then decide (6 ≤ count1045 b) else (if i < 1052 then decide (7 ≤ count1045 b) else decide (1 ≤ count1052 b))) else (if i < 1054 then decide (2 ≤ count1052 b) else (if i < 1055 then decide (1 ≤ count1054 b) else decide (2 ≤ count1054 b)))) else (if i < 1059 then (if i < 1057 then decide (3 ≤ count1054 b) else (if i < 1058 then decide (1 ≤ count1057 b) else decide (2 ≤ count1057 b))) else (if i < 1061 then (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b)) else (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b)))))))) else (if i < 1111 then (if i < 1087 then (if i < 1075 then (if i < 1069 then (if i < 1066 then (if i < 1064 then decide (3 ≤ count1061 b) else (if i < 1065 then decide (4 ≤ count1061 b) else decide (1 ≤ count1065 b))) else (if i < 1067 then decide (2 ≤ count1065 b) else (if i < 1068 then decide (3 ≤ count1065 b) else decide (4 ≤ count1065 b)))) else (if i < 1072 then (if i < 1070 then decide (5 ≤ count1065 b) else (if i < 1071 then decide (6 ≤ count1065 b) else decide (7 ≤ count1065 b))) else (if i < 1073 then decide (1 ≤ count1072 b) else (if i < 1074 then decide (2 ≤ count1072 b) else decide (3 ≤ count1072 b))))) else (if i < 1081 then (if i < 1078 then (if i < 1076 then decide (4 ≤ count1072 b) else (if i < 1077 then decide (5 ≤ count1072 b) else decide (6 ≤ count1072 b))) else (if i < 1079 then decide (7 ≤ count1072 b) else (if i < 1080 then decide (8 ≤ count1072 b) else decide (9 ≤ count1072 b)))) else (if i < 1084 then (if i < 1082 then decide (10 ≤ count1072 b) else (if i < 1083 then decide (11 ≤ count1072 b) else decide (12 ≤ count1072 b))) else (if i < 1085 then decide (13 ≤ count1072 b) else (if i < 1086 then decide (14 ≤ count1072 b) else decide (1 ≤ count1086 b)))))) else (if i < 1099 then (if i < 1093 then (if i < 1090 then (if i < 1088 then decide (2 ≤ count1086 b) else (if i < 1089 then decide (3 ≤ count1086 b) else decide (4 ≤ count1086 b))) else (if i < 1091 then decide (5 ≤ count1086 b) else (if i < 1092 then decide (6 ≤ count1086 b) else decide (7 ≤ count1086 b)))) else (if i < 1096 then (if i < 1094 then decide (8 ≤ count1086 b) else (if i < 1095 then decide (9 ≤ count1086 b) else decide (10 ≤ count1086 b))) else (if i < 1097 then decide (11 ≤ count1086 b) else (if i < 1098 then decide (12 ≤ count1086 b) else decide (13 ≤ count1086 b))))) else (if i < 1105 then (if i < 1102 then (if i < 1100 then decide (14 ≤ count1086 b) else (if i < 1101 then decide (15 ≤ count1086 b) else decide (16 ≤ count1086 b))) else (if i < 1103 then decide (17 ≤ count1086 b) else (if i < 1104 then decide (18 ≤ count1086 b) else decide (19 ≤ count1086 b)))) else (if i < 1108 then (if i < 1106 then decide (20 ≤ count1086 b) else (if i < 1107 then decide (21 ≤ count1086 b) else decide (22 ≤ count1086 b))) else (if i < 1109 then decide (23 ≤ count1086 b) else (if i < 1110 then decide (24 ≤ count1086 b) else decide (25 ≤ count1086 b))))))) else (if i < 1135 then (if i < 1123 then (if i < 1117 then (if i < 1114 then (if i < 1112 then decide (26 ≤ count1086 b) else (if i < 1113 then decide (27 ≤ count1086 b) else decide (1 ≤ count1113 b))) else (if i < 1115 then decide (2 ≤ count1113 b) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b)))) else (if i < 1120 then (if i < 1118 then decide (3 ≤ count1115 b) else (if i < 1119 then decide (1 ≤ count1118 b) else decide (2 ≤ count1118 b))) else (if i < 1121 then decide (1 ≤ count1120 b) else (if i < 1122 then decide (2 ≤ count1120 b) else decide (1 ≤ count1122 b))))) else (if i < 1129 then (if i < 1126 then (if i < 1124 then decide (2 ≤ count1122 b) else (if i < 1125 then decide (3 ≤ count1122 b) else decide (4 ≤ count1122 b))) else (if i < 1127 then decide (1 ≤ count1126 b) else (if i < 1128 then decide (2 ≤ count1126 b) else decide (3 ≤ count1126 b)))) else (if i < 1132 then (if i < 1130 then decide (4 ≤ count1126 b) else (if i < 1131 then decide (5 ≤ count1126 b) else decide (6 ≤ count1126 b))) else (if i < 1133 then decide (7 ≤ count1126 b) else (if i < 1134 then decide (1 ≤ count1133 b) else decide (2 ≤ count1133 b)))))) else (if i < 1147 then (if i < 1141 then (if i < 1138 then (if i < 1136 then decide (1 ≤ count1135 b) else (if i < 1137 then decide (2 ≤ count1135 b) else decide (3 ≤ count1135 b))) else (if i < 1139 then decide (1 ≤ count1138 b) else (if i < 1140 then decide (2 ≤ count1138 b) else decide (1 ≤ count1140 b)))) else (if i < 1144 then (if i < 1142 then decide (2 ≤ count1140 b) else (if i < 1143 then decide (1 ≤ count1142 b) else decide (2 ≤ count1142 b))) else (if i < 1145 then decide (3 ≤ count1142 b) else (if i < 1146 then decide (4 ≤ count1142 b) else decide (1 ≤ count1146 b))))) else (if i < 1153 then (if i < 1150 then (if i < 1148 then decide (2 ≤ count1146 b) else (if i < 1149 then decide (3 ≤ count1146 b) else decide (4 ≤ count1146 b))) else (if i < 1151 then decide (5 ≤ count1146 b) else (if i < 1152 then decide (6 ≤ count1146 b) else decide (7 ≤ count1146 b)))) else (if i < 1156 then (if i < 1154 then decide (1 ≤ count1153 b) else (if i < 1155 then decide (2 ≤ count1153 b) else decide (3 ≤ count1153 b))) else (if i < 1158 then (if i < 1157 then decide (4 ≤ count1153 b) else decide (5 ≤ count1153 b)) else (if i < 1159 then decide (6 ≤ count1153 b) else decide (7 ≤ count1153 b)))))))))) else (if i < 1353 then (if i < 1256 then (if i < 1208 then (if i < 1184 then (if i < 1172 then (if i < 1166 then (if i < 1163 then (if i < 1161 then decide (8 ≤ count1153 b) else (if i < 1162 then decide (9 ≤ count1153 b) else decide (10 ≤ count1153 b))) else (if i < 1164 then decide (11 ≤ count1153 b) else (if i < 1165 then decide (12 ≤ count1153 b) else decide (13 ≤ count1153 b)))) else (if i < 1169 then (if i < 1167 then decide (14 ≤ count1153 b) else (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b))) else (if i < 1170 then decide (1 ≤ count1169 b) else (if i < 1171 then decide (2 ≤ count1169 b) else decide (3 ≤ count1169 b))))) else (if i < 1178 then (if i < 1175 then (if i < 1173 then decide (1 ≤ count1172 b) else (if i < 1174 then decide (2 ≤ count1172 b) else decide (1 ≤ count1174 b))) else (if i < 1176 then decide (2 ≤ count1174 b) else (if i < 1177 then decide (1 ≤ count1176 b) else decide (2 ≤ count1176 b)))) else (if i < 1181 then (if i < 1179 then decide (3 ≤ count1176 b) else (if i < 1180 then decide (4 ≤ count1176 b) else decide (1 ≤ count1180 b))) else (if i < 1182 then decide (2 ≤ count1180 b) else (if i < 1183 then decide (3 ≤ count1180 b) else decide (4 ≤ count1180 b)))))) else (if i < 1196 then (if i < 1190 then (if i < 1187 then (if i < 1185 then decide (5 ≤ count1180 b) else (if i < 1186 then decide (6 ≤ count1180 b) else decide (7 ≤ count1180 b))) else (if i < 1188 then decide (1 ≤ count1187 b) else (if i < 1189 then decide (2 ≤ count1187 b) else decide (1 ≤ count1189 b)))) else (if i < 1193 then (if i < 1191 then decide (2 ≤ count1189 b) else (if i < 1192 then decide (3 ≤ count1189 b) else decide (1 ≤ count1192 b))) else (if i < 1194 then decide (2 ≤ count1192 b) else (if i < 1195 then decide (1 ≤ count1194 b) else decide (2 ≤ count1194 b))))) else (if i < 1202 then (if i < 1199 then (if i < 1197 then decide (1 ≤ count1196 b) else (if i < 1198 then decide (2 ≤ count1196 b) else decide (3 ≤ count1196 b))) else (if i < 1200 then decide (4 ≤ count1196 b) else (if i < 1201 then decide (1 ≤ count1200 b) else decide (2 ≤ count1200 b)))) else (if i < 1205 then (if i < 1203 then decide (3 ≤ count1200 b) else (if i < 1204 then decide (4 ≤ count1200 b) else decide (5 ≤ count1200 b))) else (if i < 1206 then decide (6 ≤ count1200 b) else (if i < 1207 then decide (7 ≤ count1200 b) else decide (1 ≤ count1207 b))))))) else (if i < 1232 then (if i < 1220 then (if i < 1214 then (if i < 1211 then (if i < 1209 then decide (2 ≤ count1207 b) else (if i < 1210 then decide (3 ≤ count1207 b) else decide (4 ≤ count1207 b))) else (if i < 1212 then decide (5 ≤ count1207 b) else (if i < 1213 then decide (6 ≤ count1207 b) else decide (7 ≤ count1207 b)))) else (if i < 1217 then (if i < 1215 then decide (8 ≤ count1207 b) else (if i < 1216 then decide (9 ≤ count1207 b) else decide (10 ≤ count1207 b))) else (if i < 1218 then decide (11 ≤ count1207 b) else (if i < 1219 then decide (12 ≤ count1207 b) else decide (13 ≤ count1207 b))))) else (if i < 1226 then (if i < 1223 then (if i < 1221 then decide (14 ≤ count1207 b) else (if i < 1222 then decide (1 ≤ count1221 b) else decide (2 ≤ count1221 b))) else (if i < 1224 then decide (3 ≤ count1221 b) else (if i < 1225 then decide (4 ≤ count1221 b) else decide (5 ≤ count1221 b)))) else (if i < 1229 then (if i < 1227 then decide (6 ≤ count1221 b) else (if i < 1228 then decide (7 ≤ count1221 b) else decide (8 ≤ count1221 b))) else (if i < 1230 then decide (9 ≤ count1221 b) else (if i < 1231 then decide (10 ≤ count1221 b) else decide (11 ≤ count1221 b)))))) else (if i < 1244 then (if i < 1238 then (if i < 1235 then (if i < 1233 then decide (12 ≤ count1221 b) else (if i < 1234 then decide (13 ≤ count1221 b) else decide (14 ≤ count1221 b))) else (if i < 1236 then decide (15 ≤ count1221 b) else (if i < 1237 then decide (16 ≤ count1221 b) else decide (17 ≤ count1221 b)))) else (if i < 1241 then (if i < 1239 then decide (18 ≤ count1221 b) else (if i < 1240 then decide (19 ≤ count1221 b) else decide (20 ≤ count1221 b))) else (if i < 1242 then decide (21 ≤ count1221 b) else (if i < 1243 then decide (22 ≤ count1221 b) else decide (23 ≤ count1221 b))))) else (if i < 1250 then (if i < 1247 then (if i < 1245 then decide (24 ≤ count1221 b) else (if i < 1246 then decide (25 ≤ count1221 b) else decide (26 ≤ count1221 b))) else (if i < 1248 then decide (27 ≤ count1221 b) else (if i < 1249 then decide (28 ≤ count1221 b) else decide (1 ≤ count1249 b)))) else (if i < 1253 then (if i < 1251 then decide (2 ≤ count1249 b) else (if i < 1252 then decide (3 ≤ count1249 b) else decide (4 ≤ count1249 b))) else (if i < 1254 then decide (5 ≤ count1249 b) else (if i < 1255 then decide (6 ≤ count1249 b) else decide (7 ≤ count1249 b)))))))) else (if i < 1304 then (if i < 1280 then (if i < 1268 then (if i < 1262 then (if i < 1259 then (if i < 1257 then decide (8 ≤ count1249 b) else (if i < 1258 then decide (9 ≤ count1249 b) else decide (10 ≤ count1249 b))) else (if i < 1260 then decide (11 ≤ count1249 b) else (if i < 1261 then decide (12 ≤ count1249 b) else decide (13 ≤ count1249 b)))) else (if i < 1265 then (if i < 1263 then decide (14 ≤ count1249 b) else (if i < 1264 then decide (15 ≤ count1249 b) else decide (16 ≤ count1249 b))) else (if i < 1266 then decide (17 ≤ count1249 b) else (if i < 1267 then decide (18 ≤ count1249 b) else decide (19 ≤ count1249 b))))) else (if i < 1274 then (if i < 1271 then (if i < 1269 then decide (20 ≤ count1249 b) else (if i < 1270 then decide (21 ≤ count1249 b) else decide (22 ≤ count1249 b))) else (if i < 1272 then decide (23 ≤ count1249 b) else (if i < 1273 then decide (24 ≤ count1249 b) else decide (25 ≤ count1249 b)))) else (if i < 1277 then (if i < 1275 then decide (26 ≤ count1249 b) else (if i < 1276 then decide (27 ≤ count1249 b) else decide (28 ≤ count1249 b))) else (if i < 1278 then decide (29 ≤ count1249 b) else (if i < 1279 then decide (30 ≤ count1249 b) else decide (31 ≤ count1249 b)))))) else (if i < 1292 then (if i < 1286 then (if i < 1283 then (if i < 1281 then decide (32 ≤ count1249 b) else (if i < 1282 then decide (33 ≤ count1249 b) else decide (34 ≤ count1249 b))) else (if i < 1284 then decide (35 ≤ count1249 b) else (if i < 1285 then decide (36 ≤ count1249 b) else decide (37 ≤ count1249 b)))) else (if i < 1289 then (if i < 1287 then decide (38 ≤ count1249 b) else (if i < 1288 then decide (39 ≤ count1249 b) else decide (40 ≤ count1249 b))) else (if i < 1290 then decide (41 ≤ count1249 b) else (if i < 1291 then decide (42 ≤ count1249 b) else decide (1 ≤ count1291 b))))) else (if i < 1298 then (if i < 1295 then (if i < 1293 then decide (2 ≤ count1291 b) else (if i < 1294 then decide (1 ≤ count1293 b) else decide (2 ≤ count1293 b))) else (if i < 1296 then decide (3 ≤ count1293 b) else (if i < 1297 then decide (1 ≤ count1296 b) else decide (2 ≤ count1296 b)))) else (if i < 1301 then (if i < 1299 then decide (1 ≤ count1298 b) else (if i < 1300 then decide (2 ≤ count1298 b) else decide (3 ≤ count1298 b))) else (if i < 1302 then decide (1 ≤ count1301 b) else (if i < 1303 then decide (2 ≤ count1301 b) else decide (3 ≤ count1301 b))))))) else (if i < 1328 then (if i < 1316 then (if i < 1310 then (if i < 1307 then (if i < 1305 then decide (4 ≤ count1301 b) else (if i < 1306 then decide (5 ≤ count1301 b) else decide (6 ≤ count1301 b))) else (if i < 1308 then decide (1 ≤ count1307 b) else (if i < 1309 then decide (2 ≤ count1307 b) else decide (1 ≤ count1309 b)))) else (if i < 1313 then (if i < 1311 then decide (2 ≤ count1309 b) else (if i < 1312 then decide (3 ≤ count1309 b) else decide (1 ≤ count1312 b))) else (if i < 1314 then decide (2 ≤ count1312 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))))) else (if i < 1322 then (if i < 1319 then (if i < 1317 then decide (1 ≤ count1316 b) else (if i < 1318 then decide (2 ≤ count1316 b) else decide (3 ≤ count1316 b))) else (if i < 1320 then decide (4 ≤ count1316 b) else (if i < 1321 then decide (1 ≤ count1320 b) else decide (2 ≤ count1320 b)))) else (if i < 1325 then (if i < 1323 then decide (3 ≤ count1320 b) else (if i < 1324 then decide (4 ≤ count1320 b) else decide (5 ≤ count1320 b))) else (if i < 1326 then decide (6 ≤ count1320 b) else (if i < 1327 then decide (7 ≤ count1320 b) else decide (1 ≤ count1327 b)))))) else (if i < 1340 then (if i < 1334 then (if i < 1331 then (if i < 1329 then decide (2 ≤ count1327 b) else (if i < 1330 then decide (3 ≤ count1327 b) else decide (4 ≤ count1327 b))) else (if i < 1332 then decide (5 ≤ count1327 b) else (if i < 1333 then decide (6 ≤ count1327 b) else decide (7 ≤ count1327 b)))) else (if i < 1337 then (if i < 1335 then decide (8 ≤ count1327 b) else (if i < 1336 then decide (9 ≤ count1327 b) else decide (10 ≤ count1327 b))) else (if i < 1338 then decide (11 ≤ count1327 b) else (if i < 1339 then decide (12 ≤ count1327 b) else decide (13 ≤ count1327 b))))) else (if i < 1346 then (if i < 1343 then (if i < 1341 then decide (1 ≤ count1340 b) else (if i < 1342 then decide (2 ≤ count1340 b) else decide (1 ≤ count1342 b))) else (if i < 1344 then decide (2 ≤ count1342 b) else (if i < 1345 then decide (3 ≤ count1342 b) else decide (1 ≤ count1345 b)))) else (if i < 1349 then (if i < 1347 then decide (2 ≤ count1345 b) else (if i < 1348 then decide (1 ≤ count1347 b) else decide (2 ≤ count1347 b))) else (if i < 1351 then (if i < 1350 then decide (1 ≤ count1349 b) else decide (2 ≤ count1349 b)) else (if i < 1352 then decide (3 ≤ count1349 b) else decide (4 ≤ count1349 b))))))))) else (if i < 1450 then (if i < 1401 then (if i < 1377 then (if i < 1365 then (if i < 1359 then (if i < 1356 then (if i < 1354 then decide (1 ≤ count1353 b) else (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b))) else (if i < 1357 then decide (4 ≤ count1353 b) else (if i < 1358 then decide (5 ≤ count1353 b) else decide (6 ≤ count1353 b)))) else (if i < 1362 then (if i < 1360 then decide (7 ≤ count1353 b) else (if i < 1361 then decide (1 ≤ count1360 b) else decide (2 ≤ count1360 b))) else (if i < 1363 then decide (1 ≤ count1362 b) else (if i < 1364 then decide (2 ≤ count1362 b) else decide (3 ≤ count1362 b))))) else (if i < 1371 then (if i < 1368 then (if i < 1366 then decide (1 ≤ count1365 b) else (if i < 1367 then decide (2 ≤ count1365 b) else decide (1 ≤ count1367 b))) else (if i < 1369 then decide (2 ≤ count1367 b) else (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)))) else (if i < 1374 then (if i < 1372 then decide (3 ≤ count1369 b) else (if i < 1373 then decide (4 ≤ count1369 b) else decide (1 ≤ count1373 b))) else (if i < 1375 then decide (2 ≤ count1373 b) else (if i < 1376 then decide (3 ≤ count1373 b) else decide (4 ≤ count1373 b)))))) else (if i < 1389 then (if i < 1383 then (if i < 1380 then (if i < 1378 then decide (5 ≤ count1373 b) else (if i < 1379 then decide (6 ≤ count1373 b) else decide (7 ≤ count1373 b))) else (if i < 1381 then decide (1 ≤ count1380 b) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (3 ≤ count1380 b)))) else (if i < 1386 then (if i < 1384 then decide (4 ≤ count1380 b) else (if i < 1385 then decide (5 ≤ count1380 b) else decide (6 ≤ count1380 b))) else (if i < 1387 then decide (7 ≤ count1380 b) else (if i < 1388 then decide (8 ≤ count1380 b) else decide (9 ≤ count1380 b))))) else (if i < 1395 then (if i < 1392 then (if i < 1390 then decide (10 ≤ count1380 b) else (if i < 1391 then decide (11 ≤ count1380 b) else decide (12 ≤ count1380 b))) else (if i < 1393 then decide (13 ≤ count1380 b) else (if i < 1394 then decide (14 ≤ count1380 b) else decide (1 ≤ count1394 b)))) else (if i < 1398 then (if i < 1396 then decide (2 ≤ count1394 b) else (if i < 1397 then decide (3 ≤ count1394 b) else decide (4 ≤ count1394 b))) else (if i < 1399 then decide (5 ≤ count1394 b) else (if i < 1400 then decide (6 ≤ count1394 b) else decide (7 ≤ count1394 b))))))) else (if i < 1425 then (if i < 1413 then (if i < 1407 then (if i < 1404 then (if i < 1402 then decide (8 ≤ count1394 b) else (if i < 1403 then decide (9 ≤ count1394 b) else decide (10 ≤ count1394 b))) else (if i < 1405 then decide (11 ≤ count1394 b) else (if i < 1406 then decide (12 ≤ count1394 b) else decide (13 ≤ count1394 b)))) else (if i < 1410 then (if i < 1408 then decide (14 ≤ count1394 b) else (if i < 1409 then decide (15 ≤ count1394 b) else decide (1 ≤ count1409 b))) else (if i < 1411 then decide (2 ≤ count1409 b) else (if i < 1412 then decide (1 ≤ count1411 b) else decide (2 ≤ count1411 b))))) else (if i < 1419 then (if i < 1416 then (if i < 1414 then decide (3 ≤ count1411 b) else (if i < 1415 then decide (1 ≤ count1414 b) else decide (2 ≤ count1414 b))) else (if i < 1417 then decide (1 ≤ count1416 b) else (if i < 1418 then decide (2 ≤ count1416 b) else decide (1 ≤ count1418 b)))) else (if i < 1422 then (if i < 1420 then decide (2 ≤ count1418 b) else (if i < 1421 then decide (3 ≤ count1418 b) else decide (4 ≤ count1418 b))) else (if i < 1423 then decide (1 ≤ count1422 b) else (if i < 1424 then decide (2 ≤ count1422 b) else decide (3 ≤ count1422 b)))))) else (if i < 1437 then (if i < 1431 then (if i < 1428 then (if i < 1426 then decide (4 ≤ count1422 b) else (if i < 1427 then decide (5 ≤ count1422 b) else decide (6 ≤ count1422 b))) else (if i < 1429 then decide (7 ≤ count1422 b) else (if i < 1430 then decide (1 ≤ count1429 b) else decide (2 ≤ count1429 b)))) else (if i < 1434 then (if i < 1432 then decide (1 ≤ count1431 b) else (if i < 1433 then decide (2 ≤ count1431 b) else decide (3 ≤ count1431 b))) else (if i < 1435 then decide (1 ≤ count1434 b) else (if i < 1436 then decide (2 ≤ count1434 b) else decide (1 ≤ count1436 b))))) else (if i < 1443 then (if i < 1440 then (if i < 1438 then decide (2 ≤ count1436 b) else (if i < 1439 then decide (1 ≤ count1438 b) else decide (2 ≤ count1438 b))) else (if i < 1441 then decide (3 ≤ count1438 b) else (if i < 1442 then decide (4 ≤ count1438 b) else decide (1 ≤ count1442 b)))) else (if i < 1446 then (if i < 1444 then decide (2 ≤ count1442 b) else (if i < 1445 then decide (3 ≤ count1442 b) else decide (4 ≤ count1442 b))) else (if i < 1448 then (if i < 1447 then decide (5 ≤ count1442 b) else decide (6 ≤ count1442 b)) else (if i < 1449 then decide (7 ≤ count1442 b) else decide (1 ≤ count1449 b)))))))) else (if i < 1498 then (if i < 1474 then (if i < 1462 then (if i < 1456 then (if i < 1453 then (if i < 1451 then decide (2 ≤ count1449 b) else (if i < 1452 then decide (3 ≤ count1449 b) else decide (4 ≤ count1449 b))) else (if i < 1454 then decide (5 ≤ count1449 b) else (if i < 1455 then decide (6 ≤ count1449 b) else decide (7 ≤ count1449 b)))) else (if i < 1459 then (if i < 1457 then decide (8 ≤ count1449 b) else (if i < 1458 then decide (9 ≤ count1449 b) else decide (10 ≤ count1449 b))) else (if i < 1460 then decide (11 ≤ count1449 b) else (if i < 1461 then decide (12 ≤ count1449 b) else decide (13 ≤ count1449 b))))) else (if i < 1468 then (if i < 1465 then (if i < 1463 then decide (14 ≤ count1449 b) else (if i < 1464 then decide (1 ≤ count1463 b) else decide (2 ≤ count1463 b))) else (if i < 1466 then decide (1 ≤ count1465 b) else (if i < 1467 then decide (2 ≤ count1465 b) else decide (3 ≤ count1465 b)))) else (if i < 1471 then (if i < 1469 then decide (1 ≤ count1468 b) else (if i < 1470 then decide (2 ≤ count1468 b) else decide (1 ≤ count1470 b))) else (if i < 1472 then decide (2 ≤ count1470 b) else (if i < 1473 then decide (1 ≤ count1472 b) else decide (2 ≤ count1472 b)))))) else (if i < 1486 then (if i < 1480 then (if i < 1477 then (if i < 1475 then decide (3 ≤ count1472 b) else (if i < 1476 then decide (4 ≤ count1472 b) else decide (1 ≤ count1476 b))) else (if i < 1478 then decide (2 ≤ count1476 b) else (if i < 1479 then decide (3 ≤ count1476 b) else decide (4 ≤ count1476 b)))) else (if i < 1483 then (if i < 1481 then decide (5 ≤ count1476 b) else (if i < 1482 then decide (6 ≤ count1476 b) else decide (7 ≤ count1476 b))) else (if i < 1484 then decide (1 ≤ count1483 b) else (if i < 1485 then decide (2 ≤ count1483 b) else decide (1 ≤ count1485 b))))) else (if i < 1492 then (if i < 1489 then (if i < 1487 then decide (2 ≤ count1485 b) else (if i < 1488 then decide (3 ≤ count1485 b) else decide (1 ≤ count1488 b))) else (if i < 1490 then decide (2 ≤ count1488 b) else (if i < 1491 then decide (1 ≤ count1490 b) else decide (2 ≤ count1490 b)))) else (if i < 1495 then (if i < 1493 then decide (1 ≤ count1492 b) else (if i < 1494 then decide (2 ≤ count1492 b) else decide (3 ≤ count1492 b))) else (if i < 1496 then decide (4 ≤ count1492 b) else (if i < 1497 then decide (1 ≤ count1496 b) else decide (2 ≤ count1496 b))))))) else (if i < 1522 then (if i < 1510 then (if i < 1504 then (if i < 1501 then (if i < 1499 then decide (3 ≤ count1496 b) else (if i < 1500 then decide (4 ≤ count1496 b) else decide (5 ≤ count1496 b))) else (if i < 1502 then decide (6 ≤ count1496 b) else (if i < 1503 then decide (7 ≤ count1496 b) else decide (1 ≤ count1503 b)))) else (if i < 1507 then (if i < 1505 then decide (2 ≤ count1503 b) else (if i < 1506 then decide (3 ≤ count1503 b) else decide (4 ≤ count1503 b))) else (if i < 1508 then decide (5 ≤ count1503 b) else (if i < 1509 then decide (6 ≤ count1503 b) else decide (7 ≤ count1503 b))))) else (if i < 1516 then (if i < 1513 then (if i < 1511 then decide (8 ≤ count1503 b) else (if i < 1512 then decide (9 ≤ count1503 b) else decide (10 ≤ count1503 b))) else (if i < 1514 then decide (11 ≤ count1503 b) else (if i < 1515 then decide (12 ≤ count1503 b) else decide (13 ≤ count1503 b)))) else (if i < 1519 then (if i < 1517 then decide (14 ≤ count1503 b) else (if i < 1518 then decide (1 ≤ count1517 b) else decide (2 ≤ count1517 b))) else (if i < 1520 then decide (3 ≤ count1517 b) else (if i < 1521 then decide (4 ≤ count1517 b) else decide (5 ≤ count1517 b)))))) else (if i < 1534 then (if i < 1528 then (if i < 1525 then (if i < 1523 then decide (6 ≤ count1517 b) else (if i < 1524 then decide (7 ≤ count1517 b) else decide (8 ≤ count1517 b))) else (if i < 1526 then decide (9 ≤ count1517 b) else (if i < 1527 then decide (10 ≤ count1517 b) else decide (11 ≤ count1517 b)))) else (if i < 1531 then (if i < 1529 then decide (12 ≤ count1517 b) else (if i < 1530 then decide (13 ≤ count1517 b) else decide (14 ≤ count1517 b))) else (if i < 1532 then decide (15 ≤ count1517 b) else (if i < 1533 then decide (1 ≤ count1532 b) else decide (2 ≤ count1532 b))))) else (if i < 1540 then (if i < 1537 then (if i < 1535 then decide (3 ≤ count1532 b) else (if i < 1536 then decide (4 ≤ count1532 b) else decide (5 ≤ count1532 b))) else (if i < 1538 then decide (6 ≤ count1532 b) else (if i < 1539 then decide (7 ≤ count1532 b) else decide (8 ≤ count1532 b)))) else (if i < 1543 then (if i < 1541 then decide (9 ≤ count1532 b) else (if i < 1542 then decide (10 ≤ count1532 b) else decide (11 ≤ count1532 b))) else (if i < 1545 then (if i < 1544 then decide (12 ≤ count1532 b) else decide (13 ≤ count1532 b)) else (if i < 1546 then decide (14 ≤ count1532 b) else decide (15 ≤ count1532 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (5 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (11 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (13 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (17 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (21 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (23 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (25 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (26 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (27 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (45 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (109 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (162 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (164 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (165 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (170 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (171 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (172 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (173 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (177 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (181 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (182 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (185 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (186 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (187 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (194 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (196 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (197 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (202 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (203 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (205 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (213 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (214 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (217 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (218 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (219 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (222 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (257 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (259 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (261 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (267 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (268 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (269 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (270 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (271 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (272 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (273 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (274 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (275 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (278 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (280 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (284 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (285 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (286 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (287 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (320 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (322 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (324 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (325 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (330 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (331 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (332 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (333 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (337 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (341 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (342 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (343 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (345 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (346 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (347 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (350 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (417 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (419 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (421 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (427 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (428 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (429 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (430 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (431 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (432 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (433 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (434 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (435 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (438 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (440 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (444 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (445 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (446 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (447 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (461 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (477 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (478 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (479 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (485 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (491 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (493 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (501 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (505 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (506 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (507 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (510 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (5 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (21 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (23 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (26 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (162 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (164 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (173 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (182 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (185 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (186 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (194 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (203 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (270 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (271 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (285 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (322 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (324 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (347 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (431 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (444 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (445 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (477 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (2 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (2 ≤ count241 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value320 (q : Snake 81) : valuation q 320 = decide (2 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value322 (q : Snake 81) : valuation q 322 = decide (2 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value430 (q : Snake 81) : valuation q 430 = decide (2 ≤ count429 (baseVal q)) := rfl
theorem value432 (q : Snake 81) : valuation q 432 = decide (2 ≤ count431 (baseVal q)) := rfl
theorem value1291 (q : Snake 81) : valuation q 1291 = decide (1 ≤ count1291 (baseVal q)) := rfl
theorem value1292 (q : Snake 81) : valuation q 1292 = decide (2 ≤ count1291 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (1 ≤ count1293 (baseVal q)) := rfl
theorem value1294 (q : Snake 81) : valuation q 1294 = decide (2 ≤ count1293 (baseVal q)) := rfl
theorem value1295 (q : Snake 81) : valuation q 1295 = decide (3 ≤ count1293 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (1 ≤ count1296 (baseVal q)) := rfl
theorem value1298 (q : Snake 81) : valuation q 1298 = decide (1 ≤ count1298 (baseVal q)) := rfl
theorem value1299 (q : Snake 81) : valuation q 1299 = decide (2 ≤ count1298 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (1 ≤ count1301 (baseVal q)) := rfl
theorem value1302 (q : Snake 81) : valuation q 1302 = decide (2 ≤ count1301 (baseVal q)) := rfl
theorem value1303 (q : Snake 81) : valuation q 1303 = decide (3 ≤ count1301 (baseVal q)) := rfl
theorem value1304 (q : Snake 81) : valuation q 1304 = decide (4 ≤ count1301 (baseVal q)) := rfl
theorem value1307 (q : Snake 81) : valuation q 1307 = decide (1 ≤ count1307 (baseVal q)) := rfl
theorem value1308 (q : Snake 81) : valuation q 1308 = decide (2 ≤ count1307 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (1 ≤ count1309 (baseVal q)) := rfl
theorem value1310 (q : Snake 81) : valuation q 1310 = decide (2 ≤ count1309 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (1 ≤ count1312 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (2 ≤ count1312 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (1 ≤ count1314 (baseVal q)) := rfl
theorem value1316 (q : Snake 81) : valuation q 1316 = decide (1 ≤ count1316 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (2 ≤ count1316 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (1 ≤ count1320 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (2 ≤ count1320 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (3 ≤ count1320 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (1 ≤ count1327 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (2 ≤ count1327 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (3 ≤ count1327 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (4 ≤ count1327 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (5 ≤ count1327 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (6 ≤ count1327 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (7 ≤ count1327 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (1 ≤ count1342 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (2 ≤ count1342 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (1 ≤ count1345 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (1 ≤ count1347 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (2 ≤ count1349 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (1 ≤ count1353 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (2 ≤ count1353 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (3 ≤ count1353 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (1 ≤ count1360 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (2 ≤ count1360 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (1 ≤ count1362 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (2 ≤ count1362 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (1 ≤ count1365 (baseVal q)) := rfl
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (2 ≤ count1365 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (1 ≤ count1367 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (2 ≤ count1367 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (1 ≤ count1369 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (2 ≤ count1369 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (3 ≤ count1369 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (4 ≤ count1369 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (1 ≤ count1373 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (2 ≤ count1373 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (3 ≤ count1373 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (4 ≤ count1373 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (5 ≤ count1373 (baseVal q)) := rfl
theorem value1380 (q : Snake 81) : valuation q 1380 = decide (1 ≤ count1380 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (2 ≤ count1380 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (3 ≤ count1380 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (4 ≤ count1380 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (5 ≤ count1380 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (6 ≤ count1380 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (5 ≤ count1394 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (6 ≤ count1394 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (7 ≤ count1394 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (8 ≤ count1394 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (9 ≤ count1394 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (1 ≤ count1409 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (2 ≤ count1409 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (1 ≤ count1411 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (2 ≤ count1411 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (3 ≤ count1411 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (1 ≤ count1414 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (2 ≤ count1414 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (1 ≤ count1416 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (2 ≤ count1416 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (1 ≤ count1418 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (2 ≤ count1418 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (3 ≤ count1418 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (1 ≤ count1422 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (2 ≤ count1422 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (3 ≤ count1422 (baseVal q)) := rfl
theorem value1425 (q : Snake 81) : valuation q 1425 = decide (4 ≤ count1422 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (5 ≤ count1422 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (1 ≤ count1429 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (2 ≤ count1429 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (1 ≤ count1431 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (2 ≤ count1431 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (3 ≤ count1431 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (1 ≤ count1434 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (2 ≤ count1434 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (1 ≤ count1436 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (1 ≤ count1438 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (2 ≤ count1438 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (3 ≤ count1438 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (1 ≤ count1442 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (2 ≤ count1442 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (3 ≤ count1442 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (4 ≤ count1442 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (2 ≤ count1449 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (3 ≤ count1449 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (4 ≤ count1449 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (5 ≤ count1449 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (6 ≤ count1449 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (7 ≤ count1449 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (8 ≤ count1449 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (1 ≤ count1463 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (2 ≤ count1463 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (1 ≤ count1465 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (2 ≤ count1465 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (3 ≤ count1465 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (1 ≤ count1468 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (2 ≤ count1468 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (1 ≤ count1470 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (2 ≤ count1470 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (1 ≤ count1472 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (2 ≤ count1472 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (3 ≤ count1472 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (1 ≤ count1476 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (2 ≤ count1476 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (3 ≤ count1476 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (4 ≤ count1476 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (5 ≤ count1476 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (1 ≤ count1483 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (2 ≤ count1483 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (1 ≤ count1485 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (1 ≤ count1488 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (1 ≤ count1490 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (1 ≤ count1492 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (2 ≤ count1492 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (1 ≤ count1496 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (2 ≤ count1496 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (3 ≤ count1496 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (1 ≤ count1503 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (2 ≤ count1503 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (3 ≤ count1503 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (4 ≤ count1503 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (5 ≤ count1503 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (6 ≤ count1503 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (7 ≤ count1503 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (6 ≤ count1517 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (7 ≤ count1517 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (8 ≤ count1517 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (9 ≤ count1517 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (10 ≤ count1517 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (15 ≤ count1532 (baseVal q)) := rfl
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
theorem meaningNeg101 (b : Nat → Bool) : literal (valuationOf b) (-101) = decide (1 ≤ countLit b [-101]) := by
  change literal b (-101) = decide (1 ≤ countLit b [-101])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-101) <;> decide
theorem meaningNeg98 (b : Nat → Bool) : literal (valuationOf b) (-98) = decide (1 ≤ countLit b [-98]) := by
  change literal b (-98) = decide (1 ≤ countLit b [-98])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-98) <;> decide
theorem meaningNeg97 (b : Nat → Bool) : literal (valuationOf b) (-97) = decide (1 ≤ countLit b [-97]) := by
  change literal b (-97) = decide (1 ≤ countLit b [-97])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-97) <;> decide
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
theorem meaningNeg70 (b : Nat → Bool) : literal (valuationOf b) (-70) = decide (1 ≤ countLit b [-70]) := by
  change literal b (-70) = decide (1 ≤ countLit b [-70])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-70) <;> decide
theorem meaningNeg68 (b : Nat → Bool) : literal (valuationOf b) (-68) = decide (1 ≤ countLit b [-68]) := by
  change literal b (-68) = decide (1 ≤ countLit b [-68])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-68) <;> decide
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
theorem meaningNeg56 (b : Nat → Bool) : literal (valuationOf b) (-56) = decide (1 ≤ countLit b [-56]) := by
  change literal b (-56) = decide (1 ≤ countLit b [-56])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-56) <;> decide
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
theorem meaningNeg19 (b : Nat → Bool) : literal (valuationOf b) (-19) = decide (1 ≤ countLit b [-19]) := by
  change literal b (-19) = decide (1 ≤ countLit b [-19])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-19) <;> decide
theorem meaningNeg17 (b : Nat → Bool) : literal (valuationOf b) (-17) = decide (1 ≤ countLit b [-17]) := by
  change literal b (-17) = decide (1 ≤ countLit b [-17])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-17) <;> decide
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
theorem meaningNeg5 (b : Nat → Bool) : literal (valuationOf b) (-5) = decide (1 ≤ countLit b [-5]) := by
  change literal b (-5) = decide (1 ≤ countLit b [-5])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-5) <;> decide
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
theorem meaning110 (b : Nat → Bool) : literal (valuationOf b) (110) = decide (1 ≤ countLit b [110]) := by
  change literal b (110) = decide (1 ≤ countLit b [110])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (110) <;> decide
theorem meaning113 (b : Nat → Bool) : literal (valuationOf b) (113) = decide (1 ≤ countLit b [113]) := by
  change literal b (113) = decide (1 ≤ countLit b [113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (113) <;> decide
theorem meaning115 (b : Nat → Bool) : literal (valuationOf b) (115) = decide (1 ≤ countLit b [115]) := by
  change literal b (115) = decide (1 ≤ countLit b [115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (115) <;> decide
theorem meaning118 (b : Nat → Bool) : literal (valuationOf b) (118) = decide (1 ≤ countLit b [118]) := by
  change literal b (118) = decide (1 ≤ countLit b [118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (118) <;> decide
theorem meaning151 (b : Nat → Bool) : literal (valuationOf b) (151) = decide (1 ≤ countLit b [151]) := by
  change literal b (151) = decide (1 ≤ countLit b [151])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (151) <;> decide
theorem meaning152 (b : Nat → Bool) : literal (valuationOf b) (152) = decide (1 ≤ countLit b [152]) := by
  change literal b (152) = decide (1 ≤ countLit b [152])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (152) <;> decide
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
theorem meaning169 (b : Nat → Bool) : literal (valuationOf b) (169) = decide (1 ≤ countLit b [169]) := by
  change literal b (169) = decide (1 ≤ countLit b [169])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (169) <;> decide
theorem meaning170 (b : Nat → Bool) : literal (valuationOf b) (170) = decide (1 ≤ countLit b [170]) := by
  change literal b (170) = decide (1 ≤ countLit b [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (170) <;> decide
theorem meaning176 (b : Nat → Bool) : literal (valuationOf b) (176) = decide (1 ≤ countLit b [176]) := by
  change literal b (176) = decide (1 ≤ countLit b [176])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (176) <;> decide
theorem meaning178 (b : Nat → Bool) : literal (valuationOf b) (178) = decide (1 ≤ countLit b [178]) := by
  change literal b (178) = decide (1 ≤ countLit b [178])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (178) <;> decide
theorem meaning184 (b : Nat → Bool) : literal (valuationOf b) (184) = decide (1 ≤ countLit b [184]) := by
  change literal b (184) = decide (1 ≤ countLit b [184])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (184) <;> decide
theorem meaning192 (b : Nat → Bool) : literal (valuationOf b) (192) = decide (1 ≤ countLit b [192]) := by
  change literal b (192) = decide (1 ≤ countLit b [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (192) <;> decide
theorem meaning197 (b : Nat → Bool) : literal (valuationOf b) (197) = decide (1 ≤ countLit b [197]) := by
  change literal b (197) = decide (1 ≤ countLit b [197])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (197) <;> decide
theorem meaning200 (b : Nat → Bool) : literal (valuationOf b) (200) = decide (1 ≤ countLit b [200]) := by
  change literal b (200) = decide (1 ≤ countLit b [200])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (200) <;> decide
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) 228 = decide (2 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) 242 = decide (2 ≤ count241 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning320 (b : Nat → Bool) : literal (valuationOf b) 320 = decide (2 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning322 (b : Nat → Bool) : literal (valuationOf b) 322 = decide (2 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning430 (b : Nat → Bool) : literal (valuationOf b) 430 = decide (2 ≤ count429 b) := rfl
theorem meaning432 (b : Nat → Bool) : literal (valuationOf b) 432 = decide (2 ≤ count431 b) := rfl
theorem meaning1291 (b : Nat → Bool) : literal (valuationOf b) 1291 = decide (1 ≤ count1291 b) := rfl
theorem meaning1292 (b : Nat → Bool) : literal (valuationOf b) 1292 = decide (2 ≤ count1291 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (1 ≤ count1293 b) := rfl
theorem meaning1294 (b : Nat → Bool) : literal (valuationOf b) 1294 = decide (2 ≤ count1293 b) := rfl
theorem meaning1295 (b : Nat → Bool) : literal (valuationOf b) 1295 = decide (3 ≤ count1293 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (1 ≤ count1296 b) := rfl
theorem meaning1298 (b : Nat → Bool) : literal (valuationOf b) 1298 = decide (1 ≤ count1298 b) := rfl
theorem meaning1299 (b : Nat → Bool) : literal (valuationOf b) 1299 = decide (2 ≤ count1298 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (1 ≤ count1301 b) := rfl
theorem meaning1302 (b : Nat → Bool) : literal (valuationOf b) 1302 = decide (2 ≤ count1301 b) := rfl
theorem meaning1303 (b : Nat → Bool) : literal (valuationOf b) 1303 = decide (3 ≤ count1301 b) := rfl
theorem meaning1304 (b : Nat → Bool) : literal (valuationOf b) 1304 = decide (4 ≤ count1301 b) := rfl
theorem meaning1307 (b : Nat → Bool) : literal (valuationOf b) 1307 = decide (1 ≤ count1307 b) := rfl
theorem meaning1308 (b : Nat → Bool) : literal (valuationOf b) 1308 = decide (2 ≤ count1307 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (1 ≤ count1309 b) := rfl
theorem meaning1310 (b : Nat → Bool) : literal (valuationOf b) 1310 = decide (2 ≤ count1309 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (1 ≤ count1312 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (2 ≤ count1312 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (1 ≤ count1314 b) := rfl
theorem meaning1316 (b : Nat → Bool) : literal (valuationOf b) 1316 = decide (1 ≤ count1316 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (2 ≤ count1316 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (1 ≤ count1320 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (2 ≤ count1320 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (3 ≤ count1320 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (1 ≤ count1327 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (2 ≤ count1327 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (3 ≤ count1327 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (4 ≤ count1327 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (5 ≤ count1327 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (6 ≤ count1327 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (7 ≤ count1327 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (1 ≤ count1342 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (2 ≤ count1342 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (1 ≤ count1345 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (1 ≤ count1347 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (2 ≤ count1349 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (1 ≤ count1353 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (2 ≤ count1353 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (3 ≤ count1353 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (1 ≤ count1360 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (2 ≤ count1360 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (1 ≤ count1362 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (2 ≤ count1362 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (1 ≤ count1365 b) := rfl
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (2 ≤ count1365 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (1 ≤ count1367 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (2 ≤ count1367 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (1 ≤ count1369 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (2 ≤ count1369 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (3 ≤ count1369 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (4 ≤ count1369 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (1 ≤ count1373 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (2 ≤ count1373 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (3 ≤ count1373 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (4 ≤ count1373 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (5 ≤ count1373 b) := rfl
theorem meaning1380 (b : Nat → Bool) : literal (valuationOf b) 1380 = decide (1 ≤ count1380 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (2 ≤ count1380 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (3 ≤ count1380 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (4 ≤ count1380 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (5 ≤ count1380 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (6 ≤ count1380 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (5 ≤ count1394 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (6 ≤ count1394 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (7 ≤ count1394 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (8 ≤ count1394 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (9 ≤ count1394 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (1 ≤ count1409 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (2 ≤ count1409 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (1 ≤ count1411 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (2 ≤ count1411 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (3 ≤ count1411 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (1 ≤ count1414 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (2 ≤ count1414 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (1 ≤ count1416 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (2 ≤ count1416 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (1 ≤ count1418 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (2 ≤ count1418 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (3 ≤ count1418 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (1 ≤ count1422 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (2 ≤ count1422 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (3 ≤ count1422 b) := rfl
theorem meaning1425 (b : Nat → Bool) : literal (valuationOf b) 1425 = decide (4 ≤ count1422 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (5 ≤ count1422 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (1 ≤ count1429 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (2 ≤ count1429 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (1 ≤ count1431 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (2 ≤ count1431 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (3 ≤ count1431 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (1 ≤ count1434 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (2 ≤ count1434 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (1 ≤ count1436 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (1 ≤ count1438 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (2 ≤ count1438 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (3 ≤ count1438 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (1 ≤ count1442 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (2 ≤ count1442 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (3 ≤ count1442 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (4 ≤ count1442 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (2 ≤ count1449 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (3 ≤ count1449 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (4 ≤ count1449 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (5 ≤ count1449 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (6 ≤ count1449 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (7 ≤ count1449 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (8 ≤ count1449 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (1 ≤ count1463 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (2 ≤ count1463 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (1 ≤ count1465 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (2 ≤ count1465 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (3 ≤ count1465 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (1 ≤ count1468 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (2 ≤ count1468 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (1 ≤ count1470 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (2 ≤ count1470 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (1 ≤ count1472 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (2 ≤ count1472 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (3 ≤ count1472 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (1 ≤ count1476 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (2 ≤ count1476 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (3 ≤ count1476 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (4 ≤ count1476 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (5 ≤ count1476 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (1 ≤ count1483 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (2 ≤ count1483 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (1 ≤ count1485 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (2 ≤ count1485 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (1 ≤ count1488 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (1 ≤ count1490 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (1 ≤ count1492 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (2 ≤ count1492 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (1 ≤ count1496 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (2 ≤ count1496 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (3 ≤ count1496 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (1 ≤ count1503 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (2 ≤ count1503 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (3 ≤ count1503 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (4 ≤ count1503 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (5 ≤ count1503 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (6 ≤ count1503 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (7 ≤ count1503 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (6 ≤ count1517 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (7 ≤ count1517 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (8 ≤ count1517 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (9 ≤ count1517 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (10 ≤ count1517 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (15 ≤ count1532 b) := rfl
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
end Snake9.Regrowth.E112166
