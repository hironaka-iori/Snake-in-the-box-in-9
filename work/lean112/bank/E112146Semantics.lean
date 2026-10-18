import E112146Data
namespace Snake9.Regrowth.E112146
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 114 then (if i < 57 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (10 : Vertex)) else decide (InPath q (11 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (13 : Vertex)) else decide (InPath q (24 : Vertex))) else (if i < 6 then decide (InPath q (25 : Vertex)) else decide (InPath q (26 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (29 : Vertex)) else (if i < 9 then decide (InPath q (65 : Vertex)) else decide (InPath q (67 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (69 : Vertex)) else decide (InPath q (71 : Vertex))) else (if i < 13 then decide (InPath q (73 : Vertex)) else decide (InPath q (74 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (75 : Vertex)) else (if i < 16 then decide (InPath q (76 : Vertex)) else decide (InPath q (77 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (78 : Vertex)) else decide (InPath q (79 : Vertex))) else (if i < 20 then decide (InPath q (80 : Vertex)) else decide (InPath q (81 : Vertex))))) else (if i < 24 then (if i < 22 then decide (InPath q (82 : Vertex)) else (if i < 23 then decide (InPath q (84 : Vertex)) else decide (InPath q (88 : Vertex)))) else (if i < 26 then (if i < 25 then decide (InPath q (90 : Vertex)) else decide (InPath q (92 : Vertex))) else (if i < 27 then decide (InPath q (94 : Vertex)) else decide (InPath q (95 : Vertex))))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then decide (InPath q (129 : Vertex)) else (if i < 30 then decide (InPath q (130 : Vertex)) else decide (InPath q (131 : Vertex)))) else (if i < 33 then (if i < 32 then decide (InPath q (133 : Vertex)) else decide (InPath q (135 : Vertex))) else (if i < 34 then decide (InPath q (137 : Vertex)) else decide (InPath q (139 : Vertex))))) else (if i < 38 then (if i < 36 then decide (InPath q (140 : Vertex)) else (if i < 37 then decide (InPath q (141 : Vertex)) else decide (InPath q (143 : Vertex)))) else (if i < 40 then (if i < 39 then decide (InPath q (144 : Vertex)) else decide (InPath q (145 : Vertex))) else (if i < 41 then decide (InPath q (146 : Vertex)) else decide (InPath q (148 : Vertex)))))) else (if i < 49 then (if i < 45 then (if i < 43 then decide (InPath q (156 : Vertex)) else (if i < 44 then decide (InPath q (158 : Vertex)) else decide (InPath q (159 : Vertex)))) else (if i < 47 then (if i < 46 then decide (InPath q (192 : Vertex)) else decide (InPath q (194 : Vertex))) else (if i < 48 then decide (InPath q (195 : Vertex)) else decide (InPath q (196 : Vertex))))) else (if i < 53 then (if i < 51 then (if i < 50 then decide (InPath q (198 : Vertex)) else decide (InPath q (202 : Vertex))) else (if i < 52 then decide (InPath q (203 : Vertex)) else decide (InPath q (204 : Vertex)))) else (if i < 55 then (if i < 54 then decide (InPath q (205 : Vertex)) else decide (InPath q (209 : Vertex))) else (if i < 56 then decide (InPath q (213 : Vertex)) else decide (InPath q (214 : Vertex)))))))) else (if i < 85 then (if i < 71 then (if i < 64 then (if i < 60 then (if i < 58 then decide (InPath q (215 : Vertex)) else (if i < 59 then decide (InPath q (216 : Vertex)) else decide (InPath q (217 : Vertex)))) else (if i < 62 then (if i < 61 then decide (InPath q (218 : Vertex)) else decide (InPath q (221 : Vertex))) else (if i < 63 then decide (InPath q (291 : Vertex)) else decide (InPath q (298 : Vertex))))) else (if i < 67 then (if i < 65 then decide (InPath q (299 : Vertex)) else (if i < 66 then decide (InPath q (314 : Vertex)) else decide (InPath q (320 : Vertex)))) else (if i < 69 then (if i < 68 then decide (InPath q (322 : Vertex)) else decide (InPath q (323 : Vertex))) else (if i < 70 then decide (InPath q (324 : Vertex)) else decide (InPath q (326 : Vertex)))))) else (if i < 78 then (if i < 74 then (if i < 72 then decide (InPath q (330 : Vertex)) else (if i < 73 then decide (InPath q (331 : Vertex)) else decide (InPath q (332 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (333 : Vertex)) else decide (InPath q (337 : Vertex))) else (if i < 77 then decide (InPath q (341 : Vertex)) else decide (InPath q (342 : Vertex))))) else (if i < 81 then (if i < 79 then decide (InPath q (343 : Vertex)) else (if i < 80 then decide (InPath q (344 : Vertex)) else decide (InPath q (345 : Vertex)))) else (if i < 83 then (if i < 82 then decide (InPath q (346 : Vertex)) else decide (InPath q (349 : Vertex))) else (if i < 84 then decide (InPath q (351 : Vertex)) else decide (InPath q (386 : Vertex))))))) else (if i < 99 then (if i < 92 then (if i < 88 then (if i < 86 then decide (InPath q (387 : Vertex)) else (if i < 87 then decide (InPath q (388 : Vertex)) else decide (InPath q (390 : Vertex)))) else (if i < 90 then (if i < 89 then decide (InPath q (397 : Vertex)) else decide (InPath q (401 : Vertex))) else (if i < 91 then decide (InPath q (405 : Vertex)) else decide (InPath q (406 : Vertex))))) else (if i < 95 then (if i < 93 then decide (InPath q (407 : Vertex)) else (if i < 94 then decide (InPath q (413 : Vertex)) else decide (InPath q (419 : Vertex)))) else (if i < 97 then (if i < 96 then decide (InPath q (421 : Vertex)) else decide (InPath q (423 : Vertex))) else (if i < 98 then decide (InPath q (425 : Vertex)) else decide (InPath q (429 : Vertex)))))) else (if i < 106 then (if i < 102 then (if i < 100 then decide (InPath q (482 : Vertex)) else (if i < 101 then decide (InPath q (483 : Vertex)) else decide (InPath q (484 : Vertex)))) else (if i < 104 then (if i < 103 then decide (InPath q (486 : Vertex)) else decide (InPath q (490 : Vertex))) else (if i < 105 then decide (InPath q (491 : Vertex)) else decide (InPath q (492 : Vertex))))) else (if i < 110 then (if i < 108 then (if i < 107 then decide (InPath q (493 : Vertex)) else decide (InPath q (497 : Vertex))) else (if i < 109 then decide (InPath q (501 : Vertex)) else decide (InPath q (502 : Vertex)))) else (if i < 112 then (if i < 111 then decide (InPath q (503 : Vertex)) else decide (InPath q (504 : Vertex))) else (if i < 113 then decide (InPath q (505 : Vertex)) else decide (InPath q (506 : Vertex))))))))) else (if i < 171 then (if i < 142 then (if i < 128 then (if i < 121 then (if i < 117 then (if i < 115 then decide (InPath q (509 : Vertex)) else (if i < 116 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else decide (BallClauseLogic.Endpoint q (11 : Vertex)))) else (if i < 119 then (if i < 118 then decide (BallClauseLogic.Endpoint q (13 : Vertex)) else decide (BallClauseLogic.Endpoint q (24 : Vertex))) else (if i < 120 then decide (BallClauseLogic.Endpoint q (25 : Vertex)) else decide (BallClauseLogic.Endpoint q (26 : Vertex))))) else (if i < 124 then (if i < 122 then decide (BallClauseLogic.Endpoint q (29 : Vertex)) else (if i < 123 then decide (BallClauseLogic.Endpoint q (65 : Vertex)) else decide (BallClauseLogic.Endpoint q (67 : Vertex)))) else (if i < 126 then (if i < 125 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else decide (BallClauseLogic.Endpoint q (71 : Vertex))) else (if i < 127 then decide (BallClauseLogic.Endpoint q (73 : Vertex)) else decide (BallClauseLogic.Endpoint q (74 : Vertex)))))) else (if i < 135 then (if i < 131 then (if i < 129 then decide (BallClauseLogic.Endpoint q (75 : Vertex)) else (if i < 130 then decide (BallClauseLogic.Endpoint q (76 : Vertex)) else decide (BallClauseLogic.Endpoint q (77 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (78 : Vertex)) else decide (BallClauseLogic.Endpoint q (79 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else decide (BallClauseLogic.Endpoint q (81 : Vertex))))) else (if i < 138 then (if i < 136 then decide (BallClauseLogic.Endpoint q (82 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (88 : Vertex)))) else (if i < 140 then (if i < 139 then decide (BallClauseLogic.Endpoint q (90 : Vertex)) else decide (BallClauseLogic.Endpoint q (92 : Vertex))) else (if i < 141 then decide (BallClauseLogic.Endpoint q (94 : Vertex)) else decide (BallClauseLogic.Endpoint q (95 : Vertex))))))) else (if i < 156 then (if i < 149 then (if i < 145 then (if i < 143 then decide (BallClauseLogic.Endpoint q (129 : Vertex)) else (if i < 144 then decide (BallClauseLogic.Endpoint q (130 : Vertex)) else decide (BallClauseLogic.Endpoint q (131 : Vertex)))) else (if i < 147 then (if i < 146 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (135 : Vertex))) else (if i < 148 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex))))) else (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (141 : Vertex)) else decide (BallClauseLogic.Endpoint q (143 : Vertex)))) else (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (145 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (146 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex)))))) else (if i < 163 then (if i < 159 then (if i < 157 then decide (BallClauseLogic.Endpoint q (156 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (158 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex)))) else (if i < 161 then (if i < 160 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (194 : Vertex))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (195 : Vertex)) else decide (BallClauseLogic.Endpoint q (196 : Vertex))))) else (if i < 167 then (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (202 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (203 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex)))) else (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (205 : Vertex)) else decide (BallClauseLogic.Endpoint q (209 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (213 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex)))))))) else (if i < 200 then (if i < 185 then (if i < 178 then (if i < 174 then (if i < 172 then decide (BallClauseLogic.Endpoint q (215 : Vertex)) else (if i < 173 then decide (BallClauseLogic.Endpoint q (216 : Vertex)) else decide (BallClauseLogic.Endpoint q (217 : Vertex)))) else (if i < 176 then (if i < 175 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex))) else (if i < 177 then decide (BallClauseLogic.Endpoint q (291 : Vertex)) else decide (BallClauseLogic.Endpoint q (298 : Vertex))))) else (if i < 181 then (if i < 179 then decide (BallClauseLogic.Endpoint q (299 : Vertex)) else (if i < 180 then decide (BallClauseLogic.Endpoint q (314 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex)))) else (if i < 183 then (if i < 182 then decide (BallClauseLogic.Endpoint q (322 : Vertex)) else decide (BallClauseLogic.Endpoint q (323 : Vertex))) else (if i < 184 then decide (BallClauseLogic.Endpoint q (324 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex)))))) else (if i < 192 then (if i < 188 then (if i < 186 then decide (BallClauseLogic.Endpoint q (330 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (331 : Vertex)) else decide (BallClauseLogic.Endpoint q (332 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (341 : Vertex)) else decide (BallClauseLogic.Endpoint q (342 : Vertex))))) else (if i < 196 then (if i < 194 then (if i < 193 then decide (BallClauseLogic.Endpoint q (343 : Vertex)) else decide (BallClauseLogic.Endpoint q (344 : Vertex))) else (if i < 195 then decide (BallClauseLogic.Endpoint q (345 : Vertex)) else decide (BallClauseLogic.Endpoint q (346 : Vertex)))) else (if i < 198 then (if i < 197 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (351 : Vertex))) else (if i < 199 then decide (BallClauseLogic.Endpoint q (386 : Vertex)) else decide (BallClauseLogic.Endpoint q (387 : Vertex))))))) else (if i < 214 then (if i < 207 then (if i < 203 then (if i < 201 then decide (BallClauseLogic.Endpoint q (388 : Vertex)) else (if i < 202 then decide (BallClauseLogic.Endpoint q (390 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (405 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (407 : Vertex))))) else (if i < 210 then (if i < 208 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else (if i < 209 then decide (BallClauseLogic.Endpoint q (419 : Vertex)) else decide (BallClauseLogic.Endpoint q (421 : Vertex)))) else (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (423 : Vertex)) else decide (BallClauseLogic.Endpoint q (425 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (429 : Vertex)) else decide (BallClauseLogic.Endpoint q (482 : Vertex)))))) else (if i < 221 then (if i < 217 then (if i < 215 then decide (BallClauseLogic.Endpoint q (483 : Vertex)) else (if i < 216 then decide (BallClauseLogic.Endpoint q (484 : Vertex)) else decide (BallClauseLogic.Endpoint q (486 : Vertex)))) else (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (490 : Vertex)) else decide (BallClauseLogic.Endpoint q (491 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (492 : Vertex)) else decide (BallClauseLogic.Endpoint q (493 : Vertex))))) else (if i < 225 then (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (501 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (502 : Vertex)) else decide (BallClauseLogic.Endpoint q (503 : Vertex)))) else (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (504 : Vertex)) else decide (BallClauseLogic.Endpoint q (505 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count229 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count231 (b : Nat → Bool) : Nat := countLit b [115, 116, 117]
def count233 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count235 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count237 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121]
def count239 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121]
def count241 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count247 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count249 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128]
def count253 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128]
def count255 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count263 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count275 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [136, 137, 138, 139, 140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
def count281 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
def count283 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [143, 144, 145]
def count287 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149]
def count295 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count303 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153, 154, 155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count315 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count317 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167, 168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]
def count337 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]
def count339 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count341 (b : Nat → Bool) : Nat := countLit b [171, 172, 173]
def count343 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count345 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177]
def count349 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177]
def count351 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count353 (b : Nat → Bool) : Nat := countLit b [178, 180, 181]
def count355 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [182, 183, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [178, 180, 181, 182, 183, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [186, 187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count373 (b : Nat → Bool) : Nat := countLit b [189, 190, 191, 192]
def count375 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count379 (b : Nat → Bool) : Nat := countLit b [193, 194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count383 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197, 198, 199]
def count387 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196, 197, 198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]
def count391 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [200, 201, 202]
def count397 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count401 (b : Nat → Bool) : Nat := countLit b [203, 204, 205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203, 204, 205, 206]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [207, 208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count411 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count413 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [207, 208, 209, 210, 211, 212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]
def count419 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count421 (b : Nat → Bool) : Nat := countLit b [214, 215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count427 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count435 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count439 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count441 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count443 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224, 225, 226, 227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count449 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count451 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count453 (b : Nat → Bool) : Nat := countLit b [4, 7]
def count455 (b : Nat → Bool) : Nat := countLit b [1, 4, 7]
def count458 (b : Nat → Bool) : Nat := countLit b [11, 14]
def count460 (b : Nat → Bool) : Nat := countLit b [8, 11, 14]
def count463 (b : Nat → Bool) : Nat := countLit b [1, 4, 7, 8, 11, 14]
def count469 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count471 (b : Nat → Bool) : Nat := countLit b [16, 17, 19]
def count474 (b : Nat → Bool) : Nat := countLit b [24, 25]
def count476 (b : Nat → Bool) : Nat := countLit b [27, 28]
def count478 (b : Nat → Bool) : Nat := countLit b [24, 25, 27, 28]
def count482 (b : Nat → Bool) : Nat := countLit b [16, 17, 19, 24, 25, 27, 28]
def count489 (b : Nat → Bool) : Nat := countLit b [1, 4, 7, 8, 11, 14, 16, 17, 19, 24, 25, 27, 28]
def count502 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count504 (b : Nat → Bool) : Nat := countLit b [29, 32, 34]
def count507 (b : Nat → Bool) : Nat := countLit b [36, 38]
def count509 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count511 (b : Nat → Bool) : Nat := countLit b [36, 38, 42, 44]
def count515 (b : Nat → Bool) : Nat := countLit b [29, 32, 34, 36, 38, 42, 44]
def count522 (b : Nat → Bool) : Nat := countLit b [47, 49]
def count524 (b : Nat → Bool) : Nat := countLit b [45, 47, 49]
def count527 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count529 (b : Nat → Bool) : Nat := countLit b [54, 57]
def count531 (b : Nat → Bool) : Nat := countLit b [50, 52, 54, 57]
def count535 (b : Nat → Bool) : Nat := countLit b [45, 47, 49, 50, 52, 54, 57]
def count542 (b : Nat → Bool) : Nat := countLit b [29, 32, 34, 36, 38, 42, 44, 45, 47, 49, 50, 52, 54, 57]
def count556 (b : Nat → Bool) : Nat := countLit b [1, 4, 7, 8, 11, 14, 16, 17, 19, 24, 25, 27, 28, 29, 32, 34, 36, 38, 42, 44, 45, 47, 49, 50, 52, 54, 57]
def count583 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count585 (b : Nat → Bool) : Nat := countLit b [58, 61, 62]
def count588 (b : Nat → Bool) : Nat := countLit b [63, 66]
def count590 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count592 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 70]
def count596 (b : Nat → Bool) : Nat := countLit b [58, 61, 62, 63, 66, 68, 70]
def count603 (b : Nat → Bool) : Nat := countLit b [73, 75]
def count605 (b : Nat → Bool) : Nat := countLit b [71, 73, 75]
def count608 (b : Nat → Bool) : Nat := countLit b [78, 79]
def count610 (b : Nat → Bool) : Nat := countLit b [82, 85]
def count612 (b : Nat → Bool) : Nat := countLit b [78, 79, 82, 85]
def count616 (b : Nat → Bool) : Nat := countLit b [71, 73, 75, 78, 79, 82, 85]
def count623 (b : Nat → Bool) : Nat := countLit b [58, 61, 62, 63, 66, 68, 70, 71, 73, 75, 78, 79, 82, 85]
def count637 (b : Nat → Bool) : Nat := countLit b [89, 92]
def count639 (b : Nat → Bool) : Nat := countLit b [87, 89, 92]
def count642 (b : Nat → Bool) : Nat := countLit b [93, 96]
def count644 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count646 (b : Nat → Bool) : Nat := countLit b [93, 96, 98, 100]
def count650 (b : Nat → Bool) : Nat := countLit b [87, 89, 92, 93, 96, 98, 100]
def count657 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count659 (b : Nat → Bool) : Nat := countLit b [102, 103, 105]
def count662 (b : Nat → Bool) : Nat := countLit b [107, 110]
def count664 (b : Nat → Bool) : Nat := countLit b [111, 114]
def count666 (b : Nat → Bool) : Nat := countLit b [107, 110, 111, 114]
def count670 (b : Nat → Bool) : Nat := countLit b [102, 103, 105, 107, 110, 111, 114]
def count677 (b : Nat → Bool) : Nat := countLit b [87, 89, 92, 93, 96, 98, 100, 102, 103, 105, 107, 110, 111, 114]
def count691 (b : Nat → Bool) : Nat := countLit b [58, 61, 62, 63, 66, 68, 70, 71, 73, 75, 78, 79, 82, 85, 87, 89, 92, 93, 96, 98, 100, 102, 103, 105, 107, 110, 111, 114]
def count719 (b : Nat → Bool) : Nat := countLit b [1, 4, 7, 8, 11, 14, 16, 17, 19, 24, 25, 27, 28, 29, 32, 34, 36, 38, 42, 44, 45, 47, 49, 50, 52, 54, 57, 58, 61, 62, 63, 66, 68, 70, 71, 73, 75, 78, 79, 82, 85, 87, 89, 92, 93, 96, 98, 100, 102, 103, 105, 107, 110, 111, 114]
def count761 (b : Nat → Bool) : Nat := countLit b [-4, -7]
def count763 (b : Nat → Bool) : Nat := countLit b [-1, -4, -7]
def count766 (b : Nat → Bool) : Nat := countLit b [-11, -14]
def count768 (b : Nat → Bool) : Nat := countLit b [-8, -11, -14]
def count771 (b : Nat → Bool) : Nat := countLit b [-1, -4, -7, -8, -11, -14]
def count777 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count779 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19]
def count782 (b : Nat → Bool) : Nat := countLit b [-24, -25]
def count784 (b : Nat → Bool) : Nat := countLit b [-27, -28]
def count786 (b : Nat → Bool) : Nat := countLit b [-24, -25, -27, -28]
def count790 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19, -24, -25, -27, -28]
def count797 (b : Nat → Bool) : Nat := countLit b [-1, -4, -7, -8, -11, -14, -16, -17, -19, -24, -25, -27, -28]
def count810 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count812 (b : Nat → Bool) : Nat := countLit b [-29, -32, -34]
def count815 (b : Nat → Bool) : Nat := countLit b [-36, -38]
def count817 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count819 (b : Nat → Bool) : Nat := countLit b [-36, -38, -42, -44]
def count823 (b : Nat → Bool) : Nat := countLit b [-29, -32, -34, -36, -38, -42, -44]
def count830 (b : Nat → Bool) : Nat := countLit b [-47, -49]
def count832 (b : Nat → Bool) : Nat := countLit b [-45, -47, -49]
def count835 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count837 (b : Nat → Bool) : Nat := countLit b [-54, -57]
def count839 (b : Nat → Bool) : Nat := countLit b [-50, -52, -54, -57]
def count843 (b : Nat → Bool) : Nat := countLit b [-45, -47, -49, -50, -52, -54, -57]
def count850 (b : Nat → Bool) : Nat := countLit b [-29, -32, -34, -36, -38, -42, -44, -45, -47, -49, -50, -52, -54, -57]
def count864 (b : Nat → Bool) : Nat := countLit b [-1, -4, -7, -8, -11, -14, -16, -17, -19, -24, -25, -27, -28, -29, -32, -34, -36, -38, -42, -44, -45, -47, -49, -50, -52, -54, -57]
def count879 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count881 (b : Nat → Bool) : Nat := countLit b [-58, -61, -62]
def count884 (b : Nat → Bool) : Nat := countLit b [-63, -66]
def count886 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count888 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -70]
def count892 (b : Nat → Bool) : Nat := countLit b [-58, -61, -62, -63, -66, -68, -70]
def count899 (b : Nat → Bool) : Nat := countLit b [-73, -75]
def count901 (b : Nat → Bool) : Nat := countLit b [-71, -73, -75]
def count904 (b : Nat → Bool) : Nat := countLit b [-78, -79]
def count906 (b : Nat → Bool) : Nat := countLit b [-82, -85]
def count908 (b : Nat → Bool) : Nat := countLit b [-78, -79, -82, -85]
def count912 (b : Nat → Bool) : Nat := countLit b [-71, -73, -75, -78, -79, -82, -85]
def count919 (b : Nat → Bool) : Nat := countLit b [-58, -61, -62, -63, -66, -68, -70, -71, -73, -75, -78, -79, -82, -85]
def count933 (b : Nat → Bool) : Nat := countLit b [-89, -92]
def count935 (b : Nat → Bool) : Nat := countLit b [-87, -89, -92]
def count938 (b : Nat → Bool) : Nat := countLit b [-93, -96]
def count940 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count942 (b : Nat → Bool) : Nat := countLit b [-93, -96, -98, -100]
def count946 (b : Nat → Bool) : Nat := countLit b [-87, -89, -92, -93, -96, -98, -100]
def count953 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count955 (b : Nat → Bool) : Nat := countLit b [-102, -103, -105]
def count958 (b : Nat → Bool) : Nat := countLit b [-107, -110]
def count960 (b : Nat → Bool) : Nat := countLit b [-111, -114]
def count962 (b : Nat → Bool) : Nat := countLit b [-107, -110, -111, -114]
def count966 (b : Nat → Bool) : Nat := countLit b [-102, -103, -105, -107, -110, -111, -114]
def count973 (b : Nat → Bool) : Nat := countLit b [-87, -89, -92, -93, -96, -98, -100, -102, -103, -105, -107, -110, -111, -114]
def count987 (b : Nat → Bool) : Nat := countLit b [-58, -61, -62, -63, -66, -68, -70, -71, -73, -75, -78, -79, -82, -85, -87, -89, -92, -93, -96, -98, -100, -102, -103, -105, -107, -110, -111, -114]
def count1002 (b : Nat → Bool) : Nat := countLit b [-1, -4, -7, -8, -11, -14, -16, -17, -19, -24, -25, -27, -28, -29, -32, -34, -36, -38, -42, -44, -45, -47, -49, -50, -52, -54, -57, -58, -61, -62, -63, -66, -68, -70, -71, -73, -75, -78, -79, -82, -85, -87, -89, -92, -93, -96, -98, -100, -102, -103, -105, -107, -110, -111, -114]
def count1017 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count1019 (b : Nat → Bool) : Nat := countLit b [2, 3, 5]
def count1022 (b : Nat → Bool) : Nat := countLit b [6, 9]
def count1024 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count1026 (b : Nat → Bool) : Nat := countLit b [6, 9, 10, 12]
def count1030 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 6, 9, 10, 12]
def count1037 (b : Nat → Bool) : Nat := countLit b [15, 18]
def count1039 (b : Nat → Bool) : Nat := countLit b [13, 15, 18]
def count1042 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count1044 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count1046 (b : Nat → Bool) : Nat := countLit b [20, 21, 22, 23]
def count1050 (b : Nat → Bool) : Nat := countLit b [13, 15, 18, 20, 21, 22, 23]
def count1057 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 6, 9, 10, 12, 13, 15, 18, 20, 21, 22, 23]
def count1071 (b : Nat → Bool) : Nat := countLit b [30, 31]
def count1073 (b : Nat → Bool) : Nat := countLit b [26, 30, 31]
def count1076 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count1078 (b : Nat → Bool) : Nat := countLit b [37, 39]
def count1080 (b : Nat → Bool) : Nat := countLit b [33, 35, 37, 39]
def count1084 (b : Nat → Bool) : Nat := countLit b [26, 30, 31, 33, 35, 37, 39]
def count1091 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count1093 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count1095 (b : Nat → Bool) : Nat := countLit b [40, 41, 43, 46]
def count1099 (b : Nat → Bool) : Nat := countLit b [48, 51]
def count1101 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count1103 (b : Nat → Bool) : Nat := countLit b [48, 51, 53, 55]
def count1107 (b : Nat → Bool) : Nat := countLit b [40, 41, 43, 46, 48, 51, 53, 55]
def count1115 (b : Nat → Bool) : Nat := countLit b [26, 30, 31, 33, 35, 37, 39, 40, 41, 43, 46, 48, 51, 53, 55]
def count1130 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 6, 9, 10, 12, 13, 15, 18, 20, 21, 22, 23, 26, 30, 31, 33, 35, 37, 39, 40, 41, 43, 46, 48, 51, 53, 55]
def count1159 (b : Nat → Bool) : Nat := countLit b [59, 60]
def count1161 (b : Nat → Bool) : Nat := countLit b [56, 59, 60]
def count1164 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count1166 (b : Nat → Bool) : Nat := countLit b [67, 69]
def count1168 (b : Nat → Bool) : Nat := countLit b [64, 65, 67, 69]
def count1172 (b : Nat → Bool) : Nat := countLit b [56, 59, 60, 64, 65, 67, 69]
def count1179 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count1181 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count1183 (b : Nat → Bool) : Nat := countLit b [72, 74, 76, 77]
def count1187 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count1189 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count1191 (b : Nat → Bool) : Nat := countLit b [80, 81, 83, 84]
def count1195 (b : Nat → Bool) : Nat := countLit b [72, 74, 76, 77, 80, 81, 83, 84]
def count1203 (b : Nat → Bool) : Nat := countLit b [56, 59, 60, 64, 65, 67, 69, 72, 74, 76, 77, 80, 81, 83, 84]
def count1218 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count1220 (b : Nat → Bool) : Nat := countLit b [86, 88, 90]
def count1223 (b : Nat → Bool) : Nat := countLit b [91, 94]
def count1225 (b : Nat → Bool) : Nat := countLit b [95, 97]
def count1227 (b : Nat → Bool) : Nat := countLit b [91, 94, 95, 97]
def count1231 (b : Nat → Bool) : Nat := countLit b [86, 88, 90, 91, 94, 95, 97]
def count1238 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count1240 (b : Nat → Bool) : Nat := countLit b [104, 106]
def count1242 (b : Nat → Bool) : Nat := countLit b [99, 101, 104, 106]
def count1246 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count1248 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count1250 (b : Nat → Bool) : Nat := countLit b [108, 109, 112, 113]
def count1254 (b : Nat → Bool) : Nat := countLit b [99, 101, 104, 106, 108, 109, 112, 113]
def count1262 (b : Nat → Bool) : Nat := countLit b [86, 88, 90, 91, 94, 95, 97, 99, 101, 104, 106, 108, 109, 112, 113]
def count1277 (b : Nat → Bool) : Nat := countLit b [56, 59, 60, 64, 65, 67, 69, 72, 74, 76, 77, 80, 81, 83, 84, 86, 88, 90, 91, 94, 95, 97, 99, 101, 104, 106, 108, 109, 112, 113]
def count1307 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 6, 9, 10, 12, 13, 15, 18, 20, 21, 22, 23, 26, 30, 31, 33, 35, 37, 39, 40, 41, 43, 46, 48, 51, 53, 55, 56, 59, 60, 64, 65, 67, 69, 72, 74, 76, 77, 80, 81, 83, 84, 86, 88, 90, 91, 94, 95, 97, 99, 101, 104, 106, 108, 109, 112, 113]
def count1349 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1351 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5]
def count1354 (b : Nat → Bool) : Nat := countLit b [-6, -9]
def count1356 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count1358 (b : Nat → Bool) : Nat := countLit b [-6, -9, -10, -12]
def count1362 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -6, -9, -10, -12]
def count1369 (b : Nat → Bool) : Nat := countLit b [-15, -18]
def count1371 (b : Nat → Bool) : Nat := countLit b [-13, -15, -18]
def count1374 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count1376 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count1378 (b : Nat → Bool) : Nat := countLit b [-20, -21, -22, -23]
def count1382 (b : Nat → Bool) : Nat := countLit b [-13, -15, -18, -20, -21, -22, -23]
def count1389 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23]
def count1403 (b : Nat → Bool) : Nat := countLit b [-30, -31]
def count1405 (b : Nat → Bool) : Nat := countLit b [-26, -30, -31]
def count1408 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count1410 (b : Nat → Bool) : Nat := countLit b [-37, -39]
def count1412 (b : Nat → Bool) : Nat := countLit b [-33, -35, -37, -39]
def count1416 (b : Nat → Bool) : Nat := countLit b [-26, -30, -31, -33, -35, -37, -39]
def count1423 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count1425 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count1427 (b : Nat → Bool) : Nat := countLit b [-40, -41, -43, -46]
def count1431 (b : Nat → Bool) : Nat := countLit b [-48, -51]
def count1433 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count1435 (b : Nat → Bool) : Nat := countLit b [-48, -51, -53, -55]
def count1439 (b : Nat → Bool) : Nat := countLit b [-40, -41, -43, -46, -48, -51, -53, -55]
def count1447 (b : Nat → Bool) : Nat := countLit b [-26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]
def count1462 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55]
def count1481 (b : Nat → Bool) : Nat := countLit b [-59, -60]
def count1483 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60]
def count1486 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count1488 (b : Nat → Bool) : Nat := countLit b [-67, -69]
def count1490 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67, -69]
def count1494 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60, -64, -65, -67, -69]
def count1501 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count1503 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count1505 (b : Nat → Bool) : Nat := countLit b [-72, -74, -76, -77]
def count1509 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1511 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count1513 (b : Nat → Bool) : Nat := countLit b [-80, -81, -83, -84]
def count1517 (b : Nat → Bool) : Nat := countLit b [-72, -74, -76, -77, -80, -81, -83, -84]
def count1525 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84]
def count1540 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count1542 (b : Nat → Bool) : Nat := countLit b [-86, -88, -90]
def count1545 (b : Nat → Bool) : Nat := countLit b [-91, -94]
def count1547 (b : Nat → Bool) : Nat := countLit b [-95, -97]
def count1549 (b : Nat → Bool) : Nat := countLit b [-91, -94, -95, -97]
def count1553 (b : Nat → Bool) : Nat := countLit b [-86, -88, -90, -91, -94, -95, -97]
def count1560 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count1562 (b : Nat → Bool) : Nat := countLit b [-104, -106]
def count1564 (b : Nat → Bool) : Nat := countLit b [-99, -101, -104, -106]
def count1568 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count1570 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1572 (b : Nat → Bool) : Nat := countLit b [-108, -109, -112, -113]
def count1576 (b : Nat → Bool) : Nat := countLit b [-99, -101, -104, -106, -108, -109, -112, -113]
def count1584 (b : Nat → Bool) : Nat := countLit b [-86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]
def count1599 (b : Nat → Bool) : Nat := countLit b [-56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]
def count1618 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -6, -9, -10, -12, -13, -15, -18, -20, -21, -22, -23, -26, -30, -31, -33, -35, -37, -39, -40, -41, -43, -46, -48, -51, -53, -55, -56, -59, -60, -64, -65, -67, -69, -72, -74, -76, -77, -80, -81, -83, -84, -86, -88, -90, -91, -94, -95, -97, -99, -101, -104, -106, -108, -109, -112, -113]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 818 then (if i < 409 then (if i < 204 then (if i < 102 then (if i < 51 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else b 24))))) else (if i < 38 then (if i < 31 then (if i < 28 then (if i < 26 then b 25 else (if i < 27 then b 26 else b 27)) else (if i < 29 then b 28 else (if i < 30 then b 29 else b 30))) else (if i < 34 then (if i < 32 then b 31 else (if i < 33 then b 32 else b 33)) else (if i < 36 then (if i < 35 then b 34 else b 35) else (if i < 37 then b 36 else b 37)))) else (if i < 44 then (if i < 41 then (if i < 39 then b 38 else (if i < 40 then b 39 else b 40)) else (if i < 42 then b 41 else (if i < 43 then b 42 else b 43))) else (if i < 47 then (if i < 45 then b 44 else (if i < 46 then b 45 else b 46)) else (if i < 49 then (if i < 48 then b 47 else b 48) else (if i < 50 then b 49 else b 50)))))) else (if i < 76 then (if i < 63 then (if i < 57 then (if i < 54 then (if i < 52 then b 51 else (if i < 53 then b 52 else b 53)) else (if i < 55 then b 54 else (if i < 56 then b 55 else b 56))) else (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)))) else (if i < 69 then (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 67 then b 66 else (if i < 68 then b 67 else b 68))) else (if i < 72 then (if i < 70 then b 69 else (if i < 71 then b 70 else b 71)) else (if i < 74 then (if i < 73 then b 72 else b 73) else (if i < 75 then b 74 else b 75))))) else (if i < 89 then (if i < 82 then (if i < 79 then (if i < 77 then b 76 else (if i < 78 then b 77 else b 78)) else (if i < 80 then b 79 else (if i < 81 then b 80 else b 81))) else (if i < 85 then (if i < 83 then b 82 else (if i < 84 then b 83 else b 84)) else (if i < 87 then (if i < 86 then b 85 else b 86) else (if i < 88 then b 87 else b 88)))) else (if i < 95 then (if i < 92 then (if i < 90 then b 89 else (if i < 91 then b 90 else b 91)) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))) else (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 100 then (if i < 99 then b 98 else b 99) else (if i < 101 then b 100 else b 101))))))) else (if i < 153 then (if i < 127 then (if i < 114 then (if i < 108 then (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 106 then b 105 else (if i < 107 then b 106 else b 107))) else (if i < 111 then (if i < 109 then b 108 else (if i < 110 then b 109 else b 110)) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113)))) else (if i < 120 then (if i < 117 then (if i < 115 then b 114 else (if i < 116 then b 115 else b 116)) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119))) else (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 125 then (if i < 124 then b 123 else b 124) else (if i < 126 then b 125 else b 126))))) else (if i < 140 then (if i < 133 then (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 131 then b 130 else (if i < 132 then b 131 else b 132))) else (if i < 136 then (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)) else (if i < 138 then (if i < 137 then b 136 else b 137) else (if i < 139 then b 138 else b 139)))) else (if i < 146 then (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 144 then b 143 else (if i < 145 then b 144 else b 145))) else (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 151 then (if i < 150 then b 149 else b 150) else (if i < 152 then b 151 else b 152)))))) else (if i < 178 then (if i < 165 then (if i < 159 then (if i < 156 then (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)) else (if i < 157 then b 156 else (if i < 158 then b 157 else b 158))) else (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)))) else (if i < 171 then (if i < 168 then (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)) else (if i < 169 then b 168 else (if i < 170 then b 169 else b 170))) else (if i < 174 then (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)) else (if i < 176 then (if i < 175 then b 174 else b 175) else (if i < 177 then b 176 else b 177))))) else (if i < 191 then (if i < 184 then (if i < 181 then (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)) else (if i < 182 then b 181 else (if i < 183 then b 182 else b 183))) else (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 189 then (if i < 188 then b 187 else b 188) else (if i < 190 then b 189 else b 190)))) else (if i < 197 then (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196))) else (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 202 then (if i < 201 then b 200 else b 201) else (if i < 203 then b 202 else b 203)))))))) else (if i < 306 then (if i < 255 then (if i < 229 then (if i < 216 then (if i < 210 then (if i < 207 then (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)) else (if i < 208 then b 207 else (if i < 209 then b 208 else b 209))) else (if i < 213 then (if i < 211 then b 210 else (if i < 212 then b 211 else b 212)) else (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)))) else (if i < 222 then (if i < 219 then (if i < 217 then b 216 else (if i < 218 then b 217 else b 218)) else (if i < 220 then b 219 else (if i < 221 then b 220 else b 221))) else (if i < 225 then (if i < 223 then b 222 else (if i < 224 then b 223 else b 224)) else (if i < 227 then (if i < 226 then b 225 else b 226) else (if i < 228 then b 227 else b 228))))) else (if i < 242 then (if i < 235 then (if i < 232 then (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b))) else (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))) else (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 240 then (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b)) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b))))) else (if i < 248 then (if i < 245 then (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b))) else (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b)))) else (if i < 251 then (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 253 then (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))))))) else (if i < 280 then (if i < 267 then (if i < 261 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)))) else (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))))) else (if i < 273 then (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)))) else (if i < 276 then (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 278 then (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)))))) else (if i < 293 then (if i < 286 then (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)))) else (if i < 289 then (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))) else (if i < 291 then (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b)) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))))) else (if i < 299 then (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))) else (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))))))) else (if i < 357 then (if i < 331 then (if i < 318 then (if i < 312 then (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))) else (if i < 315 then (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))) else (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b))))) else (if i < 324 then (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)))) else (if i < 327 then (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))) else (if i < 329 then (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)))))) else (if i < 344 then (if i < 337 then (if i < 334 then (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b))) else (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)))) else (if i < 340 then (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))) else (if i < 342 then (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)) else (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b))))) else (if i < 350 then (if i < 347 then (if i < 345 then decide (2 ≤ count343 b) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b))) else (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))) else (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 355 then (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))))))) else (if i < 383 then (if i < 370 then (if i < 363 then (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)))) else (if i < 366 then (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b))) else (if i < 368 then (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))))) else (if i < 376 then (if i < 373 then (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))) else (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)))) else (if i < 379 then (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b))) else (if i < 381 then (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b)) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))))) else (if i < 396 then (if i < 389 then (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 394 then (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b)) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))))) else (if i < 402 then (if i < 399 then (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b))) else (if i < 400 then decide (1 ≤ count399 b) else (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)))) else (if i < 405 then (if i < 403 then decide (2 ≤ count401 b) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b))) else (if i < 407 then (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b)) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)))))))))) else (if i < 613 then (if i < 511 then (if i < 460 then (if i < 434 then (if i < 421 then (if i < 415 then (if i < 412 then (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b))) else (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))))) else (if i < 427 then (if i < 424 then (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))) else (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)))) else (if i < 430 then (if i < 428 then decide (1 ≤ count427 b) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 432 then (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b)))))) else (if i < 447 then (if i < 440 then (if i < 437 then (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b))) else (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b)))) else (if i < 443 then (if i < 441 then decide (2 ≤ count439 b) else (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b))) else (if i < 445 then (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b)) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b))))) else (if i < 453 then (if i < 450 then (if i < 448 then decide (1 ≤ count447 b) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b))) else (if i < 451 then decide (2 ≤ count449 b) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b)))) else (if i < 456 then (if i < 454 then decide (1 ≤ count453 b) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b))) else (if i < 458 then (if i < 457 then decide (2 ≤ count455 b) else decide (3 ≤ count455 b)) else (if i < 459 then decide (1 ≤ count458 b) else decide (2 ≤ count458 b))))))) else (if i < 485 then (if i < 472 then (if i < 466 then (if i < 463 then (if i < 461 then decide (1 ≤ count460 b) else (if i < 462 then decide (2 ≤ count460 b) else decide (3 ≤ count460 b))) else (if i < 464 then decide (1 ≤ count463 b) else (if i < 465 then decide (2 ≤ count463 b) else decide (3 ≤ count463 b)))) else (if i < 469 then (if i < 467 then decide (4 ≤ count463 b) else (if i < 468 then decide (5 ≤ count463 b) else decide (6 ≤ count463 b))) else (if i < 470 then decide (1 ≤ count469 b) else (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b))))) else (if i < 478 then (if i < 475 then (if i < 473 then decide (2 ≤ count471 b) else (if i < 474 then decide (3 ≤ count471 b) else decide (1 ≤ count474 b))) else (if i < 476 then decide (2 ≤ count474 b) else (if i < 477 then decide (1 ≤ count476 b) else decide (2 ≤ count476 b)))) else (if i < 481 then (if i < 479 then decide (1 ≤ count478 b) else (if i < 480 then decide (2 ≤ count478 b) else decide (3 ≤ count478 b))) else (if i < 483 then (if i < 482 then decide (4 ≤ count478 b) else decide (1 ≤ count482 b)) else (if i < 484 then decide (2 ≤ count482 b) else decide (3 ≤ count482 b)))))) else (if i < 498 then (if i < 491 then (if i < 488 then (if i < 486 then decide (4 ≤ count482 b) else (if i < 487 then decide (5 ≤ count482 b) else decide (6 ≤ count482 b))) else (if i < 489 then decide (7 ≤ count482 b) else (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b)))) else (if i < 494 then (if i < 492 then decide (3 ≤ count489 b) else (if i < 493 then decide (4 ≤ count489 b) else decide (5 ≤ count489 b))) else (if i < 496 then (if i < 495 then decide (6 ≤ count489 b) else decide (7 ≤ count489 b)) else (if i < 497 then decide (8 ≤ count489 b) else decide (9 ≤ count489 b))))) else (if i < 504 then (if i < 501 then (if i < 499 then decide (10 ≤ count489 b) else (if i < 500 then decide (11 ≤ count489 b) else decide (12 ≤ count489 b))) else (if i < 502 then decide (13 ≤ count489 b) else (if i < 503 then decide (1 ≤ count502 b) else decide (2 ≤ count502 b)))) else (if i < 507 then (if i < 505 then decide (1 ≤ count504 b) else (if i < 506 then decide (2 ≤ count504 b) else decide (3 ≤ count504 b))) else (if i < 509 then (if i < 508 then decide (1 ≤ count507 b) else decide (2 ≤ count507 b)) else (if i < 510 then decide (1 ≤ count509 b) else decide (2 ≤ count509 b)))))))) else (if i < 562 then (if i < 536 then (if i < 523 then (if i < 517 then (if i < 514 then (if i < 512 then decide (1 ≤ count511 b) else (if i < 513 then decide (2 ≤ count511 b) else decide (3 ≤ count511 b))) else (if i < 515 then decide (4 ≤ count511 b) else (if i < 516 then decide (1 ≤ count515 b) else decide (2 ≤ count515 b)))) else (if i < 520 then (if i < 518 then decide (3 ≤ count515 b) else (if i < 519 then decide (4 ≤ count515 b) else decide (5 ≤ count515 b))) else (if i < 521 then decide (6 ≤ count515 b) else (if i < 522 then decide (7 ≤ count515 b) else decide (1 ≤ count522 b))))) else (if i < 529 then (if i < 526 then (if i < 524 then decide (2 ≤ count522 b) else (if i < 525 then decide (1 ≤ count524 b) else decide (2 ≤ count524 b))) else (if i < 527 then decide (3 ≤ count524 b) else (if i < 528 then decide (1 ≤ count527 b) else decide (2 ≤ count527 b)))) else (if i < 532 then (if i < 530 then decide (1 ≤ count529 b) else (if i < 531 then decide (2 ≤ count529 b) else decide (1 ≤ count531 b))) else (if i < 534 then (if i < 533 then decide (2 ≤ count531 b) else decide (3 ≤ count531 b)) else (if i < 535 then decide (4 ≤ count531 b) else decide (1 ≤ count535 b)))))) else (if i < 549 then (if i < 542 then (if i < 539 then (if i < 537 then decide (2 ≤ count535 b) else (if i < 538 then decide (3 ≤ count535 b) else decide (4 ≤ count535 b))) else (if i < 540 then decide (5 ≤ count535 b) else (if i < 541 then decide (6 ≤ count535 b) else decide (7 ≤ count535 b)))) else (if i < 545 then (if i < 543 then decide (1 ≤ count542 b) else (if i < 544 then decide (2 ≤ count542 b) else decide (3 ≤ count542 b))) else (if i < 547 then (if i < 546 then decide (4 ≤ count542 b) else decide (5 ≤ count542 b)) else (if i < 548 then decide (6 ≤ count542 b) else decide (7 ≤ count542 b))))) else (if i < 555 then (if i < 552 then (if i < 550 then decide (8 ≤ count542 b) else (if i < 551 then decide (9 ≤ count542 b) else decide (10 ≤ count542 b))) else (if i < 553 then decide (11 ≤ count542 b) else (if i < 554 then decide (12 ≤ count542 b) else decide (13 ≤ count542 b)))) else (if i < 558 then (if i < 556 then decide (14 ≤ count542 b) else (if i < 557 then decide (1 ≤ count556 b) else decide (2 ≤ count556 b))) else (if i < 560 then (if i < 559 then decide (3 ≤ count556 b) else decide (4 ≤ count556 b)) else (if i < 561 then decide (5 ≤ count556 b) else decide (6 ≤ count556 b))))))) else (if i < 587 then (if i < 574 then (if i < 568 then (if i < 565 then (if i < 563 then decide (7 ≤ count556 b) else (if i < 564 then decide (8 ≤ count556 b) else decide (9 ≤ count556 b))) else (if i < 566 then decide (10 ≤ count556 b) else (if i < 567 then decide (11 ≤ count556 b) else decide (12 ≤ count556 b)))) else (if i < 571 then (if i < 569 then decide (13 ≤ count556 b) else (if i < 570 then decide (14 ≤ count556 b) else decide (15 ≤ count556 b))) else (if i < 572 then decide (16 ≤ count556 b) else (if i < 573 then decide (17 ≤ count556 b) else decide (18 ≤ count556 b))))) else (if i < 580 then (if i < 577 then (if i < 575 then decide (19 ≤ count556 b) else (if i < 576 then decide (20 ≤ count556 b) else decide (21 ≤ count556 b))) else (if i < 578 then decide (22 ≤ count556 b) else (if i < 579 then decide (23 ≤ count556 b) else decide (24 ≤ count556 b)))) else (if i < 583 then (if i < 581 then decide (25 ≤ count556 b) else (if i < 582 then decide (26 ≤ count556 b) else decide (27 ≤ count556 b))) else (if i < 585 then (if i < 584 then decide (1 ≤ count583 b) else decide (2 ≤ count583 b)) else (if i < 586 then decide (1 ≤ count585 b) else decide (2 ≤ count585 b)))))) else (if i < 600 then (if i < 593 then (if i < 590 then (if i < 588 then decide (3 ≤ count585 b) else (if i < 589 then decide (1 ≤ count588 b) else decide (2 ≤ count588 b))) else (if i < 591 then decide (1 ≤ count590 b) else (if i < 592 then decide (2 ≤ count590 b) else decide (1 ≤ count592 b)))) else (if i < 596 then (if i < 594 then decide (2 ≤ count592 b) else (if i < 595 then decide (3 ≤ count592 b) else decide (4 ≤ count592 b))) else (if i < 598 then (if i < 597 then decide (1 ≤ count596 b) else decide (2 ≤ count596 b)) else (if i < 599 then decide (3 ≤ count596 b) else decide (4 ≤ count596 b))))) else (if i < 606 then (if i < 603 then (if i < 601 then decide (5 ≤ count596 b) else (if i < 602 then decide (6 ≤ count596 b) else decide (7 ≤ count596 b))) else (if i < 604 then decide (1 ≤ count603 b) else (if i < 605 then decide (2 ≤ count603 b) else decide (1 ≤ count605 b)))) else (if i < 609 then (if i < 607 then decide (2 ≤ count605 b) else (if i < 608 then decide (3 ≤ count605 b) else decide (1 ≤ count608 b))) else (if i < 611 then (if i < 610 then decide (2 ≤ count608 b) else decide (1 ≤ count610 b)) else (if i < 612 then decide (2 ≤ count610 b) else decide (1 ≤ count612 b))))))))) else (if i < 715 then (if i < 664 then (if i < 638 then (if i < 625 then (if i < 619 then (if i < 616 then (if i < 614 then decide (2 ≤ count612 b) else (if i < 615 then decide (3 ≤ count612 b) else decide (4 ≤ count612 b))) else (if i < 617 then decide (1 ≤ count616 b) else (if i < 618 then decide (2 ≤ count616 b) else decide (3 ≤ count616 b)))) else (if i < 622 then (if i < 620 then decide (4 ≤ count616 b) else (if i < 621 then decide (5 ≤ count616 b) else decide (6 ≤ count616 b))) else (if i < 623 then decide (7 ≤ count616 b) else (if i < 624 then decide (1 ≤ count623 b) else decide (2 ≤ count623 b))))) else (if i < 631 then (if i < 628 then (if i < 626 then decide (3 ≤ count623 b) else (if i < 627 then decide (4 ≤ count623 b) else decide (5 ≤ count623 b))) else (if i < 629 then decide (6 ≤ count623 b) else (if i < 630 then decide (7 ≤ count623 b) else decide (8 ≤ count623 b)))) else (if i < 634 then (if i < 632 then decide (9 ≤ count623 b) else (if i < 633 then decide (10 ≤ count623 b) else decide (11 ≤ count623 b))) else (if i < 636 then (if i < 635 then decide (12 ≤ count623 b) else decide (13 ≤ count623 b)) else (if i < 637 then decide (14 ≤ count623 b) else decide (1 ≤ count637 b)))))) else (if i < 651 then (if i < 644 then (if i < 641 then (if i < 639 then decide (2 ≤ count637 b) else (if i < 640 then decide (1 ≤ count639 b) else decide (2 ≤ count639 b))) else (if i < 642 then decide (3 ≤ count639 b) else (if i < 643 then decide (1 ≤ count642 b) else decide (2 ≤ count642 b)))) else (if i < 647 then (if i < 645 then decide (1 ≤ count644 b) else (if i < 646 then decide (2 ≤ count644 b) else decide (1 ≤ count646 b))) else (if i < 649 then (if i < 648 then decide (2 ≤ count646 b) else decide (3 ≤ count646 b)) else (if i < 650 then decide (4 ≤ count646 b) else decide (1 ≤ count650 b))))) else (if i < 657 then (if i < 654 then (if i < 652 then decide (2 ≤ count650 b) else (if i < 653 then decide (3 ≤ count650 b) else decide (4 ≤ count650 b))) else (if i < 655 then decide (5 ≤ count650 b) else (if i < 656 then decide (6 ≤ count650 b) else decide (7 ≤ count650 b)))) else (if i < 660 then (if i < 658 then decide (1 ≤ count657 b) else (if i < 659 then decide (2 ≤ count657 b) else decide (1 ≤ count659 b))) else (if i < 662 then (if i < 661 then decide (2 ≤ count659 b) else decide (3 ≤ count659 b)) else (if i < 663 then decide (1 ≤ count662 b) else decide (2 ≤ count662 b))))))) else (if i < 689 then (if i < 676 then (if i < 670 then (if i < 667 then (if i < 665 then decide (1 ≤ count664 b) else (if i < 666 then decide (2 ≤ count664 b) else decide (1 ≤ count666 b))) else (if i < 668 then decide (2 ≤ count666 b) else (if i < 669 then decide (3 ≤ count666 b) else decide (4 ≤ count666 b)))) else (if i < 673 then (if i < 671 then decide (1 ≤ count670 b) else (if i < 672 then decide (2 ≤ count670 b) else decide (3 ≤ count670 b))) else (if i < 674 then decide (4 ≤ count670 b) else (if i < 675 then decide (5 ≤ count670 b) else decide (6 ≤ count670 b))))) else (if i < 682 then (if i < 679 then (if i < 677 then decide (7 ≤ count670 b) else (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b))) else (if i < 680 then decide (3 ≤ count677 b) else (if i < 681 then decide (4 ≤ count677 b) else decide (5 ≤ count677 b)))) else (if i < 685 then (if i < 683 then decide (6 ≤ count677 b) else (if i < 684 then decide (7 ≤ count677 b) else decide (8 ≤ count677 b))) else (if i < 687 then (if i < 686 then decide (9 ≤ count677 b) else decide (10 ≤ count677 b)) else (if i < 688 then decide (11 ≤ count677 b) else decide (12 ≤ count677 b)))))) else (if i < 702 then (if i < 695 then (if i < 692 then (if i < 690 then decide (13 ≤ count677 b) else (if i < 691 then decide (14 ≤ count677 b) else decide (1 ≤ count691 b))) else (if i < 693 then decide (2 ≤ count691 b) else (if i < 694 then decide (3 ≤ count691 b) else decide (4 ≤ count691 b)))) else (if i < 698 then (if i < 696 then decide (5 ≤ count691 b) else (if i < 697 then decide (6 ≤ count691 b) else decide (7 ≤ count691 b))) else (if i < 700 then (if i < 699 then decide (8 ≤ count691 b) else decide (9 ≤ count691 b)) else (if i < 701 then decide (10 ≤ count691 b) else decide (11 ≤ count691 b))))) else (if i < 708 then (if i < 705 then (if i < 703 then decide (12 ≤ count691 b) else (if i < 704 then decide (13 ≤ count691 b) else decide (14 ≤ count691 b))) else (if i < 706 then decide (15 ≤ count691 b) else (if i < 707 then decide (16 ≤ count691 b) else decide (17 ≤ count691 b)))) else (if i < 711 then (if i < 709 then decide (18 ≤ count691 b) else (if i < 710 then decide (19 ≤ count691 b) else decide (20 ≤ count691 b))) else (if i < 713 then (if i < 712 then decide (21 ≤ count691 b) else decide (22 ≤ count691 b)) else (if i < 714 then decide (23 ≤ count691 b) else decide (24 ≤ count691 b)))))))) else (if i < 766 then (if i < 740 then (if i < 727 then (if i < 721 then (if i < 718 then (if i < 716 then decide (25 ≤ count691 b) else (if i < 717 then decide (26 ≤ count691 b) else decide (27 ≤ count691 b))) else (if i < 719 then decide (28 ≤ count691 b) else (if i < 720 then decide (1 ≤ count719 b) else decide (2 ≤ count719 b)))) else (if i < 724 then (if i < 722 then decide (3 ≤ count719 b) else (if i < 723 then decide (4 ≤ count719 b) else decide (5 ≤ count719 b))) else (if i < 725 then decide (6 ≤ count719 b) else (if i < 726 then decide (7 ≤ count719 b) else decide (8 ≤ count719 b))))) else (if i < 733 then (if i < 730 then (if i < 728 then decide (9 ≤ count719 b) else (if i < 729 then decide (10 ≤ count719 b) else decide (11 ≤ count719 b))) else (if i < 731 then decide (12 ≤ count719 b) else (if i < 732 then decide (13 ≤ count719 b) else decide (14 ≤ count719 b)))) else (if i < 736 then (if i < 734 then decide (15 ≤ count719 b) else (if i < 735 then decide (16 ≤ count719 b) else decide (17 ≤ count719 b))) else (if i < 738 then (if i < 737 then decide (18 ≤ count719 b) else decide (19 ≤ count719 b)) else (if i < 739 then decide (20 ≤ count719 b) else decide (21 ≤ count719 b)))))) else (if i < 753 then (if i < 746 then (if i < 743 then (if i < 741 then decide (22 ≤ count719 b) else (if i < 742 then decide (23 ≤ count719 b) else decide (24 ≤ count719 b))) else (if i < 744 then decide (25 ≤ count719 b) else (if i < 745 then decide (26 ≤ count719 b) else decide (27 ≤ count719 b)))) else (if i < 749 then (if i < 747 then decide (28 ≤ count719 b) else (if i < 748 then decide (29 ≤ count719 b) else decide (30 ≤ count719 b))) else (if i < 751 then (if i < 750 then decide (31 ≤ count719 b) else decide (32 ≤ count719 b)) else (if i < 752 then decide (33 ≤ count719 b) else decide (34 ≤ count719 b))))) else (if i < 759 then (if i < 756 then (if i < 754 then decide (35 ≤ count719 b) else (if i < 755 then decide (36 ≤ count719 b) else decide (37 ≤ count719 b))) else (if i < 757 then decide (38 ≤ count719 b) else (if i < 758 then decide (39 ≤ count719 b) else decide (40 ≤ count719 b)))) else (if i < 762 then (if i < 760 then decide (41 ≤ count719 b) else (if i < 761 then decide (42 ≤ count719 b) else decide (1 ≤ count761 b))) else (if i < 764 then (if i < 763 then decide (2 ≤ count761 b) else decide (1 ≤ count763 b)) else (if i < 765 then decide (2 ≤ count763 b) else decide (3 ≤ count763 b))))))) else (if i < 792 then (if i < 779 then (if i < 772 then (if i < 769 then (if i < 767 then decide (1 ≤ count766 b) else (if i < 768 then decide (2 ≤ count766 b) else decide (1 ≤ count768 b))) else (if i < 770 then decide (2 ≤ count768 b) else (if i < 771 then decide (3 ≤ count768 b) else decide (1 ≤ count771 b)))) else (if i < 775 then (if i < 773 then decide (2 ≤ count771 b) else (if i < 774 then decide (3 ≤ count771 b) else decide (4 ≤ count771 b))) else (if i < 777 then (if i < 776 then decide (5 ≤ count771 b) else decide (6 ≤ count771 b)) else (if i < 778 then decide (1 ≤ count777 b) else decide (2 ≤ count777 b))))) else (if i < 785 then (if i < 782 then (if i < 780 then decide (1 ≤ count779 b) else (if i < 781 then decide (2 ≤ count779 b) else decide (3 ≤ count779 b))) else (if i < 783 then decide (1 ≤ count782 b) else (if i < 784 then decide (2 ≤ count782 b) else decide (1 ≤ count784 b)))) else (if i < 788 then (if i < 786 then decide (2 ≤ count784 b) else (if i < 787 then decide (1 ≤ count786 b) else decide (2 ≤ count786 b))) else (if i < 790 then (if i < 789 then decide (3 ≤ count786 b) else decide (4 ≤ count786 b)) else (if i < 791 then decide (1 ≤ count790 b) else decide (2 ≤ count790 b)))))) else (if i < 805 then (if i < 798 then (if i < 795 then (if i < 793 then decide (3 ≤ count790 b) else (if i < 794 then decide (4 ≤ count790 b) else decide (5 ≤ count790 b))) else (if i < 796 then decide (6 ≤ count790 b) else (if i < 797 then decide (7 ≤ count790 b) else decide (1 ≤ count797 b)))) else (if i < 801 then (if i < 799 then decide (2 ≤ count797 b) else (if i < 800 then decide (3 ≤ count797 b) else decide (4 ≤ count797 b))) else (if i < 803 then (if i < 802 then decide (5 ≤ count797 b) else decide (6 ≤ count797 b)) else (if i < 804 then decide (7 ≤ count797 b) else decide (8 ≤ count797 b))))) else (if i < 811 then (if i < 808 then (if i < 806 then decide (9 ≤ count797 b) else (if i < 807 then decide (10 ≤ count797 b) else decide (11 ≤ count797 b))) else (if i < 809 then decide (12 ≤ count797 b) else (if i < 810 then decide (13 ≤ count797 b) else decide (1 ≤ count810 b)))) else (if i < 814 then (if i < 812 then decide (2 ≤ count810 b) else (if i < 813 then decide (1 ≤ count812 b) else decide (2 ≤ count812 b))) else (if i < 816 then (if i < 815 then decide (3 ≤ count812 b) else decide (1 ≤ count815 b)) else (if i < 817 then decide (2 ≤ count815 b) else decide (1 ≤ count817 b))))))))))) else (if i < 1227 then (if i < 1022 then (if i < 920 then (if i < 869 then (if i < 843 then (if i < 830 then (if i < 824 then (if i < 821 then (if i < 819 then decide (2 ≤ count817 b) else (if i < 820 then decide (1 ≤ count819 b) else decide (2 ≤ count819 b))) else (if i < 822 then decide (3 ≤ count819 b) else (if i < 823 then decide (4 ≤ count819 b) else decide (1 ≤ count823 b)))) else (if i < 827 then (if i < 825 then decide (2 ≤ count823 b) else (if i < 826 then decide (3 ≤ count823 b) else decide (4 ≤ count823 b))) else (if i < 828 then decide (5 ≤ count823 b) else (if i < 829 then decide (6 ≤ count823 b) else decide (7 ≤ count823 b))))) else (if i < 836 then (if i < 833 then (if i < 831 then decide (1 ≤ count830 b) else (if i < 832 then decide (2 ≤ count830 b) else decide (1 ≤ count832 b))) else (if i < 834 then decide (2 ≤ count832 b) else (if i < 835 then decide (3 ≤ count832 b) else decide (1 ≤ count835 b)))) else (if i < 839 then (if i < 837 then decide (2 ≤ count835 b) else (if i < 838 then decide (1 ≤ count837 b) else decide (2 ≤ count837 b))) else (if i < 841 then (if i < 840 then decide (1 ≤ count839 b) else decide (2 ≤ count839 b)) else (if i < 842 then decide (3 ≤ count839 b) else decide (4 ≤ count839 b)))))) else (if i < 856 then (if i < 849 then (if i < 846 then (if i < 844 then decide (1 ≤ count843 b) else (if i < 845 then decide (2 ≤ count843 b) else decide (3 ≤ count843 b))) else (if i < 847 then decide (4 ≤ count843 b) else (if i < 848 then decide (5 ≤ count843 b) else decide (6 ≤ count843 b)))) else (if i < 852 then (if i < 850 then decide (7 ≤ count843 b) else (if i < 851 then decide (1 ≤ count850 b) else decide (2 ≤ count850 b))) else (if i < 854 then (if i < 853 then decide (3 ≤ count850 b) else decide (4 ≤ count850 b)) else (if i < 855 then decide (5 ≤ count850 b) else decide (6 ≤ count850 b))))) else (if i < 862 then (if i < 859 then (if i < 857 then decide (7 ≤ count850 b) else (if i < 858 then decide (8 ≤ count850 b) else decide (9 ≤ count850 b))) else (if i < 860 then decide (10 ≤ count850 b) else (if i < 861 then decide (11 ≤ count850 b) else decide (12 ≤ count850 b)))) else (if i < 865 then (if i < 863 then decide (13 ≤ count850 b) else (if i < 864 then decide (14 ≤ count850 b) else decide (1 ≤ count864 b))) else (if i < 867 then (if i < 866 then decide (2 ≤ count864 b) else decide (3 ≤ count864 b)) else (if i < 868 then decide (4 ≤ count864 b) else decide (5 ≤ count864 b))))))) else (if i < 894 then (if i < 881 then (if i < 875 then (if i < 872 then (if i < 870 then decide (6 ≤ count864 b) else (if i < 871 then decide (7 ≤ count864 b) else decide (8 ≤ count864 b))) else (if i < 873 then decide (9 ≤ count864 b) else (if i < 874 then decide (10 ≤ count864 b) else decide (11 ≤ count864 b)))) else (if i < 878 then (if i < 876 then decide (12 ≤ count864 b) else (if i < 877 then decide (13 ≤ count864 b) else decide (14 ≤ count864 b))) else (if i < 879 then decide (15 ≤ count864 b) else (if i < 880 then decide (1 ≤ count879 b) else decide (2 ≤ count879 b))))) else (if i < 887 then (if i < 884 then (if i < 882 then decide (1 ≤ count881 b) else (if i < 883 then decide (2 ≤ count881 b) else decide (3 ≤ count881 b))) else (if i < 885 then decide (1 ≤ count884 b) else (if i < 886 then decide (2 ≤ count884 b) else decide (1 ≤ count886 b)))) else (if i < 890 then (if i < 888 then decide (2 ≤ count886 b) else (if i < 889 then decide (1 ≤ count888 b) else decide (2 ≤ count888 b))) else (if i < 892 then (if i < 891 then decide (3 ≤ count888 b) else decide (4 ≤ count888 b)) else (if i < 893 then decide (1 ≤ count892 b) else decide (2 ≤ count892 b)))))) else (if i < 907 then (if i < 900 then (if i < 897 then (if i < 895 then decide (3 ≤ count892 b) else (if i < 896 then decide (4 ≤ count892 b) else decide (5 ≤ count892 b))) else (if i < 898 then decide (6 ≤ count892 b) else (if i < 899 then decide (7 ≤ count892 b) else decide (1 ≤ count899 b)))) else (if i < 903 then (if i < 901 then decide (2 ≤ count899 b) else (if i < 902 then decide (1 ≤ count901 b) else decide (2 ≤ count901 b))) else (if i < 905 then (if i < 904 then decide (3 ≤ count901 b) else decide (1 ≤ count904 b)) else (if i < 906 then decide (2 ≤ count904 b) else decide (1 ≤ count906 b))))) else (if i < 913 then (if i < 910 then (if i < 908 then decide (2 ≤ count906 b) else (if i < 909 then decide (1 ≤ count908 b) else decide (2 ≤ count908 b))) else (if i < 911 then decide (3 ≤ count908 b) else (if i < 912 then decide (4 ≤ count908 b) else decide (1 ≤ count912 b)))) else (if i < 916 then (if i < 914 then decide (2 ≤ count912 b) else (if i < 915 then decide (3 ≤ count912 b) else decide (4 ≤ count912 b))) else (if i < 918 then (if i < 917 then decide (5 ≤ count912 b) else decide (6 ≤ count912 b)) else (if i < 919 then decide (7 ≤ count912 b) else decide (1 ≤ count919 b)))))))) else (if i < 971 then (if i < 945 then (if i < 932 then (if i < 926 then (if i < 923 then (if i < 921 then decide (2 ≤ count919 b) else (if i < 922 then decide (3 ≤ count919 b) else decide (4 ≤ count919 b))) else (if i < 924 then decide (5 ≤ count919 b) else (if i < 925 then decide (6 ≤ count919 b) else decide (7 ≤ count919 b)))) else (if i < 929 then (if i < 927 then decide (8 ≤ count919 b) else (if i < 928 then decide (9 ≤ count919 b) else decide (10 ≤ count919 b))) else (if i < 930 then decide (11 ≤ count919 b) else (if i < 931 then decide (12 ≤ count919 b) else decide (13 ≤ count919 b))))) else (if i < 938 then (if i < 935 then (if i < 933 then decide (14 ≤ count919 b) else (if i < 934 then decide (1 ≤ count933 b) else decide (2 ≤ count933 b))) else (if i < 936 then decide (1 ≤ count935 b) else (if i < 937 then decide (2 ≤ count935 b) else decide (3 ≤ count935 b)))) else (if i < 941 then (if i < 939 then decide (1 ≤ count938 b) else (if i < 940 then decide (2 ≤ count938 b) else decide (1 ≤ count940 b))) else (if i < 943 then (if i < 942 then decide (2 ≤ count940 b) else decide (1 ≤ count942 b)) else (if i < 944 then decide (2 ≤ count942 b) else decide (3 ≤ count942 b)))))) else (if i < 958 then (if i < 951 then (if i < 948 then (if i < 946 then decide (4 ≤ count942 b) else (if i < 947 then decide (1 ≤ count946 b) else decide (2 ≤ count946 b))) else (if i < 949 then decide (3 ≤ count946 b) else (if i < 950 then decide (4 ≤ count946 b) else decide (5 ≤ count946 b)))) else (if i < 954 then (if i < 952 then decide (6 ≤ count946 b) else (if i < 953 then decide (7 ≤ count946 b) else decide (1 ≤ count953 b))) else (if i < 956 then (if i < 955 then decide (2 ≤ count953 b) else decide (1 ≤ count955 b)) else (if i < 957 then decide (2 ≤ count955 b) else decide (3 ≤ count955 b))))) else (if i < 964 then (if i < 961 then (if i < 959 then decide (1 ≤ count958 b) else (if i < 960 then decide (2 ≤ count958 b) else decide (1 ≤ count960 b))) else (if i < 962 then decide (2 ≤ count960 b) else (if i < 963 then decide (1 ≤ count962 b) else decide (2 ≤ count962 b)))) else (if i < 967 then (if i < 965 then decide (3 ≤ count962 b) else (if i < 966 then decide (4 ≤ count962 b) else decide (1 ≤ count966 b))) else (if i < 969 then (if i < 968 then decide (2 ≤ count966 b) else decide (3 ≤ count966 b)) else (if i < 970 then decide (4 ≤ count966 b) else decide (5 ≤ count966 b))))))) else (if i < 996 then (if i < 983 then (if i < 977 then (if i < 974 then (if i < 972 then decide (6 ≤ count966 b) else (if i < 973 then decide (7 ≤ count966 b) else decide (1 ≤ count973 b))) else (if i < 975 then decide (2 ≤ count973 b) else (if i < 976 then decide (3 ≤ count973 b) else decide (4 ≤ count973 b)))) else (if i < 980 then (if i < 978 then decide (5 ≤ count973 b) else (if i < 979 then decide (6 ≤ count973 b) else decide (7 ≤ count973 b))) else (if i < 981 then decide (8 ≤ count973 b) else (if i < 982 then decide (9 ≤ count973 b) else decide (10 ≤ count973 b))))) else (if i < 989 then (if i < 986 then (if i < 984 then decide (11 ≤ count973 b) else (if i < 985 then decide (12 ≤ count973 b) else decide (13 ≤ count973 b))) else (if i < 987 then decide (14 ≤ count973 b) else (if i < 988 then decide (1 ≤ count987 b) else decide (2 ≤ count987 b)))) else (if i < 992 then (if i < 990 then decide (3 ≤ count987 b) else (if i < 991 then decide (4 ≤ count987 b) else decide (5 ≤ count987 b))) else (if i < 994 then (if i < 993 then decide (6 ≤ count987 b) else decide (7 ≤ count987 b)) else (if i < 995 then decide (8 ≤ count987 b) else decide (9 ≤ count987 b)))))) else (if i < 1009 then (if i < 1002 then (if i < 999 then (if i < 997 then decide (10 ≤ count987 b) else (if i < 998 then decide (11 ≤ count987 b) else decide (12 ≤ count987 b))) else (if i < 1000 then decide (13 ≤ count987 b) else (if i < 1001 then decide (14 ≤ count987 b) else decide (15 ≤ count987 b)))) else (if i < 1005 then (if i < 1003 then decide (1 ≤ count1002 b) else (if i < 1004 then decide (2 ≤ count1002 b) else decide (3 ≤ count1002 b))) else (if i < 1007 then (if i < 1006 then decide (4 ≤ count1002 b) else decide (5 ≤ count1002 b)) else (if i < 1008 then decide (6 ≤ count1002 b) else decide (7 ≤ count1002 b))))) else (if i < 1015 then (if i < 1012 then (if i < 1010 then decide (8 ≤ count1002 b) else (if i < 1011 then decide (9 ≤ count1002 b) else decide (10 ≤ count1002 b))) else (if i < 1013 then decide (11 ≤ count1002 b) else (if i < 1014 then decide (12 ≤ count1002 b) else decide (13 ≤ count1002 b)))) else (if i < 1018 then (if i < 1016 then decide (14 ≤ count1002 b) else (if i < 1017 then decide (15 ≤ count1002 b) else decide (1 ≤ count1017 b))) else (if i < 1020 then (if i < 1019 then decide (2 ≤ count1017 b) else decide (1 ≤ count1019 b)) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (3 ≤ count1019 b))))))))) else (if i < 1124 then (if i < 1073 then (if i < 1047 then (if i < 1034 then (if i < 1028 then (if i < 1025 then (if i < 1023 then decide (1 ≤ count1022 b) else (if i < 1024 then decide (2 ≤ count1022 b) else decide (1 ≤ count1024 b))) else (if i < 1026 then decide (2 ≤ count1024 b) else (if i < 1027 then decide (1 ≤ count1026 b) else decide (2 ≤ count1026 b)))) else (if i < 1031 then (if i < 1029 then decide (3 ≤ count1026 b) else (if i < 1030 then decide (4 ≤ count1026 b) else decide (1 ≤ count1030 b))) else (if i < 1032 then decide (2 ≤ count1030 b) else (if i < 1033 then decide (3 ≤ count1030 b) else decide (4 ≤ count1030 b))))) else (if i < 1040 then (if i < 1037 then (if i < 1035 then decide (5 ≤ count1030 b) else (if i < 1036 then decide (6 ≤ count1030 b) else decide (7 ≤ count1030 b))) else (if i < 1038 then decide (1 ≤ count1037 b) else (if i < 1039 then decide (2 ≤ count1037 b) else decide (1 ≤ count1039 b)))) else (if i < 1043 then (if i < 1041 then decide (2 ≤ count1039 b) else (if i < 1042 then decide (3 ≤ count1039 b) else decide (1 ≤ count1042 b))) else (if i < 1045 then (if i < 1044 then decide (2 ≤ count1042 b) else decide (1 ≤ count1044 b)) else (if i < 1046 then decide (2 ≤ count1044 b) else decide (1 ≤ count1046 b)))))) else (if i < 1060 then (if i < 1053 then (if i < 1050 then (if i < 1048 then decide (2 ≤ count1046 b) else (if i < 1049 then decide (3 ≤ count1046 b) else decide (4 ≤ count1046 b))) else (if i < 1051 then decide (1 ≤ count1050 b) else (if i < 1052 then decide (2 ≤ count1050 b) else decide (3 ≤ count1050 b)))) else (if i < 1056 then (if i < 1054 then decide (4 ≤ count1050 b) else (if i < 1055 then decide (5 ≤ count1050 b) else decide (6 ≤ count1050 b))) else (if i < 1058 then (if i < 1057 then decide (7 ≤ count1050 b) else decide (1 ≤ count1057 b)) else (if i < 1059 then decide (2 ≤ count1057 b) else decide (3 ≤ count1057 b))))) else (if i < 1066 then (if i < 1063 then (if i < 1061 then decide (4 ≤ count1057 b) else (if i < 1062 then decide (5 ≤ count1057 b) else decide (6 ≤ count1057 b))) else (if i < 1064 then decide (7 ≤ count1057 b) else (if i < 1065 then decide (8 ≤ count1057 b) else decide (9 ≤ count1057 b)))) else (if i < 1069 then (if i < 1067 then decide (10 ≤ count1057 b) else (if i < 1068 then decide (11 ≤ count1057 b) else decide (12 ≤ count1057 b))) else (if i < 1071 then (if i < 1070 then decide (13 ≤ count1057 b) else decide (14 ≤ count1057 b)) else (if i < 1072 then decide (1 ≤ count1071 b) else decide (2 ≤ count1071 b))))))) else (if i < 1098 then (if i < 1085 then (if i < 1079 then (if i < 1076 then (if i < 1074 then decide (1 ≤ count1073 b) else (if i < 1075 then decide (2 ≤ count1073 b) else decide (3 ≤ count1073 b))) else (if i < 1077 then decide (1 ≤ count1076 b) else (if i < 1078 then decide (2 ≤ count1076 b) else decide (1 ≤ count1078 b)))) else (if i < 1082 then (if i < 1080 then decide (2 ≤ count1078 b) else (if i < 1081 then decide (1 ≤ count1080 b) else decide (2 ≤ count1080 b))) else (if i < 1083 then decide (3 ≤ count1080 b) else (if i < 1084 then decide (4 ≤ count1080 b) else decide (1 ≤ count1084 b))))) else (if i < 1091 then (if i < 1088 then (if i < 1086 then decide (2 ≤ count1084 b) else (if i < 1087 then decide (3 ≤ count1084 b) else decide (4 ≤ count1084 b))) else (if i < 1089 then decide (5 ≤ count1084 b) else (if i < 1090 then decide (6 ≤ count1084 b) else decide (7 ≤ count1084 b)))) else (if i < 1094 then (if i < 1092 then decide (1 ≤ count1091 b) else (if i < 1093 then decide (2 ≤ count1091 b) else decide (1 ≤ count1093 b))) else (if i < 1096 then (if i < 1095 then decide (2 ≤ count1093 b) else decide (1 ≤ count1095 b)) else (if i < 1097 then decide (2 ≤ count1095 b) else decide (3 ≤ count1095 b)))))) else (if i < 1111 then (if i < 1104 then (if i < 1101 then (if i < 1099 then decide (4 ≤ count1095 b) else (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b))) else (if i < 1102 then decide (1 ≤ count1101 b) else (if i < 1103 then decide (2 ≤ count1101 b) else decide (1 ≤ count1103 b)))) else (if i < 1107 then (if i < 1105 then decide (2 ≤ count1103 b) else (if i < 1106 then decide (3 ≤ count1103 b) else decide (4 ≤ count1103 b))) else (if i < 1109 then (if i < 1108 then decide (1 ≤ count1107 b) else decide (2 ≤ count1107 b)) else (if i < 1110 then decide (3 ≤ count1107 b) else decide (4 ≤ count1107 b))))) else (if i < 1117 then (if i < 1114 then (if i < 1112 then decide (5 ≤ count1107 b) else (if i < 1113 then decide (6 ≤ count1107 b) else decide (7 ≤ count1107 b))) else (if i < 1115 then decide (8 ≤ count1107 b) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b)))) else (if i < 1120 then (if i < 1118 then decide (3 ≤ count1115 b) else (if i < 1119 then decide (4 ≤ count1115 b) else decide (5 ≤ count1115 b))) else (if i < 1122 then (if i < 1121 then decide (6 ≤ count1115 b) else decide (7 ≤ count1115 b)) else (if i < 1123 then decide (8 ≤ count1115 b) else decide (9 ≤ count1115 b)))))))) else (if i < 1175 then (if i < 1149 then (if i < 1136 then (if i < 1130 then (if i < 1127 then (if i < 1125 then decide (10 ≤ count1115 b) else (if i < 1126 then decide (11 ≤ count1115 b) else decide (12 ≤ count1115 b))) else (if i < 1128 then decide (13 ≤ count1115 b) else (if i < 1129 then decide (14 ≤ count1115 b) else decide (15 ≤ count1115 b)))) else (if i < 1133 then (if i < 1131 then decide (1 ≤ count1130 b) else (if i < 1132 then decide (2 ≤ count1130 b) else decide (3 ≤ count1130 b))) else (if i < 1134 then decide (4 ≤ count1130 b) else (if i < 1135 then decide (5 ≤ count1130 b) else decide (6 ≤ count1130 b))))) else (if i < 1142 then (if i < 1139 then (if i < 1137 then decide (7 ≤ count1130 b) else (if i < 1138 then decide (8 ≤ count1130 b) else decide (9 ≤ count1130 b))) else (if i < 1140 then decide (10 ≤ count1130 b) else (if i < 1141 then decide (11 ≤ count1130 b) else decide (12 ≤ count1130 b)))) else (if i < 1145 then (if i < 1143 then decide (13 ≤ count1130 b) else (if i < 1144 then decide (14 ≤ count1130 b) else decide (15 ≤ count1130 b))) else (if i < 1147 then (if i < 1146 then decide (16 ≤ count1130 b) else decide (17 ≤ count1130 b)) else (if i < 1148 then decide (18 ≤ count1130 b) else decide (19 ≤ count1130 b)))))) else (if i < 1162 then (if i < 1155 then (if i < 1152 then (if i < 1150 then decide (20 ≤ count1130 b) else (if i < 1151 then decide (21 ≤ count1130 b) else decide (22 ≤ count1130 b))) else (if i < 1153 then decide (23 ≤ count1130 b) else (if i < 1154 then decide (24 ≤ count1130 b) else decide (25 ≤ count1130 b)))) else (if i < 1158 then (if i < 1156 then decide (26 ≤ count1130 b) else (if i < 1157 then decide (27 ≤ count1130 b) else decide (28 ≤ count1130 b))) else (if i < 1160 then (if i < 1159 then decide (29 ≤ count1130 b) else decide (1 ≤ count1159 b)) else (if i < 1161 then decide (2 ≤ count1159 b) else decide (1 ≤ count1161 b))))) else (if i < 1168 then (if i < 1165 then (if i < 1163 then decide (2 ≤ count1161 b) else (if i < 1164 then decide (3 ≤ count1161 b) else decide (1 ≤ count1164 b))) else (if i < 1166 then decide (2 ≤ count1164 b) else (if i < 1167 then decide (1 ≤ count1166 b) else decide (2 ≤ count1166 b)))) else (if i < 1171 then (if i < 1169 then decide (1 ≤ count1168 b) else (if i < 1170 then decide (2 ≤ count1168 b) else decide (3 ≤ count1168 b))) else (if i < 1173 then (if i < 1172 then decide (4 ≤ count1168 b) else decide (1 ≤ count1172 b)) else (if i < 1174 then decide (2 ≤ count1172 b) else decide (3 ≤ count1172 b))))))) else (if i < 1201 then (if i < 1188 then (if i < 1181 then (if i < 1178 then (if i < 1176 then decide (4 ≤ count1172 b) else (if i < 1177 then decide (5 ≤ count1172 b) else decide (6 ≤ count1172 b))) else (if i < 1179 then decide (7 ≤ count1172 b) else (if i < 1180 then decide (1 ≤ count1179 b) else decide (2 ≤ count1179 b)))) else (if i < 1184 then (if i < 1182 then decide (1 ≤ count1181 b) else (if i < 1183 then decide (2 ≤ count1181 b) else decide (1 ≤ count1183 b))) else (if i < 1186 then (if i < 1185 then decide (2 ≤ count1183 b) else decide (3 ≤ count1183 b)) else (if i < 1187 then decide (4 ≤ count1183 b) else decide (1 ≤ count1187 b))))) else (if i < 1194 then (if i < 1191 then (if i < 1189 then decide (2 ≤ count1187 b) else (if i < 1190 then decide (1 ≤ count1189 b) else decide (2 ≤ count1189 b))) else (if i < 1192 then decide (1 ≤ count1191 b) else (if i < 1193 then decide (2 ≤ count1191 b) else decide (3 ≤ count1191 b)))) else (if i < 1197 then (if i < 1195 then decide (4 ≤ count1191 b) else (if i < 1196 then decide (1 ≤ count1195 b) else decide (2 ≤ count1195 b))) else (if i < 1199 then (if i < 1198 then decide (3 ≤ count1195 b) else decide (4 ≤ count1195 b)) else (if i < 1200 then decide (5 ≤ count1195 b) else decide (6 ≤ count1195 b)))))) else (if i < 1214 then (if i < 1207 then (if i < 1204 then (if i < 1202 then decide (7 ≤ count1195 b) else (if i < 1203 then decide (8 ≤ count1195 b) else decide (1 ≤ count1203 b))) else (if i < 1205 then decide (2 ≤ count1203 b) else (if i < 1206 then decide (3 ≤ count1203 b) else decide (4 ≤ count1203 b)))) else (if i < 1210 then (if i < 1208 then decide (5 ≤ count1203 b) else (if i < 1209 then decide (6 ≤ count1203 b) else decide (7 ≤ count1203 b))) else (if i < 1212 then (if i < 1211 then decide (8 ≤ count1203 b) else decide (9 ≤ count1203 b)) else (if i < 1213 then decide (10 ≤ count1203 b) else decide (11 ≤ count1203 b))))) else (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (12 ≤ count1203 b) else (if i < 1216 then decide (13 ≤ count1203 b) else decide (14 ≤ count1203 b))) else (if i < 1218 then decide (15 ≤ count1203 b) else (if i < 1219 then decide (1 ≤ count1218 b) else decide (2 ≤ count1218 b)))) else (if i < 1223 then (if i < 1221 then decide (1 ≤ count1220 b) else (if i < 1222 then decide (2 ≤ count1220 b) else decide (3 ≤ count1220 b))) else (if i < 1225 then (if i < 1224 then decide (1 ≤ count1223 b) else decide (2 ≤ count1223 b)) else (if i < 1226 then decide (1 ≤ count1225 b) else decide (2 ≤ count1225 b)))))))))) else (if i < 1432 then (if i < 1329 then (if i < 1278 then (if i < 1252 then (if i < 1239 then (if i < 1233 then (if i < 1230 then (if i < 1228 then decide (1 ≤ count1227 b) else (if i < 1229 then decide (2 ≤ count1227 b) else decide (3 ≤ count1227 b))) else (if i < 1231 then decide (4 ≤ count1227 b) else (if i < 1232 then decide (1 ≤ count1231 b) else decide (2 ≤ count1231 b)))) else (if i < 1236 then (if i < 1234 then decide (3 ≤ count1231 b) else (if i < 1235 then decide (4 ≤ count1231 b) else decide (5 ≤ count1231 b))) else (if i < 1237 then decide (6 ≤ count1231 b) else (if i < 1238 then decide (7 ≤ count1231 b) else decide (1 ≤ count1238 b))))) else (if i < 1245 then (if i < 1242 then (if i < 1240 then decide (2 ≤ count1238 b) else (if i < 1241 then decide (1 ≤ count1240 b) else decide (2 ≤ count1240 b))) else (if i < 1243 then decide (1 ≤ count1242 b) else (if i < 1244 then decide (2 ≤ count1242 b) else decide (3 ≤ count1242 b)))) else (if i < 1248 then (if i < 1246 then decide (4 ≤ count1242 b) else (if i < 1247 then decide (1 ≤ count1246 b) else decide (2 ≤ count1246 b))) else (if i < 1250 then (if i < 1249 then decide (1 ≤ count1248 b) else decide (2 ≤ count1248 b)) else (if i < 1251 then decide (1 ≤ count1250 b) else decide (2 ≤ count1250 b)))))) else (if i < 1265 then (if i < 1258 then (if i < 1255 then (if i < 1253 then decide (3 ≤ count1250 b) else (if i < 1254 then decide (4 ≤ count1250 b) else decide (1 ≤ count1254 b))) else (if i < 1256 then decide (2 ≤ count1254 b) else (if i < 1257 then decide (3 ≤ count1254 b) else decide (4 ≤ count1254 b)))) else (if i < 1261 then (if i < 1259 then decide (5 ≤ count1254 b) else (if i < 1260 then decide (6 ≤ count1254 b) else decide (7 ≤ count1254 b))) else (if i < 1263 then (if i < 1262 then decide (8 ≤ count1254 b) else decide (1 ≤ count1262 b)) else (if i < 1264 then decide (2 ≤ count1262 b) else decide (3 ≤ count1262 b))))) else (if i < 1271 then (if i < 1268 then (if i < 1266 then decide (4 ≤ count1262 b) else (if i < 1267 then decide (5 ≤ count1262 b) else decide (6 ≤ count1262 b))) else (if i < 1269 then decide (7 ≤ count1262 b) else (if i < 1270 then decide (8 ≤ count1262 b) else decide (9 ≤ count1262 b)))) else (if i < 1274 then (if i < 1272 then decide (10 ≤ count1262 b) else (if i < 1273 then decide (11 ≤ count1262 b) else decide (12 ≤ count1262 b))) else (if i < 1276 then (if i < 1275 then decide (13 ≤ count1262 b) else decide (14 ≤ count1262 b)) else (if i < 1277 then decide (15 ≤ count1262 b) else decide (1 ≤ count1277 b))))))) else (if i < 1303 then (if i < 1290 then (if i < 1284 then (if i < 1281 then (if i < 1279 then decide (2 ≤ count1277 b) else (if i < 1280 then decide (3 ≤ count1277 b) else decide (4 ≤ count1277 b))) else (if i < 1282 then decide (5 ≤ count1277 b) else (if i < 1283 then decide (6 ≤ count1277 b) else decide (7 ≤ count1277 b)))) else (if i < 1287 then (if i < 1285 then decide (8 ≤ count1277 b) else (if i < 1286 then decide (9 ≤ count1277 b) else decide (10 ≤ count1277 b))) else (if i < 1288 then decide (11 ≤ count1277 b) else (if i < 1289 then decide (12 ≤ count1277 b) else decide (13 ≤ count1277 b))))) else (if i < 1296 then (if i < 1293 then (if i < 1291 then decide (14 ≤ count1277 b) else (if i < 1292 then decide (15 ≤ count1277 b) else decide (16 ≤ count1277 b))) else (if i < 1294 then decide (17 ≤ count1277 b) else (if i < 1295 then decide (18 ≤ count1277 b) else decide (19 ≤ count1277 b)))) else (if i < 1299 then (if i < 1297 then decide (20 ≤ count1277 b) else (if i < 1298 then decide (21 ≤ count1277 b) else decide (22 ≤ count1277 b))) else (if i < 1301 then (if i < 1300 then decide (23 ≤ count1277 b) else decide (24 ≤ count1277 b)) else (if i < 1302 then decide (25 ≤ count1277 b) else decide (26 ≤ count1277 b)))))) else (if i < 1316 then (if i < 1309 then (if i < 1306 then (if i < 1304 then decide (27 ≤ count1277 b) else (if i < 1305 then decide (28 ≤ count1277 b) else decide (29 ≤ count1277 b))) else (if i < 1307 then decide (30 ≤ count1277 b) else (if i < 1308 then decide (1 ≤ count1307 b) else decide (2 ≤ count1307 b)))) else (if i < 1312 then (if i < 1310 then decide (3 ≤ count1307 b) else (if i < 1311 then decide (4 ≤ count1307 b) else decide (5 ≤ count1307 b))) else (if i < 1314 then (if i < 1313 then decide (6 ≤ count1307 b) else decide (7 ≤ count1307 b)) else (if i < 1315 then decide (8 ≤ count1307 b) else decide (9 ≤ count1307 b))))) else (if i < 1322 then (if i < 1319 then (if i < 1317 then decide (10 ≤ count1307 b) else (if i < 1318 then decide (11 ≤ count1307 b) else decide (12 ≤ count1307 b))) else (if i < 1320 then decide (13 ≤ count1307 b) else (if i < 1321 then decide (14 ≤ count1307 b) else decide (15 ≤ count1307 b)))) else (if i < 1325 then (if i < 1323 then decide (16 ≤ count1307 b) else (if i < 1324 then decide (17 ≤ count1307 b) else decide (18 ≤ count1307 b))) else (if i < 1327 then (if i < 1326 then decide (19 ≤ count1307 b) else decide (20 ≤ count1307 b)) else (if i < 1328 then decide (21 ≤ count1307 b) else decide (22 ≤ count1307 b)))))))) else (if i < 1380 then (if i < 1354 then (if i < 1341 then (if i < 1335 then (if i < 1332 then (if i < 1330 then decide (23 ≤ count1307 b) else (if i < 1331 then decide (24 ≤ count1307 b) else decide (25 ≤ count1307 b))) else (if i < 1333 then decide (26 ≤ count1307 b) else (if i < 1334 then decide (27 ≤ count1307 b) else decide (28 ≤ count1307 b)))) else (if i < 1338 then (if i < 1336 then decide (29 ≤ count1307 b) else (if i < 1337 then decide (30 ≤ count1307 b) else decide (31 ≤ count1307 b))) else (if i < 1339 then decide (32 ≤ count1307 b) else (if i < 1340 then decide (33 ≤ count1307 b) else decide (34 ≤ count1307 b))))) else (if i < 1347 then (if i < 1344 then (if i < 1342 then decide (35 ≤ count1307 b) else (if i < 1343 then decide (36 ≤ count1307 b) else decide (37 ≤ count1307 b))) else (if i < 1345 then decide (38 ≤ count1307 b) else (if i < 1346 then decide (39 ≤ count1307 b) else decide (40 ≤ count1307 b)))) else (if i < 1350 then (if i < 1348 then decide (41 ≤ count1307 b) else (if i < 1349 then decide (42 ≤ count1307 b) else decide (1 ≤ count1349 b))) else (if i < 1352 then (if i < 1351 then decide (2 ≤ count1349 b) else decide (1 ≤ count1351 b)) else (if i < 1353 then decide (2 ≤ count1351 b) else decide (3 ≤ count1351 b)))))) else (if i < 1367 then (if i < 1360 then (if i < 1357 then (if i < 1355 then decide (1 ≤ count1354 b) else (if i < 1356 then decide (2 ≤ count1354 b) else decide (1 ≤ count1356 b))) else (if i < 1358 then decide (2 ≤ count1356 b) else (if i < 1359 then decide (1 ≤ count1358 b) else decide (2 ≤ count1358 b)))) else (if i < 1363 then (if i < 1361 then decide (3 ≤ count1358 b) else (if i < 1362 then decide (4 ≤ count1358 b) else decide (1 ≤ count1362 b))) else (if i < 1365 then (if i < 1364 then decide (2 ≤ count1362 b) else decide (3 ≤ count1362 b)) else (if i < 1366 then decide (4 ≤ count1362 b) else decide (5 ≤ count1362 b))))) else (if i < 1373 then (if i < 1370 then (if i < 1368 then decide (6 ≤ count1362 b) else (if i < 1369 then decide (7 ≤ count1362 b) else decide (1 ≤ count1369 b))) else (if i < 1371 then decide (2 ≤ count1369 b) else (if i < 1372 then decide (1 ≤ count1371 b) else decide (2 ≤ count1371 b)))) else (if i < 1376 then (if i < 1374 then decide (3 ≤ count1371 b) else (if i < 1375 then decide (1 ≤ count1374 b) else decide (2 ≤ count1374 b))) else (if i < 1378 then (if i < 1377 then decide (1 ≤ count1376 b) else decide (2 ≤ count1376 b)) else (if i < 1379 then decide (1 ≤ count1378 b) else decide (2 ≤ count1378 b))))))) else (if i < 1406 then (if i < 1393 then (if i < 1386 then (if i < 1383 then (if i < 1381 then decide (3 ≤ count1378 b) else (if i < 1382 then decide (4 ≤ count1378 b) else decide (1 ≤ count1382 b))) else (if i < 1384 then decide (2 ≤ count1382 b) else (if i < 1385 then decide (3 ≤ count1382 b) else decide (4 ≤ count1382 b)))) else (if i < 1389 then (if i < 1387 then decide (5 ≤ count1382 b) else (if i < 1388 then decide (6 ≤ count1382 b) else decide (7 ≤ count1382 b))) else (if i < 1391 then (if i < 1390 then decide (1 ≤ count1389 b) else decide (2 ≤ count1389 b)) else (if i < 1392 then decide (3 ≤ count1389 b) else decide (4 ≤ count1389 b))))) else (if i < 1399 then (if i < 1396 then (if i < 1394 then decide (5 ≤ count1389 b) else (if i < 1395 then decide (6 ≤ count1389 b) else decide (7 ≤ count1389 b))) else (if i < 1397 then decide (8 ≤ count1389 b) else (if i < 1398 then decide (9 ≤ count1389 b) else decide (10 ≤ count1389 b)))) else (if i < 1402 then (if i < 1400 then decide (11 ≤ count1389 b) else (if i < 1401 then decide (12 ≤ count1389 b) else decide (13 ≤ count1389 b))) else (if i < 1404 then (if i < 1403 then decide (14 ≤ count1389 b) else decide (1 ≤ count1403 b)) else (if i < 1405 then decide (2 ≤ count1403 b) else decide (1 ≤ count1405 b)))))) else (if i < 1419 then (if i < 1412 then (if i < 1409 then (if i < 1407 then decide (2 ≤ count1405 b) else (if i < 1408 then decide (3 ≤ count1405 b) else decide (1 ≤ count1408 b))) else (if i < 1410 then decide (2 ≤ count1408 b) else (if i < 1411 then decide (1 ≤ count1410 b) else decide (2 ≤ count1410 b)))) else (if i < 1415 then (if i < 1413 then decide (1 ≤ count1412 b) else (if i < 1414 then decide (2 ≤ count1412 b) else decide (3 ≤ count1412 b))) else (if i < 1417 then (if i < 1416 then decide (4 ≤ count1412 b) else decide (1 ≤ count1416 b)) else (if i < 1418 then decide (2 ≤ count1416 b) else decide (3 ≤ count1416 b))))) else (if i < 1425 then (if i < 1422 then (if i < 1420 then decide (4 ≤ count1416 b) else (if i < 1421 then decide (5 ≤ count1416 b) else decide (6 ≤ count1416 b))) else (if i < 1423 then decide (7 ≤ count1416 b) else (if i < 1424 then decide (1 ≤ count1423 b) else decide (2 ≤ count1423 b)))) else (if i < 1428 then (if i < 1426 then decide (1 ≤ count1425 b) else (if i < 1427 then decide (2 ≤ count1425 b) else decide (1 ≤ count1427 b))) else (if i < 1430 then (if i < 1429 then decide (2 ≤ count1427 b) else decide (3 ≤ count1427 b)) else (if i < 1431 then decide (4 ≤ count1427 b) else decide (1 ≤ count1431 b))))))))) else (if i < 1534 then (if i < 1483 then (if i < 1457 then (if i < 1444 then (if i < 1438 then (if i < 1435 then (if i < 1433 then decide (2 ≤ count1431 b) else (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b))) else (if i < 1436 then decide (1 ≤ count1435 b) else (if i < 1437 then decide (2 ≤ count1435 b) else decide (3 ≤ count1435 b)))) else (if i < 1441 then (if i < 1439 then decide (4 ≤ count1435 b) else (if i < 1440 then decide (1 ≤ count1439 b) else decide (2 ≤ count1439 b))) else (if i < 1442 then decide (3 ≤ count1439 b) else (if i < 1443 then decide (4 ≤ count1439 b) else decide (5 ≤ count1439 b))))) else (if i < 1450 then (if i < 1447 then (if i < 1445 then decide (6 ≤ count1439 b) else (if i < 1446 then decide (7 ≤ count1439 b) else decide (8 ≤ count1439 b))) else (if i < 1448 then decide (1 ≤ count1447 b) else (if i < 1449 then decide (2 ≤ count1447 b) else decide (3 ≤ count1447 b)))) else (if i < 1453 then (if i < 1451 then decide (4 ≤ count1447 b) else (if i < 1452 then decide (5 ≤ count1447 b) else decide (6 ≤ count1447 b))) else (if i < 1455 then (if i < 1454 then decide (7 ≤ count1447 b) else decide (8 ≤ count1447 b)) else (if i < 1456 then decide (9 ≤ count1447 b) else decide (10 ≤ count1447 b)))))) else (if i < 1470 then (if i < 1463 then (if i < 1460 then (if i < 1458 then decide (11 ≤ count1447 b) else (if i < 1459 then decide (12 ≤ count1447 b) else decide (13 ≤ count1447 b))) else (if i < 1461 then decide (14 ≤ count1447 b) else (if i < 1462 then decide (15 ≤ count1447 b) else decide (1 ≤ count1462 b)))) else (if i < 1466 then (if i < 1464 then decide (2 ≤ count1462 b) else (if i < 1465 then decide (3 ≤ count1462 b) else decide (4 ≤ count1462 b))) else (if i < 1468 then (if i < 1467 then decide (5 ≤ count1462 b) else decide (6 ≤ count1462 b)) else (if i < 1469 then decide (7 ≤ count1462 b) else decide (8 ≤ count1462 b))))) else (if i < 1476 then (if i < 1473 then (if i < 1471 then decide (9 ≤ count1462 b) else (if i < 1472 then decide (10 ≤ count1462 b) else decide (11 ≤ count1462 b))) else (if i < 1474 then decide (12 ≤ count1462 b) else (if i < 1475 then decide (13 ≤ count1462 b) else decide (14 ≤ count1462 b)))) else (if i < 1479 then (if i < 1477 then decide (15 ≤ count1462 b) else (if i < 1478 then decide (16 ≤ count1462 b) else decide (17 ≤ count1462 b))) else (if i < 1481 then (if i < 1480 then decide (18 ≤ count1462 b) else decide (19 ≤ count1462 b)) else (if i < 1482 then decide (1 ≤ count1481 b) else decide (2 ≤ count1481 b))))))) else (if i < 1508 then (if i < 1495 then (if i < 1489 then (if i < 1486 then (if i < 1484 then decide (1 ≤ count1483 b) else (if i < 1485 then decide (2 ≤ count1483 b) else decide (3 ≤ count1483 b))) else (if i < 1487 then decide (1 ≤ count1486 b) else (if i < 1488 then decide (2 ≤ count1486 b) else decide (1 ≤ count1488 b)))) else (if i < 1492 then (if i < 1490 then decide (2 ≤ count1488 b) else (if i < 1491 then decide (1 ≤ count1490 b) else decide (2 ≤ count1490 b))) else (if i < 1493 then decide (3 ≤ count1490 b) else (if i < 1494 then decide (4 ≤ count1490 b) else decide (1 ≤ count1494 b))))) else (if i < 1501 then (if i < 1498 then (if i < 1496 then decide (2 ≤ count1494 b) else (if i < 1497 then decide (3 ≤ count1494 b) else decide (4 ≤ count1494 b))) else (if i < 1499 then decide (5 ≤ count1494 b) else (if i < 1500 then decide (6 ≤ count1494 b) else decide (7 ≤ count1494 b)))) else (if i < 1504 then (if i < 1502 then decide (1 ≤ count1501 b) else (if i < 1503 then decide (2 ≤ count1501 b) else decide (1 ≤ count1503 b))) else (if i < 1506 then (if i < 1505 then decide (2 ≤ count1503 b) else decide (1 ≤ count1505 b)) else (if i < 1507 then decide (2 ≤ count1505 b) else decide (3 ≤ count1505 b)))))) else (if i < 1521 then (if i < 1514 then (if i < 1511 then (if i < 1509 then decide (4 ≤ count1505 b) else (if i < 1510 then decide (1 ≤ count1509 b) else decide (2 ≤ count1509 b))) else (if i < 1512 then decide (1 ≤ count1511 b) else (if i < 1513 then decide (2 ≤ count1511 b) else decide (1 ≤ count1513 b)))) else (if i < 1517 then (if i < 1515 then decide (2 ≤ count1513 b) else (if i < 1516 then decide (3 ≤ count1513 b) else decide (4 ≤ count1513 b))) else (if i < 1519 then (if i < 1518 then decide (1 ≤ count1517 b) else decide (2 ≤ count1517 b)) else (if i < 1520 then decide (3 ≤ count1517 b) else decide (4 ≤ count1517 b))))) else (if i < 1527 then (if i < 1524 then (if i < 1522 then decide (5 ≤ count1517 b) else (if i < 1523 then decide (6 ≤ count1517 b) else decide (7 ≤ count1517 b))) else (if i < 1525 then decide (8 ≤ count1517 b) else (if i < 1526 then decide (1 ≤ count1525 b) else decide (2 ≤ count1525 b)))) else (if i < 1530 then (if i < 1528 then decide (3 ≤ count1525 b) else (if i < 1529 then decide (4 ≤ count1525 b) else decide (5 ≤ count1525 b))) else (if i < 1532 then (if i < 1531 then decide (6 ≤ count1525 b) else decide (7 ≤ count1525 b)) else (if i < 1533 then decide (8 ≤ count1525 b) else decide (9 ≤ count1525 b)))))))) else (if i < 1585 then (if i < 1559 then (if i < 1546 then (if i < 1540 then (if i < 1537 then (if i < 1535 then decide (10 ≤ count1525 b) else (if i < 1536 then decide (11 ≤ count1525 b) else decide (12 ≤ count1525 b))) else (if i < 1538 then decide (13 ≤ count1525 b) else (if i < 1539 then decide (14 ≤ count1525 b) else decide (15 ≤ count1525 b)))) else (if i < 1543 then (if i < 1541 then decide (1 ≤ count1540 b) else (if i < 1542 then decide (2 ≤ count1540 b) else decide (1 ≤ count1542 b))) else (if i < 1544 then decide (2 ≤ count1542 b) else (if i < 1545 then decide (3 ≤ count1542 b) else decide (1 ≤ count1545 b))))) else (if i < 1552 then (if i < 1549 then (if i < 1547 then decide (2 ≤ count1545 b) else (if i < 1548 then decide (1 ≤ count1547 b) else decide (2 ≤ count1547 b))) else (if i < 1550 then decide (1 ≤ count1549 b) else (if i < 1551 then decide (2 ≤ count1549 b) else decide (3 ≤ count1549 b)))) else (if i < 1555 then (if i < 1553 then decide (4 ≤ count1549 b) else (if i < 1554 then decide (1 ≤ count1553 b) else decide (2 ≤ count1553 b))) else (if i < 1557 then (if i < 1556 then decide (3 ≤ count1553 b) else decide (4 ≤ count1553 b)) else (if i < 1558 then decide (5 ≤ count1553 b) else decide (6 ≤ count1553 b)))))) else (if i < 1572 then (if i < 1565 then (if i < 1562 then (if i < 1560 then decide (7 ≤ count1553 b) else (if i < 1561 then decide (1 ≤ count1560 b) else decide (2 ≤ count1560 b))) else (if i < 1563 then decide (1 ≤ count1562 b) else (if i < 1564 then decide (2 ≤ count1562 b) else decide (1 ≤ count1564 b)))) else (if i < 1568 then (if i < 1566 then decide (2 ≤ count1564 b) else (if i < 1567 then decide (3 ≤ count1564 b) else decide (4 ≤ count1564 b))) else (if i < 1570 then (if i < 1569 then decide (1 ≤ count1568 b) else decide (2 ≤ count1568 b)) else (if i < 1571 then decide (1 ≤ count1570 b) else decide (2 ≤ count1570 b))))) else (if i < 1578 then (if i < 1575 then (if i < 1573 then decide (1 ≤ count1572 b) else (if i < 1574 then decide (2 ≤ count1572 b) else decide (3 ≤ count1572 b))) else (if i < 1576 then decide (4 ≤ count1572 b) else (if i < 1577 then decide (1 ≤ count1576 b) else decide (2 ≤ count1576 b)))) else (if i < 1581 then (if i < 1579 then decide (3 ≤ count1576 b) else (if i < 1580 then decide (4 ≤ count1576 b) else decide (5 ≤ count1576 b))) else (if i < 1583 then (if i < 1582 then decide (6 ≤ count1576 b) else decide (7 ≤ count1576 b)) else (if i < 1584 then decide (8 ≤ count1576 b) else decide (1 ≤ count1584 b))))))) else (if i < 1611 then (if i < 1598 then (if i < 1591 then (if i < 1588 then (if i < 1586 then decide (2 ≤ count1584 b) else (if i < 1587 then decide (3 ≤ count1584 b) else decide (4 ≤ count1584 b))) else (if i < 1589 then decide (5 ≤ count1584 b) else (if i < 1590 then decide (6 ≤ count1584 b) else decide (7 ≤ count1584 b)))) else (if i < 1594 then (if i < 1592 then decide (8 ≤ count1584 b) else (if i < 1593 then decide (9 ≤ count1584 b) else decide (10 ≤ count1584 b))) else (if i < 1596 then (if i < 1595 then decide (11 ≤ count1584 b) else decide (12 ≤ count1584 b)) else (if i < 1597 then decide (13 ≤ count1584 b) else decide (14 ≤ count1584 b))))) else (if i < 1604 then (if i < 1601 then (if i < 1599 then decide (15 ≤ count1584 b) else (if i < 1600 then decide (1 ≤ count1599 b) else decide (2 ≤ count1599 b))) else (if i < 1602 then decide (3 ≤ count1599 b) else (if i < 1603 then decide (4 ≤ count1599 b) else decide (5 ≤ count1599 b)))) else (if i < 1607 then (if i < 1605 then decide (6 ≤ count1599 b) else (if i < 1606 then decide (7 ≤ count1599 b) else decide (8 ≤ count1599 b))) else (if i < 1609 then (if i < 1608 then decide (9 ≤ count1599 b) else decide (10 ≤ count1599 b)) else (if i < 1610 then decide (11 ≤ count1599 b) else decide (12 ≤ count1599 b)))))) else (if i < 1624 then (if i < 1617 then (if i < 1614 then (if i < 1612 then decide (13 ≤ count1599 b) else (if i < 1613 then decide (14 ≤ count1599 b) else decide (15 ≤ count1599 b))) else (if i < 1615 then decide (16 ≤ count1599 b) else (if i < 1616 then decide (17 ≤ count1599 b) else decide (18 ≤ count1599 b)))) else (if i < 1620 then (if i < 1618 then decide (19 ≤ count1599 b) else (if i < 1619 then decide (1 ≤ count1618 b) else decide (2 ≤ count1618 b))) else (if i < 1622 then (if i < 1621 then decide (3 ≤ count1618 b) else decide (4 ≤ count1618 b)) else (if i < 1623 then decide (5 ≤ count1618 b) else decide (6 ≤ count1618 b))))) else (if i < 1630 then (if i < 1627 then (if i < 1625 then decide (7 ≤ count1618 b) else (if i < 1626 then decide (8 ≤ count1618 b) else decide (9 ≤ count1618 b))) else (if i < 1628 then decide (10 ≤ count1618 b) else (if i < 1629 then decide (11 ≤ count1618 b) else decide (12 ≤ count1618 b)))) else (if i < 1633 then (if i < 1631 then decide (13 ≤ count1618 b) else (if i < 1632 then decide (14 ≤ count1618 b) else decide (15 ≤ count1618 b))) else (if i < 1635 then (if i < 1634 then decide (16 ≤ count1618 b) else decide (17 ≤ count1618 b)) else (if i < 1636 then decide (18 ≤ count1618 b) else decide (19 ≤ count1618 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (10 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (11 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (13 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (24 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (25 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (26 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (29 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (65 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (67 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (69 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (71 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (73 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (74 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (75 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (76 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (77 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (78 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (79 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (80 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (81 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (82 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (84 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (88 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (90 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (92 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (94 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (95 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (129 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (130 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (131 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (133 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (135 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (137 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (139 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (140 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (141 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (143 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (144 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (145 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (146 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (148 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (156 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (158 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (159 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (192 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (194 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (195 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (196 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (198 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (202 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (203 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (204 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (205 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (209 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (213 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (214 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (215 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (216 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (217 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (218 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (221 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (291 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (298 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (299 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (314 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (322 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (323 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (324 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (326 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (330 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (331 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (332 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (333 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (337 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (341 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (342 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (343 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (345 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (346 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (349 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (351 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (386 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (387 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (388 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (390 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (397 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (401 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (405 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (406 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (407 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (413 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (419 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (421 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (423 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (425 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (429 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (482 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (483 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (484 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (486 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (490 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (491 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (493 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (502 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (506 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (24 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (26 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (71 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (82 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (129 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (146 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (156 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (196 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (198 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (203 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (213 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (215 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (216 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (291 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (298 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (299 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (351 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (388 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (390 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (405 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (421 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (484 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value308 (q : Snake 81) : valuation q 308 = decide (2 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value310 (q : Snake 81) : valuation q 310 = decide (2 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value320 (q : Snake 81) : valuation q 320 = decide (2 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value334 (q : Snake 81) : valuation q 334 = decide (2 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value336 (q : Snake 81) : valuation q 336 = decide (2 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value350 (q : Snake 81) : valuation q 350 = decide (2 ≤ count349 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value364 (q : Snake 81) : valuation q 364 = decide (2 ≤ count363 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value448 (q : Snake 81) : valuation q 448 = decide (2 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value450 (q : Snake 81) : valuation q 450 = decide (2 ≤ count449 (baseVal q)) := rfl
theorem value452 (q : Snake 81) : valuation q 452 = decide (2 ≤ count451 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (2 ≤ count1349 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (1 ≤ count1351 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (2 ≤ count1351 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (3 ≤ count1351 (baseVal q)) := rfl
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
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (5 ≤ count1362 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (1 ≤ count1369 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (2 ≤ count1369 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (1 ≤ count1371 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (2 ≤ count1371 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (3 ≤ count1371 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (1 ≤ count1374 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (2 ≤ count1374 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (1 ≤ count1376 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (2 ≤ count1376 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (2 ≤ count1378 (baseVal q)) := rfl
theorem value1380 (q : Snake 81) : valuation q 1380 = decide (3 ≤ count1378 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (2 ≤ count1382 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (3 ≤ count1382 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (4 ≤ count1382 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (5 ≤ count1382 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (6 ≤ count1382 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (5 ≤ count1389 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (6 ≤ count1389 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (7 ≤ count1389 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (8 ≤ count1389 (baseVal q)) := rfl
theorem value1397 (q : Snake 81) : valuation q 1397 = decide (9 ≤ count1389 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (1 ≤ count1403 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (2 ≤ count1403 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (1 ≤ count1405 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (2 ≤ count1405 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (3 ≤ count1405 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (1 ≤ count1408 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (2 ≤ count1408 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (1 ≤ count1410 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (2 ≤ count1410 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (1 ≤ count1412 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (2 ≤ count1412 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (3 ≤ count1412 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (4 ≤ count1412 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (1 ≤ count1416 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (2 ≤ count1416 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (3 ≤ count1416 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (4 ≤ count1416 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (5 ≤ count1416 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (6 ≤ count1416 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (1 ≤ count1423 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (2 ≤ count1423 (baseVal q)) := rfl
theorem value1425 (q : Snake 81) : valuation q 1425 = decide (1 ≤ count1425 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (2 ≤ count1425 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (1 ≤ count1427 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (2 ≤ count1427 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (3 ≤ count1427 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (1 ≤ count1431 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (2 ≤ count1431 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (1 ≤ count1433 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (2 ≤ count1433 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (1 ≤ count1435 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (2 ≤ count1435 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (3 ≤ count1435 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (1 ≤ count1439 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (2 ≤ count1439 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (3 ≤ count1439 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (4 ≤ count1439 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (4 ≤ count1447 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (5 ≤ count1447 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (6 ≤ count1447 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (7 ≤ count1447 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (8 ≤ count1447 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (9 ≤ count1447 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (10 ≤ count1462 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (11 ≤ count1462 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (12 ≤ count1462 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (13 ≤ count1462 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (14 ≤ count1462 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (15 ≤ count1462 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (1 ≤ count1481 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (2 ≤ count1481 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (1 ≤ count1483 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (2 ≤ count1483 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (3 ≤ count1483 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (1 ≤ count1486 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (1 ≤ count1488 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (1 ≤ count1490 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (2 ≤ count1490 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (1 ≤ count1494 (baseVal q)) := rfl
theorem value1495 (q : Snake 81) : valuation q 1495 = decide (2 ≤ count1494 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (3 ≤ count1494 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (1 ≤ count1501 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (2 ≤ count1501 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (1 ≤ count1503 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (2 ≤ count1503 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (1 ≤ count1505 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (2 ≤ count1505 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (3 ≤ count1505 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (1 ≤ count1509 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (2 ≤ count1509 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (1 ≤ count1511 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (2 ≤ count1511 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (1 ≤ count1513 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (2 ≤ count1513 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (1 ≤ count1517 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (2 ≤ count1517 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (3 ≤ count1517 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (4 ≤ count1517 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (1 ≤ count1525 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (2 ≤ count1525 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (3 ≤ count1525 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (4 ≤ count1525 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (5 ≤ count1525 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (1 ≤ count1540 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (2 ≤ count1540 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (1 ≤ count1542 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (2 ≤ count1542 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (3 ≤ count1542 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (1 ≤ count1545 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (1 ≤ count1547 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (2 ≤ count1547 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (1 ≤ count1549 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (2 ≤ count1549 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (3 ≤ count1549 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (2 ≤ count1553 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (3 ≤ count1553 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (4 ≤ count1553 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (5 ≤ count1553 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (6 ≤ count1553 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (1 ≤ count1560 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (1 ≤ count1562 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (2 ≤ count1562 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (1 ≤ count1568 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (1 ≤ count1570 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (1 ≤ count1572 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (1 ≤ count1576 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (2 ≤ count1576 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (3 ≤ count1584 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (4 ≤ count1584 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (5 ≤ count1584 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (6 ≤ count1584 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (7 ≤ count1584 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (4 ≤ count1599 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (5 ≤ count1599 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (6 ≤ count1599 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (7 ≤ count1599 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (8 ≤ count1599 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (9 ≤ count1599 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (19 ≤ count1618 (baseVal q)) := rfl
theorem meaningNeg113 (b : Nat → Bool) : literal (valuationOf b) (-113) = decide (1 ≤ countLit b [-113]) := by
  change literal b (-113) = decide (1 ≤ countLit b [-113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-113) <;> decide
theorem meaningNeg109 (b : Nat → Bool) : literal (valuationOf b) (-109) = decide (1 ≤ countLit b [-109]) := by
  change literal b (-109) = decide (1 ≤ countLit b [-109])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-109) <;> decide
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
theorem meaningNeg80 (b : Nat → Bool) : literal (valuationOf b) (-80) = decide (1 ≤ countLit b [-80]) := by
  change literal b (-80) = decide (1 ≤ countLit b [-80])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-80) <;> decide
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
theorem meaningNeg26 (b : Nat → Bool) : literal (valuationOf b) (-26) = decide (1 ≤ countLit b [-26]) := by
  change literal b (-26) = decide (1 ≤ countLit b [-26])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-26) <;> decide
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
theorem meaningNeg18 (b : Nat → Bool) : literal (valuationOf b) (-18) = decide (1 ≤ countLit b [-18]) := by
  change literal b (-18) = decide (1 ≤ countLit b [-18])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-18) <;> decide
theorem meaningNeg15 (b : Nat → Bool) : literal (valuationOf b) (-15) = decide (1 ≤ countLit b [-15]) := by
  change literal b (-15) = decide (1 ≤ countLit b [-15])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-15) <;> decide
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
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
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
theorem meaning148 (b : Nat → Bool) : literal (valuationOf b) (148) = decide (1 ≤ countLit b [148]) := by
  change literal b (148) = decide (1 ≤ countLit b [148])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (148) <;> decide
theorem meaning152 (b : Nat → Bool) : literal (valuationOf b) (152) = decide (1 ≤ countLit b [152]) := by
  change literal b (152) = decide (1 ≤ countLit b [152])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (152) <;> decide
theorem meaning156 (b : Nat → Bool) : literal (valuationOf b) (156) = decide (1 ≤ countLit b [156]) := by
  change literal b (156) = decide (1 ≤ countLit b [156])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (156) <;> decide
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
theorem meaning166 (b : Nat → Bool) : literal (valuationOf b) (166) = decide (1 ≤ countLit b [166]) := by
  change literal b (166) = decide (1 ≤ countLit b [166])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (166) <;> decide
theorem meaning171 (b : Nat → Bool) : literal (valuationOf b) (171) = decide (1 ≤ countLit b [171]) := by
  change literal b (171) = decide (1 ≤ countLit b [171])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (171) <;> decide
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
theorem meaning175 (b : Nat → Bool) : literal (valuationOf b) (175) = decide (1 ≤ countLit b [175]) := by
  change literal b (175) = decide (1 ≤ countLit b [175])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (175) <;> decide
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
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) (201) = decide (1 ≤ countLit b [201]) := by
  change literal b (201) = decide (1 ≤ countLit b [201])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (201) <;> decide
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) (203) = decide (1 ≤ countLit b [203]) := by
  change literal b (203) = decide (1 ≤ countLit b [203])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (203) <;> decide
theorem meaning206 (b : Nat → Bool) : literal (valuationOf b) (206) = decide (1 ≤ countLit b [206]) := by
  change literal b (206) = decide (1 ≤ countLit b [206])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (206) <;> decide
theorem meaning207 (b : Nat → Bool) : literal (valuationOf b) (207) = decide (1 ≤ countLit b [207]) := by
  change literal b (207) = decide (1 ≤ countLit b [207])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (207) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning308 (b : Nat → Bool) : literal (valuationOf b) 308 = decide (2 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning310 (b : Nat → Bool) : literal (valuationOf b) 310 = decide (2 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning320 (b : Nat → Bool) : literal (valuationOf b) 320 = decide (2 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning334 (b : Nat → Bool) : literal (valuationOf b) 334 = decide (2 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning336 (b : Nat → Bool) : literal (valuationOf b) 336 = decide (2 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning338 (b : Nat → Bool) : literal (valuationOf b) 338 = decide (2 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning350 (b : Nat → Bool) : literal (valuationOf b) 350 = decide (2 ≤ count349 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning364 (b : Nat → Bool) : literal (valuationOf b) 364 = decide (2 ≤ count363 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning448 (b : Nat → Bool) : literal (valuationOf b) 448 = decide (2 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning450 (b : Nat → Bool) : literal (valuationOf b) 450 = decide (2 ≤ count449 b) := rfl
theorem meaning452 (b : Nat → Bool) : literal (valuationOf b) 452 = decide (2 ≤ count451 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (2 ≤ count1349 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (1 ≤ count1351 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (2 ≤ count1351 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (3 ≤ count1351 b) := rfl
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
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (5 ≤ count1362 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (1 ≤ count1369 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (2 ≤ count1369 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (1 ≤ count1371 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (2 ≤ count1371 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (3 ≤ count1371 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (1 ≤ count1374 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (2 ≤ count1374 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (1 ≤ count1376 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (2 ≤ count1376 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (2 ≤ count1378 b) := rfl
theorem meaning1380 (b : Nat → Bool) : literal (valuationOf b) 1380 = decide (3 ≤ count1378 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (2 ≤ count1382 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (3 ≤ count1382 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (4 ≤ count1382 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (5 ≤ count1382 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (6 ≤ count1382 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (5 ≤ count1389 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (6 ≤ count1389 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (7 ≤ count1389 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (8 ≤ count1389 b) := rfl
theorem meaning1397 (b : Nat → Bool) : literal (valuationOf b) 1397 = decide (9 ≤ count1389 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (1 ≤ count1403 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (2 ≤ count1403 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (1 ≤ count1405 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (2 ≤ count1405 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (3 ≤ count1405 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (1 ≤ count1408 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (2 ≤ count1408 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (1 ≤ count1410 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (2 ≤ count1410 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (1 ≤ count1412 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (2 ≤ count1412 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (3 ≤ count1412 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (4 ≤ count1412 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (1 ≤ count1416 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (2 ≤ count1416 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (3 ≤ count1416 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (4 ≤ count1416 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (5 ≤ count1416 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (6 ≤ count1416 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (1 ≤ count1423 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (2 ≤ count1423 b) := rfl
theorem meaning1425 (b : Nat → Bool) : literal (valuationOf b) 1425 = decide (1 ≤ count1425 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (2 ≤ count1425 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (1 ≤ count1427 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (2 ≤ count1427 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (3 ≤ count1427 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (1 ≤ count1431 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (2 ≤ count1431 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (1 ≤ count1433 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (2 ≤ count1433 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (1 ≤ count1435 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (2 ≤ count1435 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (3 ≤ count1435 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (1 ≤ count1439 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (2 ≤ count1439 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (3 ≤ count1439 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (4 ≤ count1439 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (4 ≤ count1447 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (5 ≤ count1447 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (6 ≤ count1447 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (7 ≤ count1447 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (8 ≤ count1447 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (9 ≤ count1447 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (10 ≤ count1462 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (11 ≤ count1462 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (12 ≤ count1462 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (13 ≤ count1462 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (14 ≤ count1462 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (15 ≤ count1462 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (1 ≤ count1481 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (2 ≤ count1481 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (1 ≤ count1483 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (2 ≤ count1483 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (3 ≤ count1483 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (1 ≤ count1486 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (1 ≤ count1488 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (1 ≤ count1490 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (2 ≤ count1490 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (1 ≤ count1494 b) := rfl
theorem meaning1495 (b : Nat → Bool) : literal (valuationOf b) 1495 = decide (2 ≤ count1494 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (3 ≤ count1494 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (1 ≤ count1501 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (2 ≤ count1501 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (1 ≤ count1503 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (2 ≤ count1503 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (1 ≤ count1505 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (2 ≤ count1505 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (3 ≤ count1505 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (1 ≤ count1509 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (2 ≤ count1509 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (1 ≤ count1511 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (2 ≤ count1511 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (1 ≤ count1513 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (2 ≤ count1513 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (1 ≤ count1517 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (2 ≤ count1517 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (3 ≤ count1517 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (4 ≤ count1517 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (1 ≤ count1525 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (2 ≤ count1525 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (3 ≤ count1525 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (4 ≤ count1525 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (5 ≤ count1525 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (1 ≤ count1540 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (2 ≤ count1540 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (1 ≤ count1542 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (2 ≤ count1542 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (3 ≤ count1542 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (1 ≤ count1545 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (1 ≤ count1547 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (2 ≤ count1547 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (1 ≤ count1549 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (2 ≤ count1549 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (3 ≤ count1549 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (2 ≤ count1553 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (3 ≤ count1553 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (4 ≤ count1553 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (5 ≤ count1553 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (6 ≤ count1553 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (1 ≤ count1560 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (1 ≤ count1562 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (2 ≤ count1562 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (1 ≤ count1568 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (1 ≤ count1570 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (1 ≤ count1572 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (1 ≤ count1576 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (2 ≤ count1576 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (3 ≤ count1584 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (4 ≤ count1584 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (5 ≤ count1584 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (6 ≤ count1584 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (7 ≤ count1584 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (4 ≤ count1599 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (5 ≤ count1599 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (6 ≤ count1599 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (7 ≤ count1599 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (8 ≤ count1599 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (9 ≤ count1599 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (19 ≤ count1618 b) := rfl
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
end Snake9.Regrowth.E112146
