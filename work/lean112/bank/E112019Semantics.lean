import E112019Data
namespace Snake9.Regrowth.E112019
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 121 then (if i < 60 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (4 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (10 : Vertex)) else decide (InPath q (12 : Vertex))) else (if i < 6 then decide (InPath q (14 : Vertex)) else decide (InPath q (66 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (67 : Vertex)) else decide (InPath q (68 : Vertex))) else (if i < 10 then decide (InPath q (69 : Vertex)) else decide (InPath q (71 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (74 : Vertex)) else decide (InPath q (75 : Vertex))) else (if i < 14 then decide (InPath q (77 : Vertex)) else decide (InPath q (79 : Vertex)))))) else (if i < 22 then (if i < 18 then (if i < 16 then decide (InPath q (80 : Vertex)) else (if i < 17 then decide (InPath q (81 : Vertex)) else decide (InPath q (83 : Vertex)))) else (if i < 20 then (if i < 19 then decide (InPath q (84 : Vertex)) else decide (InPath q (88 : Vertex))) else (if i < 21 then decide (InPath q (92 : Vertex)) else decide (InPath q (94 : Vertex))))) else (if i < 26 then (if i < 24 then (if i < 23 then decide (InPath q (95 : Vertex)) else decide (InPath q (130 : Vertex))) else (if i < 25 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex)))) else (if i < 28 then (if i < 27 then decide (InPath q (133 : Vertex)) else decide (InPath q (135 : Vertex))) else (if i < 29 then decide (InPath q (138 : Vertex)) else decide (InPath q (139 : Vertex))))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then decide (InPath q (141 : Vertex)) else (if i < 32 then decide (InPath q (143 : Vertex)) else decide (InPath q (144 : Vertex)))) else (if i < 35 then (if i < 34 then decide (InPath q (145 : Vertex)) else decide (InPath q (147 : Vertex))) else (if i < 36 then decide (InPath q (148 : Vertex)) else decide (InPath q (152 : Vertex))))) else (if i < 41 then (if i < 39 then (if i < 38 then decide (InPath q (156 : Vertex)) else decide (InPath q (158 : Vertex))) else (if i < 40 then decide (InPath q (159 : Vertex)) else decide (InPath q (192 : Vertex)))) else (if i < 43 then (if i < 42 then decide (InPath q (193 : Vertex)) else decide (InPath q (198 : Vertex))) else (if i < 44 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex)))))) else (if i < 52 then (if i < 48 then (if i < 46 then decide (InPath q (201 : Vertex)) else (if i < 47 then decide (InPath q (203 : Vertex)) else decide (InPath q (204 : Vertex)))) else (if i < 50 then (if i < 49 then decide (InPath q (206 : Vertex)) else decide (InPath q (210 : Vertex))) else (if i < 51 then decide (InPath q (212 : Vertex)) else decide (InPath q (213 : Vertex))))) else (if i < 56 then (if i < 54 then (if i < 53 then decide (InPath q (214 : Vertex)) else decide (InPath q (215 : Vertex))) else (if i < 55 then decide (InPath q (217 : Vertex)) else decide (InPath q (218 : Vertex)))) else (if i < 58 then (if i < 57 then decide (InPath q (219 : Vertex)) else decide (InPath q (221 : Vertex))) else (if i < 59 then decide (InPath q (266 : Vertex)) else decide (InPath q (282 : Vertex)))))))) else (if i < 90 then (if i < 75 then (if i < 67 then (if i < 63 then (if i < 61 then decide (InPath q (284 : Vertex)) else (if i < 62 then decide (InPath q (286 : Vertex)) else decide (InPath q (320 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (321 : Vertex)) else decide (InPath q (324 : Vertex))) else (if i < 66 then decide (InPath q (326 : Vertex)) else decide (InPath q (328 : Vertex))))) else (if i < 71 then (if i < 69 then (if i < 68 then decide (InPath q (331 : Vertex)) else decide (InPath q (332 : Vertex))) else (if i < 70 then decide (InPath q (334 : Vertex)) else decide (InPath q (338 : Vertex)))) else (if i < 73 then (if i < 72 then decide (InPath q (341 : Vertex)) else decide (InPath q (342 : Vertex))) else (if i < 74 then decide (InPath q (343 : Vertex)) else decide (InPath q (344 : Vertex)))))) else (if i < 82 then (if i < 78 then (if i < 76 then decide (InPath q (345 : Vertex)) else (if i < 77 then decide (InPath q (346 : Vertex)) else decide (InPath q (347 : Vertex)))) else (if i < 80 then (if i < 79 then decide (InPath q (349 : Vertex)) else decide (InPath q (384 : Vertex))) else (if i < 81 then decide (InPath q (385 : Vertex)) else decide (InPath q (386 : Vertex))))) else (if i < 86 then (if i < 84 then (if i < 83 then decide (InPath q (388 : Vertex)) else decide (InPath q (389 : Vertex))) else (if i < 85 then decide (InPath q (390 : Vertex)) else decide (InPath q (392 : Vertex)))) else (if i < 88 then (if i < 87 then decide (InPath q (394 : Vertex)) else decide (InPath q (395 : Vertex))) else (if i < 89 then decide (InPath q (396 : Vertex)) else decide (InPath q (398 : Vertex))))))) else (if i < 105 then (if i < 97 then (if i < 93 then (if i < 91 then decide (InPath q (402 : Vertex)) else (if i < 92 then decide (InPath q (405 : Vertex)) else decide (InPath q (406 : Vertex)))) else (if i < 95 then (if i < 94 then decide (InPath q (407 : Vertex)) else decide (InPath q (408 : Vertex))) else (if i < 96 then decide (InPath q (409 : Vertex)) else decide (InPath q (411 : Vertex))))) else (if i < 101 then (if i < 99 then (if i < 98 then decide (InPath q (413 : Vertex)) else decide (InPath q (415 : Vertex))) else (if i < 100 then decide (InPath q (448 : Vertex)) else decide (InPath q (449 : Vertex)))) else (if i < 103 then (if i < 102 then decide (InPath q (450 : Vertex)) else decide (InPath q (451 : Vertex))) else (if i < 104 then decide (InPath q (453 : Vertex)) else decide (InPath q (455 : Vertex)))))) else (if i < 113 then (if i < 109 then (if i < 107 then (if i < 106 then decide (InPath q (456 : Vertex)) else decide (InPath q (459 : Vertex))) else (if i < 108 then decide (InPath q (460 : Vertex)) else decide (InPath q (461 : Vertex)))) else (if i < 111 then (if i < 110 then decide (InPath q (462 : Vertex)) else decide (InPath q (463 : Vertex))) else (if i < 112 then decide (InPath q (464 : Vertex)) else decide (InPath q (465 : Vertex))))) else (if i < 117 then (if i < 115 then (if i < 114 then decide (InPath q (466 : Vertex)) else decide (InPath q (467 : Vertex))) else (if i < 116 then decide (InPath q (468 : Vertex)) else decide (InPath q (472 : Vertex)))) else (if i < 119 then (if i < 118 then decide (InPath q (474 : Vertex)) else decide (InPath q (475 : Vertex))) else (if i < 120 then decide (InPath q (476 : Vertex)) else decide (InPath q (478 : Vertex))))))))) else (if i < 182 then (if i < 151 then (if i < 136 then (if i < 128 then (if i < 124 then (if i < 122 then decide (InPath q (479 : Vertex)) else (if i < 123 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (4 : Vertex)))) else (if i < 126 then (if i < 125 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else decide (BallClauseLogic.Endpoint q (12 : Vertex))) else (if i < 127 then decide (BallClauseLogic.Endpoint q (14 : Vertex)) else decide (BallClauseLogic.Endpoint q (66 : Vertex))))) else (if i < 132 then (if i < 130 then (if i < 129 then decide (BallClauseLogic.Endpoint q (67 : Vertex)) else decide (BallClauseLogic.Endpoint q (68 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else decide (BallClauseLogic.Endpoint q (71 : Vertex)))) else (if i < 134 then (if i < 133 then decide (BallClauseLogic.Endpoint q (74 : Vertex)) else decide (BallClauseLogic.Endpoint q (75 : Vertex))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (77 : Vertex)) else decide (BallClauseLogic.Endpoint q (79 : Vertex)))))) else (if i < 143 then (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (81 : Vertex)) else decide (BallClauseLogic.Endpoint q (83 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (88 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (92 : Vertex)) else decide (BallClauseLogic.Endpoint q (94 : Vertex))))) else (if i < 147 then (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (135 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex))))))) else (if i < 166 then (if i < 158 then (if i < 154 then (if i < 152 then decide (BallClauseLogic.Endpoint q (141 : Vertex)) else (if i < 153 then decide (BallClauseLogic.Endpoint q (143 : Vertex)) else decide (BallClauseLogic.Endpoint q (144 : Vertex)))) else (if i < 156 then (if i < 155 then decide (BallClauseLogic.Endpoint q (145 : Vertex)) else decide (BallClauseLogic.Endpoint q (147 : Vertex))) else (if i < 157 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (152 : Vertex))))) else (if i < 162 then (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (156 : Vertex)) else decide (BallClauseLogic.Endpoint q (158 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (159 : Vertex)) else decide (BallClauseLogic.Endpoint q (192 : Vertex)))) else (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else decide (BallClauseLogic.Endpoint q (198 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (200 : Vertex)))))) else (if i < 174 then (if i < 170 then (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else decide (BallClauseLogic.Endpoint q (203 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (204 : Vertex)) else decide (BallClauseLogic.Endpoint q (206 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (210 : Vertex)) else decide (BallClauseLogic.Endpoint q (212 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (213 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex))))) else (if i < 178 then (if i < 176 then (if i < 175 then decide (BallClauseLogic.Endpoint q (215 : Vertex)) else decide (BallClauseLogic.Endpoint q (217 : Vertex))) else (if i < 177 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (219 : Vertex)))) else (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else decide (BallClauseLogic.Endpoint q (266 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (282 : Vertex)) else decide (BallClauseLogic.Endpoint q (284 : Vertex)))))))) else (if i < 212 then (if i < 197 then (if i < 189 then (if i < 185 then (if i < 183 then decide (BallClauseLogic.Endpoint q (286 : Vertex)) else (if i < 184 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else decide (BallClauseLogic.Endpoint q (321 : Vertex)))) else (if i < 187 then (if i < 186 then decide (BallClauseLogic.Endpoint q (324 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex))) else (if i < 188 then decide (BallClauseLogic.Endpoint q (328 : Vertex)) else decide (BallClauseLogic.Endpoint q (331 : Vertex))))) else (if i < 193 then (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (332 : Vertex)) else decide (BallClauseLogic.Endpoint q (334 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (338 : Vertex)) else decide (BallClauseLogic.Endpoint q (341 : Vertex)))) else (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (343 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (344 : Vertex)) else decide (BallClauseLogic.Endpoint q (345 : Vertex)))))) else (if i < 204 then (if i < 200 then (if i < 198 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else (if i < 199 then decide (BallClauseLogic.Endpoint q (347 : Vertex)) else decide (BallClauseLogic.Endpoint q (349 : Vertex)))) else (if i < 202 then (if i < 201 then decide (BallClauseLogic.Endpoint q (384 : Vertex)) else decide (BallClauseLogic.Endpoint q (385 : Vertex))) else (if i < 203 then decide (BallClauseLogic.Endpoint q (386 : Vertex)) else decide (BallClauseLogic.Endpoint q (388 : Vertex))))) else (if i < 208 then (if i < 206 then (if i < 205 then decide (BallClauseLogic.Endpoint q (389 : Vertex)) else decide (BallClauseLogic.Endpoint q (390 : Vertex))) else (if i < 207 then decide (BallClauseLogic.Endpoint q (392 : Vertex)) else decide (BallClauseLogic.Endpoint q (394 : Vertex)))) else (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (395 : Vertex)) else decide (BallClauseLogic.Endpoint q (396 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (398 : Vertex)) else decide (BallClauseLogic.Endpoint q (402 : Vertex))))))) else (if i < 227 then (if i < 219 then (if i < 215 then (if i < 213 then decide (BallClauseLogic.Endpoint q (405 : Vertex)) else (if i < 214 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (407 : Vertex)))) else (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (408 : Vertex)) else decide (BallClauseLogic.Endpoint q (409 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (411 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex))))) else (if i < 223 then (if i < 221 then (if i < 220 then decide (BallClauseLogic.Endpoint q (415 : Vertex)) else decide (BallClauseLogic.Endpoint q (448 : Vertex))) else (if i < 222 then decide (BallClauseLogic.Endpoint q (449 : Vertex)) else decide (BallClauseLogic.Endpoint q (450 : Vertex)))) else (if i < 225 then (if i < 224 then decide (BallClauseLogic.Endpoint q (451 : Vertex)) else decide (BallClauseLogic.Endpoint q (453 : Vertex))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (455 : Vertex)) else decide (BallClauseLogic.Endpoint q (456 : Vertex)))))) else (if i < 235 then (if i < 231 then (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (459 : Vertex)) else decide (BallClauseLogic.Endpoint q (460 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (461 : Vertex)) else decide (BallClauseLogic.Endpoint q (462 : Vertex)))) else (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (463 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (465 : Vertex)) else decide (BallClauseLogic.Endpoint q (466 : Vertex))))) else (if i < 239 then (if i < 237 then (if i < 236 then decide (BallClauseLogic.Endpoint q (467 : Vertex)) else decide (BallClauseLogic.Endpoint q (468 : Vertex))) else (if i < 238 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (474 : Vertex)))) else (if i < 241 then (if i < 240 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (476 : Vertex))) else (if i < 242 then decide (BallClauseLogic.Endpoint q (478 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count243 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [122, 123, 124]
def count247 (b : Nat → Bool) : Nat := countLit b [125, 126]
def count249 (b : Nat → Bool) : Nat := countLit b [127, 128]
def count251 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128]
def count253 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128]
def count255 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count259 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [129, 130, 131, 132, 133, 134, 135, 136]
def count269 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136]
def count271 (b : Nat → Bool) : Nat := countLit b [138, 139]
def count273 (b : Nat → Bool) : Nat := countLit b [137, 138, 139]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [140, 141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142, 143]
def count283 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147, 148, 149, 150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
def count299 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151]
def count301 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [152, 153, 154]
def count305 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [167, 168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [170, 171, 172, 173]
def count339 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 173]
def count341 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177]
def count347 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count349 (b : Nat → Bool) : Nat := countLit b [180, 182]
def count351 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189]
def count371 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189]
def count373 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193]
def count379 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count381 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count383 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count403 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [209, 210]
def count409 (b : Nat → Bool) : Nat := countLit b [211, 212]
def count411 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212]
def count413 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212]
def count415 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count417 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212]
def count419 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count421 (b : Nat → Bool) : Nat := countLit b [213, 214, 215]
def count423 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [218, 219]
def count427 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219]
def count429 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216, 217, 218, 219]
def count431 (b : Nat → Bool) : Nat := countLit b [220, 221]
def count433 (b : Nat → Bool) : Nat := countLit b [222, 223]
def count435 (b : Nat → Bool) : Nat := countLit b [220, 221, 222, 223]
def count437 (b : Nat → Bool) : Nat := countLit b [224, 225]
def count439 (b : Nat → Bool) : Nat := countLit b [226, 227]
def count441 (b : Nat → Bool) : Nat := countLit b [224, 225, 226, 227]
def count443 (b : Nat → Bool) : Nat := countLit b [220, 221, 222, 223, 224, 225, 226, 227]
def count445 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [228, 229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count455 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [228, 229, 230, 231, 232, 233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count463 (b : Nat → Bool) : Nat := countLit b [235, 236, 237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count469 (b : Nat → Bool) : Nat := countLit b [239, 240, 241, 242]
def count471 (b : Nat → Bool) : Nat := countLit b [235, 236, 237, 238, 239, 240, 241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count475 (b : Nat → Bool) : Nat := countLit b [213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count477 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count479 (b : Nat → Bool) : Nat := countLit b [122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242]
def count481 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count483 (b : Nat → Bool) : Nat := countLit b [1, 3, 4]
def count486 (b : Nat → Bool) : Nat := countLit b [6, 8]
def count488 (b : Nat → Bool) : Nat := countLit b [10, 12]
def count490 (b : Nat → Bool) : Nat := countLit b [6, 8, 10, 12]
def count494 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 10, 12]
def count501 (b : Nat → Bool) : Nat := countLit b [13, 15]
def count503 (b : Nat → Bool) : Nat := countLit b [17, 20]
def count505 (b : Nat → Bool) : Nat := countLit b [13, 15, 17, 20]
def count509 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count511 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count513 (b : Nat → Bool) : Nat := countLit b [22, 23, 25, 27]
def count517 (b : Nat → Bool) : Nat := countLit b [13, 15, 17, 20, 22, 23, 25, 27]
def count525 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 10, 12, 13, 15, 17, 20, 22, 23, 25, 27]
def count540 (b : Nat → Bool) : Nat := countLit b [29, 30]
def count542 (b : Nat → Bool) : Nat := countLit b [32, 34]
def count544 (b : Nat → Bool) : Nat := countLit b [29, 30, 32, 34]
def count548 (b : Nat → Bool) : Nat := countLit b [37, 39]
def count550 (b : Nat → Bool) : Nat := countLit b [40, 42]
def count552 (b : Nat → Bool) : Nat := countLit b [37, 39, 40, 42]
def count556 (b : Nat → Bool) : Nat := countLit b [29, 30, 32, 34, 37, 39, 40, 42]
def count564 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count566 (b : Nat → Bool) : Nat := countLit b [49, 50]
def count568 (b : Nat → Bool) : Nat := countLit b [45, 47, 49, 50]
def count572 (b : Nat → Bool) : Nat := countLit b [53, 56]
def count574 (b : Nat → Bool) : Nat := countLit b [57, 59]
def count576 (b : Nat → Bool) : Nat := countLit b [53, 56, 57, 59]
def count580 (b : Nat → Bool) : Nat := countLit b [45, 47, 49, 50, 53, 56, 57, 59]
def count588 (b : Nat → Bool) : Nat := countLit b [29, 30, 32, 34, 37, 39, 40, 42, 45, 47, 49, 50, 53, 56, 57, 59]
def count604 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 10, 12, 13, 15, 17, 20, 22, 23, 25, 27, 29, 30, 32, 34, 37, 39, 40, 42, 45, 47, 49, 50, 53, 56, 57, 59]
def count635 (b : Nat → Bool) : Nat := countLit b [62, 65]
def count637 (b : Nat → Bool) : Nat := countLit b [60, 62, 65]
def count640 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count642 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count644 (b : Nat → Bool) : Nat := countLit b [68, 70, 73, 74]
def count648 (b : Nat → Bool) : Nat := countLit b [60, 62, 65, 68, 70, 73, 74]
def count655 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count657 (b : Nat → Bool) : Nat := countLit b [79, 83]
def count659 (b : Nat → Bool) : Nat := countLit b [77, 78, 79, 83]
def count663 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count665 (b : Nat → Bool) : Nat := countLit b [88, 90]
def count667 (b : Nat → Bool) : Nat := countLit b [84, 86, 88, 90]
def count671 (b : Nat → Bool) : Nat := countLit b [77, 78, 79, 83, 84, 86, 88, 90]
def count679 (b : Nat → Bool) : Nat := countLit b [60, 62, 65, 68, 70, 73, 74, 77, 78, 79, 83, 84, 86, 88, 90]
def count694 (b : Nat → Bool) : Nat := countLit b [93, 94]
def count696 (b : Nat → Bool) : Nat := countLit b [96, 97]
def count698 (b : Nat → Bool) : Nat := countLit b [93, 94, 96, 97]
def count702 (b : Nat → Bool) : Nat := countLit b [100, 101]
def count704 (b : Nat → Bool) : Nat := countLit b [104, 105]
def count706 (b : Nat → Bool) : Nat := countLit b [100, 101, 104, 105]
def count710 (b : Nat → Bool) : Nat := countLit b [93, 94, 96, 97, 100, 101, 104, 105]
def count718 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count720 (b : Nat → Bool) : Nat := countLit b [109, 111]
def count722 (b : Nat → Bool) : Nat := countLit b [106, 108, 109, 111]
def count726 (b : Nat → Bool) : Nat := countLit b [114, 117]
def count728 (b : Nat → Bool) : Nat := countLit b [119, 121]
def count730 (b : Nat → Bool) : Nat := countLit b [114, 117, 119, 121]
def count734 (b : Nat → Bool) : Nat := countLit b [106, 108, 109, 111, 114, 117, 119, 121]
def count742 (b : Nat → Bool) : Nat := countLit b [93, 94, 96, 97, 100, 101, 104, 105, 106, 108, 109, 111, 114, 117, 119, 121]
def count758 (b : Nat → Bool) : Nat := countLit b [60, 62, 65, 68, 70, 73, 74, 77, 78, 79, 83, 84, 86, 88, 90, 93, 94, 96, 97, 100, 101, 104, 105, 106, 108, 109, 111, 114, 117, 119, 121]
def count789 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 8, 10, 12, 13, 15, 17, 20, 22, 23, 25, 27, 29, 30, 32, 34, 37, 39, 40, 42, 45, 47, 49, 50, 53, 56, 57, 59, 60, 62, 65, 68, 70, 73, 74, 77, 78, 79, 83, 84, 86, 88, 90, 93, 94, 96, 97, 100, 101, 104, 105, 106, 108, 109, 111, 114, 117, 119, 121]
def count831 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count833 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4]
def count836 (b : Nat → Bool) : Nat := countLit b [-6, -8]
def count838 (b : Nat → Bool) : Nat := countLit b [-10, -12]
def count840 (b : Nat → Bool) : Nat := countLit b [-6, -8, -10, -12]
def count844 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -10, -12]
def count851 (b : Nat → Bool) : Nat := countLit b [-13, -15]
def count853 (b : Nat → Bool) : Nat := countLit b [-17, -20]
def count855 (b : Nat → Bool) : Nat := countLit b [-13, -15, -17, -20]
def count859 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count861 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count863 (b : Nat → Bool) : Nat := countLit b [-22, -23, -25, -27]
def count867 (b : Nat → Bool) : Nat := countLit b [-13, -15, -17, -20, -22, -23, -25, -27]
def count875 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -10, -12, -13, -15, -17, -20, -22, -23, -25, -27]
def count890 (b : Nat → Bool) : Nat := countLit b [-29, -30]
def count892 (b : Nat → Bool) : Nat := countLit b [-32, -34]
def count894 (b : Nat → Bool) : Nat := countLit b [-29, -30, -32, -34]
def count898 (b : Nat → Bool) : Nat := countLit b [-37, -39]
def count900 (b : Nat → Bool) : Nat := countLit b [-40, -42]
def count902 (b : Nat → Bool) : Nat := countLit b [-37, -39, -40, -42]
def count906 (b : Nat → Bool) : Nat := countLit b [-29, -30, -32, -34, -37, -39, -40, -42]
def count914 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count916 (b : Nat → Bool) : Nat := countLit b [-49, -50]
def count918 (b : Nat → Bool) : Nat := countLit b [-45, -47, -49, -50]
def count922 (b : Nat → Bool) : Nat := countLit b [-53, -56]
def count924 (b : Nat → Bool) : Nat := countLit b [-57, -59]
def count926 (b : Nat → Bool) : Nat := countLit b [-53, -56, -57, -59]
def count930 (b : Nat → Bool) : Nat := countLit b [-45, -47, -49, -50, -53, -56, -57, -59]
def count938 (b : Nat → Bool) : Nat := countLit b [-29, -30, -32, -34, -37, -39, -40, -42, -45, -47, -49, -50, -53, -56, -57, -59]
def count954 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -10, -12, -13, -15, -17, -20, -22, -23, -25, -27, -29, -30, -32, -34, -37, -39, -40, -42, -45, -47, -49, -50, -53, -56, -57, -59]
def count976 (b : Nat → Bool) : Nat := countLit b [-62, -65]
def count978 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65]
def count981 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count983 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count985 (b : Nat → Bool) : Nat := countLit b [-68, -70, -73, -74]
def count989 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65, -68, -70, -73, -74]
def count996 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count998 (b : Nat → Bool) : Nat := countLit b [-79, -83]
def count1000 (b : Nat → Bool) : Nat := countLit b [-77, -78, -79, -83]
def count1004 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count1006 (b : Nat → Bool) : Nat := countLit b [-88, -90]
def count1008 (b : Nat → Bool) : Nat := countLit b [-84, -86, -88, -90]
def count1012 (b : Nat → Bool) : Nat := countLit b [-77, -78, -79, -83, -84, -86, -88, -90]
def count1020 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65, -68, -70, -73, -74, -77, -78, -79, -83, -84, -86, -88, -90]
def count1035 (b : Nat → Bool) : Nat := countLit b [-93, -94]
def count1037 (b : Nat → Bool) : Nat := countLit b [-96, -97]
def count1039 (b : Nat → Bool) : Nat := countLit b [-93, -94, -96, -97]
def count1043 (b : Nat → Bool) : Nat := countLit b [-100, -101]
def count1045 (b : Nat → Bool) : Nat := countLit b [-104, -105]
def count1047 (b : Nat → Bool) : Nat := countLit b [-100, -101, -104, -105]
def count1051 (b : Nat → Bool) : Nat := countLit b [-93, -94, -96, -97, -100, -101, -104, -105]
def count1059 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count1061 (b : Nat → Bool) : Nat := countLit b [-109, -111]
def count1063 (b : Nat → Bool) : Nat := countLit b [-106, -108, -109, -111]
def count1067 (b : Nat → Bool) : Nat := countLit b [-114, -117]
def count1069 (b : Nat → Bool) : Nat := countLit b [-119, -121]
def count1071 (b : Nat → Bool) : Nat := countLit b [-114, -117, -119, -121]
def count1075 (b : Nat → Bool) : Nat := countLit b [-106, -108, -109, -111, -114, -117, -119, -121]
def count1083 (b : Nat → Bool) : Nat := countLit b [-93, -94, -96, -97, -100, -101, -104, -105, -106, -108, -109, -111, -114, -117, -119, -121]
def count1099 (b : Nat → Bool) : Nat := countLit b [-60, -62, -65, -68, -70, -73, -74, -77, -78, -79, -83, -84, -86, -88, -90, -93, -94, -96, -97, -100, -101, -104, -105, -106, -108, -109, -111, -114, -117, -119, -121]
def count1121 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -8, -10, -12, -13, -15, -17, -20, -22, -23, -25, -27, -29, -30, -32, -34, -37, -39, -40, -42, -45, -47, -49, -50, -53, -56, -57, -59, -60, -62, -65, -68, -70, -73, -74, -77, -78, -79, -83, -84, -86, -88, -90, -93, -94, -96, -97, -100, -101, -104, -105, -106, -108, -109, -111, -114, -117, -119, -121]
def count1143 (b : Nat → Bool) : Nat := countLit b [5, 7]
def count1145 (b : Nat → Bool) : Nat := countLit b [2, 5, 7]
def count1148 (b : Nat → Bool) : Nat := countLit b [9, 11]
def count1150 (b : Nat → Bool) : Nat := countLit b [14, 16]
def count1152 (b : Nat → Bool) : Nat := countLit b [9, 11, 14, 16]
def count1156 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 9, 11, 14, 16]
def count1163 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count1165 (b : Nat → Bool) : Nat := countLit b [18, 19, 21]
def count1168 (b : Nat → Bool) : Nat := countLit b [24, 26]
def count1170 (b : Nat → Bool) : Nat := countLit b [28, 31]
def count1172 (b : Nat → Bool) : Nat := countLit b [24, 26, 28, 31]
def count1176 (b : Nat → Bool) : Nat := countLit b [18, 19, 21, 24, 26, 28, 31]
def count1183 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 9, 11, 14, 16, 18, 19, 21, 24, 26, 28, 31]
def count1197 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count1199 (b : Nat → Bool) : Nat := countLit b [33, 35, 36]
def count1202 (b : Nat → Bool) : Nat := countLit b [38, 41]
def count1204 (b : Nat → Bool) : Nat := countLit b [43, 44]
def count1206 (b : Nat → Bool) : Nat := countLit b [38, 41, 43, 44]
def count1210 (b : Nat → Bool) : Nat := countLit b [33, 35, 36, 38, 41, 43, 44]
def count1217 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count1219 (b : Nat → Bool) : Nat := countLit b [51, 52]
def count1221 (b : Nat → Bool) : Nat := countLit b [46, 48, 51, 52]
def count1225 (b : Nat → Bool) : Nat := countLit b [54, 55]
def count1227 (b : Nat → Bool) : Nat := countLit b [58, 61]
def count1229 (b : Nat → Bool) : Nat := countLit b [54, 55, 58, 61]
def count1233 (b : Nat → Bool) : Nat := countLit b [46, 48, 51, 52, 54, 55, 58, 61]
def count1241 (b : Nat → Bool) : Nat := countLit b [33, 35, 36, 38, 41, 43, 44, 46, 48, 51, 52, 54, 55, 58, 61]
def count1256 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 9, 11, 14, 16, 18, 19, 21, 24, 26, 28, 31, 33, 35, 36, 38, 41, 43, 44, 46, 48, 51, 52, 54, 55, 58, 61]
def count1285 (b : Nat → Bool) : Nat := countLit b [64, 66]
def count1287 (b : Nat → Bool) : Nat := countLit b [63, 64, 66]
def count1290 (b : Nat → Bool) : Nat := countLit b [67, 69]
def count1292 (b : Nat → Bool) : Nat := countLit b [71, 72]
def count1294 (b : Nat → Bool) : Nat := countLit b [67, 69, 71, 72]
def count1298 (b : Nat → Bool) : Nat := countLit b [63, 64, 66, 67, 69, 71, 72]
def count1305 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count1307 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count1309 (b : Nat → Bool) : Nat := countLit b [75, 76, 80, 81]
def count1313 (b : Nat → Bool) : Nat := countLit b [82, 85]
def count1315 (b : Nat → Bool) : Nat := countLit b [87, 89]
def count1317 (b : Nat → Bool) : Nat := countLit b [82, 85, 87, 89]
def count1321 (b : Nat → Bool) : Nat := countLit b [75, 76, 80, 81, 82, 85, 87, 89]
def count1329 (b : Nat → Bool) : Nat := countLit b [63, 64, 66, 67, 69, 71, 72, 75, 76, 80, 81, 82, 85, 87, 89]
def count1344 (b : Nat → Bool) : Nat := countLit b [92, 95]
def count1346 (b : Nat → Bool) : Nat := countLit b [91, 92, 95]
def count1349 (b : Nat → Bool) : Nat := countLit b [98, 99]
def count1351 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count1353 (b : Nat → Bool) : Nat := countLit b [98, 99, 102, 103]
def count1357 (b : Nat → Bool) : Nat := countLit b [91, 92, 95, 98, 99, 102, 103]
def count1364 (b : Nat → Bool) : Nat := countLit b [107, 110]
def count1366 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count1368 (b : Nat → Bool) : Nat := countLit b [107, 110, 112, 113]
def count1372 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count1374 (b : Nat → Bool) : Nat := countLit b [118, 120]
def count1376 (b : Nat → Bool) : Nat := countLit b [115, 116, 118, 120]
def count1380 (b : Nat → Bool) : Nat := countLit b [107, 110, 112, 113, 115, 116, 118, 120]
def count1388 (b : Nat → Bool) : Nat := countLit b [91, 92, 95, 98, 99, 102, 103, 107, 110, 112, 113, 115, 116, 118, 120]
def count1403 (b : Nat → Bool) : Nat := countLit b [63, 64, 66, 67, 69, 71, 72, 75, 76, 80, 81, 82, 85, 87, 89, 91, 92, 95, 98, 99, 102, 103, 107, 110, 112, 113, 115, 116, 118, 120]
def count1433 (b : Nat → Bool) : Nat := countLit b [2, 5, 7, 9, 11, 14, 16, 18, 19, 21, 24, 26, 28, 31, 33, 35, 36, 38, 41, 43, 44, 46, 48, 51, 52, 54, 55, 58, 61, 63, 64, 66, 67, 69, 71, 72, 75, 76, 80, 81, 82, 85, 87, 89, 91, 92, 95, 98, 99, 102, 103, 107, 110, 112, 113, 115, 116, 118, 120]
def count1475 (b : Nat → Bool) : Nat := countLit b [-5, -7]
def count1477 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7]
def count1480 (b : Nat → Bool) : Nat := countLit b [-9, -11]
def count1482 (b : Nat → Bool) : Nat := countLit b [-14, -16]
def count1484 (b : Nat → Bool) : Nat := countLit b [-9, -11, -14, -16]
def count1488 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -9, -11, -14, -16]
def count1495 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count1497 (b : Nat → Bool) : Nat := countLit b [-18, -19, -21]
def count1500 (b : Nat → Bool) : Nat := countLit b [-24, -26]
def count1502 (b : Nat → Bool) : Nat := countLit b [-28, -31]
def count1504 (b : Nat → Bool) : Nat := countLit b [-24, -26, -28, -31]
def count1508 (b : Nat → Bool) : Nat := countLit b [-18, -19, -21, -24, -26, -28, -31]
def count1515 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31]
def count1529 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count1531 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36]
def count1534 (b : Nat → Bool) : Nat := countLit b [-38, -41]
def count1536 (b : Nat → Bool) : Nat := countLit b [-43, -44]
def count1538 (b : Nat → Bool) : Nat := countLit b [-38, -41, -43, -44]
def count1542 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36, -38, -41, -43, -44]
def count1549 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count1551 (b : Nat → Bool) : Nat := countLit b [-51, -52]
def count1553 (b : Nat → Bool) : Nat := countLit b [-46, -48, -51, -52]
def count1557 (b : Nat → Bool) : Nat := countLit b [-54, -55]
def count1559 (b : Nat → Bool) : Nat := countLit b [-58, -61]
def count1561 (b : Nat → Bool) : Nat := countLit b [-54, -55, -58, -61]
def count1565 (b : Nat → Bool) : Nat := countLit b [-46, -48, -51, -52, -54, -55, -58, -61]
def count1573 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]
def count1588 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]
def count1607 (b : Nat → Bool) : Nat := countLit b [-64, -66]
def count1609 (b : Nat → Bool) : Nat := countLit b [-63, -64, -66]
def count1612 (b : Nat → Bool) : Nat := countLit b [-67, -69]
def count1614 (b : Nat → Bool) : Nat := countLit b [-71, -72]
def count1616 (b : Nat → Bool) : Nat := countLit b [-67, -69, -71, -72]
def count1620 (b : Nat → Bool) : Nat := countLit b [-63, -64, -66, -67, -69, -71, -72]
def count1627 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count1629 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1631 (b : Nat → Bool) : Nat := countLit b [-75, -76, -80, -81]
def count1635 (b : Nat → Bool) : Nat := countLit b [-82, -85]
def count1637 (b : Nat → Bool) : Nat := countLit b [-87, -89]
def count1639 (b : Nat → Bool) : Nat := countLit b [-82, -85, -87, -89]
def count1643 (b : Nat → Bool) : Nat := countLit b [-75, -76, -80, -81, -82, -85, -87, -89]
def count1651 (b : Nat → Bool) : Nat := countLit b [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]
def count1666 (b : Nat → Bool) : Nat := countLit b [-92, -95]
def count1668 (b : Nat → Bool) : Nat := countLit b [-91, -92, -95]
def count1671 (b : Nat → Bool) : Nat := countLit b [-98, -99]
def count1673 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1675 (b : Nat → Bool) : Nat := countLit b [-98, -99, -102, -103]
def count1679 (b : Nat → Bool) : Nat := countLit b [-91, -92, -95, -98, -99, -102, -103]
def count1686 (b : Nat → Bool) : Nat := countLit b [-107, -110]
def count1688 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1690 (b : Nat → Bool) : Nat := countLit b [-107, -110, -112, -113]
def count1694 (b : Nat → Bool) : Nat := countLit b [-115, -116]
def count1696 (b : Nat → Bool) : Nat := countLit b [-118, -120]
def count1698 (b : Nat → Bool) : Nat := countLit b [-115, -116, -118, -120]
def count1702 (b : Nat → Bool) : Nat := countLit b [-107, -110, -112, -113, -115, -116, -118, -120]
def count1710 (b : Nat → Bool) : Nat := countLit b [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]
def count1725 (b : Nat → Bool) : Nat := countLit b [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]
def count1744 (b : Nat → Bool) : Nat := countLit b [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61, -63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 881 then (if i < 440 then (if i < 220 then (if i < 110 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 20 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 18 then (if i < 17 then b 16 else b 17) else (if i < 19 then b 18 else b 19))) else (if i < 23 then (if i < 21 then b 20 else (if i < 22 then b 21 else b 22)) else (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else b 26))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 32 then (if i < 31 then b 30 else b 31) else (if i < 33 then b 32 else b 33))) else (if i < 37 then (if i < 35 then b 34 else (if i < 36 then b 35 else b 36)) else (if i < 39 then (if i < 38 then b 37 else b 38) else (if i < 40 then b 39 else b 40)))) else (if i < 48 then (if i < 44 then (if i < 42 then b 41 else (if i < 43 then b 42 else b 43)) else (if i < 46 then (if i < 45 then b 44 else b 45) else (if i < 47 then b 46 else b 47))) else (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 53 then (if i < 52 then b 51 else b 52) else (if i < 54 then b 53 else b 54)))))) else (if i < 82 then (if i < 68 then (if i < 61 then (if i < 58 then (if i < 56 then b 55 else (if i < 57 then b 56 else b 57)) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60))) else (if i < 64 then (if i < 62 then b 61 else (if i < 63 then b 62 else b 63)) else (if i < 66 then (if i < 65 then b 64 else b 65) else (if i < 67 then b 66 else b 67)))) else (if i < 75 then (if i < 71 then (if i < 69 then b 68 else (if i < 70 then b 69 else b 70)) else (if i < 73 then (if i < 72 then b 71 else b 72) else (if i < 74 then b 73 else b 74))) else (if i < 78 then (if i < 76 then b 75 else (if i < 77 then b 76 else b 77)) else (if i < 80 then (if i < 79 then b 78 else b 79) else (if i < 81 then b 80 else b 81))))) else (if i < 96 then (if i < 89 then (if i < 85 then (if i < 83 then b 82 else (if i < 84 then b 83 else b 84)) else (if i < 87 then (if i < 86 then b 85 else b 86) else (if i < 88 then b 87 else b 88))) else (if i < 92 then (if i < 90 then b 89 else (if i < 91 then b 90 else b 91)) else (if i < 94 then (if i < 93 then b 92 else b 93) else (if i < 95 then b 94 else b 95)))) else (if i < 103 then (if i < 99 then (if i < 97 then b 96 else (if i < 98 then b 97 else b 98)) else (if i < 101 then (if i < 100 then b 99 else b 100) else (if i < 102 then b 101 else b 102))) else (if i < 106 then (if i < 104 then b 103 else (if i < 105 then b 104 else b 105)) else (if i < 108 then (if i < 107 then b 106 else b 107) else (if i < 109 then b 108 else b 109))))))) else (if i < 165 then (if i < 137 then (if i < 123 then (if i < 116 then (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 114 then b 113 else (if i < 115 then b 114 else b 115))) else (if i < 119 then (if i < 117 then b 116 else (if i < 118 then b 117 else b 118)) else (if i < 121 then (if i < 120 then b 119 else b 120) else (if i < 122 then b 121 else b 122)))) else (if i < 130 then (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else b 129))) else (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 135 then (if i < 134 then b 133 else b 134) else (if i < 136 then b 135 else b 136))))) else (if i < 151 then (if i < 144 then (if i < 140 then (if i < 138 then b 137 else (if i < 139 then b 138 else b 139)) else (if i < 142 then (if i < 141 then b 140 else b 141) else (if i < 143 then b 142 else b 143))) else (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 149 then (if i < 148 then b 147 else b 148) else (if i < 150 then b 149 else b 150)))) else (if i < 158 then (if i < 154 then (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)) else (if i < 156 then (if i < 155 then b 154 else b 155) else (if i < 157 then b 156 else b 157))) else (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 163 then (if i < 162 then b 161 else b 162) else (if i < 164 then b 163 else b 164)))))) else (if i < 192 then (if i < 178 then (if i < 171 then (if i < 168 then (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)) else (if i < 169 then b 168 else (if i < 170 then b 169 else b 170))) else (if i < 174 then (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)) else (if i < 176 then (if i < 175 then b 174 else b 175) else (if i < 177 then b 176 else b 177)))) else (if i < 185 then (if i < 181 then (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)) else (if i < 183 then (if i < 182 then b 181 else b 182) else (if i < 184 then b 183 else b 184))) else (if i < 188 then (if i < 186 then b 185 else (if i < 187 then b 186 else b 187)) else (if i < 190 then (if i < 189 then b 188 else b 189) else (if i < 191 then b 190 else b 191))))) else (if i < 206 then (if i < 199 then (if i < 195 then (if i < 193 then b 192 else (if i < 194 then b 193 else b 194)) else (if i < 197 then (if i < 196 then b 195 else b 196) else (if i < 198 then b 197 else b 198))) else (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 204 then (if i < 203 then b 202 else b 203) else (if i < 205 then b 204 else b 205)))) else (if i < 213 then (if i < 209 then (if i < 207 then b 206 else (if i < 208 then b 207 else b 208)) else (if i < 211 then (if i < 210 then b 209 else b 210) else (if i < 212 then b 211 else b 212))) else (if i < 216 then (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)) else (if i < 218 then (if i < 217 then b 216 else b 217) else (if i < 219 then b 218 else b 219)))))))) else (if i < 330 then (if i < 275 then (if i < 247 then (if i < 233 then (if i < 226 then (if i < 223 then (if i < 221 then b 220 else (if i < 222 then b 221 else b 222)) else (if i < 224 then b 223 else (if i < 225 then b 224 else b 225))) else (if i < 229 then (if i < 227 then b 226 else (if i < 228 then b 227 else b 228)) else (if i < 231 then (if i < 230 then b 229 else b 230) else (if i < 232 then b 231 else b 232)))) else (if i < 240 then (if i < 236 then (if i < 234 then b 233 else (if i < 235 then b 234 else b 235)) else (if i < 238 then (if i < 237 then b 236 else b 237) else (if i < 239 then b 238 else b 239))) else (if i < 243 then (if i < 241 then b 240 else (if i < 242 then b 241 else b 242)) else (if i < 245 then (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b)) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)))))) else (if i < 261 then (if i < 254 then (if i < 250 then (if i < 248 then decide (1 ≤ count247 b) else (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b))) else (if i < 252 then (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)) else (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)))) else (if i < 257 then (if i < 255 then decide (2 ≤ count253 b) else (if i < 256 then decide (1 ≤ count255 b) else decide (2 ≤ count255 b))) else (if i < 259 then (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))))) else (if i < 268 then (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 266 then (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b)) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)))) else (if i < 271 then (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b))) else (if i < 273 then (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)) else (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b))))))) else (if i < 302 then (if i < 288 then (if i < 281 then (if i < 278 then (if i < 276 then decide (1 ≤ count275 b) else (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b))) else (if i < 279 then decide (2 ≤ count277 b) else (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)))) else (if i < 284 then (if i < 282 then decide (1 ≤ count281 b) else (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b))) else (if i < 286 then (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)) else (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b))))) else (if i < 295 then (if i < 291 then (if i < 289 then decide (2 ≤ count287 b) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))) else (if i < 293 then (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b)) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)))) else (if i < 298 then (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))) else (if i < 300 then (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))))) else (if i < 316 then (if i < 309 then (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 307 then (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))) else (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))))) else (if i < 323 then (if i < 319 then (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))) else (if i < 321 then (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b)) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)))) else (if i < 326 then (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b))) else (if i < 328 then (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b)) else (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)))))))) else (if i < 385 then (if i < 357 then (if i < 343 then (if i < 336 then (if i < 333 then (if i < 331 then decide (2 ≤ count329 b) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b))) else (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b)))) else (if i < 339 then (if i < 337 then decide (2 ≤ count335 b) else (if i < 338 then decide (1 ≤ count337 b) else decide (2 ≤ count337 b))) else (if i < 341 then (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b)) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))))) else (if i < 350 then (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))) else (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 355 then (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)))))) else (if i < 371 then (if i < 364 then (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 362 then (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b)))) else (if i < 367 then (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))) else (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))))) else (if i < 378 then (if i < 374 then (if i < 372 then decide (1 ≤ count371 b) else (if i < 373 then decide (2 ≤ count371 b) else decide (1 ≤ count373 b))) else (if i < 376 then (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b)))) else (if i < 381 then (if i < 379 then decide (2 ≤ count377 b) else (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b))) else (if i < 383 then (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))))))) else (if i < 412 then (if i < 398 then (if i < 391 then (if i < 388 then (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b))) else (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)))) else (if i < 394 then (if i < 392 then decide (1 ≤ count391 b) else (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b))) else (if i < 396 then (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))))) else (if i < 405 then (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 403 then (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b)) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b)))) else (if i < 408 then (if i < 406 then decide (1 ≤ count405 b) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))) else (if i < 410 then (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b)))))) else (if i < 426 then (if i < 419 then (if i < 415 then (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b))) else (if i < 417 then (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b)) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b)))) else (if i < 422 then (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))) else (if i < 424 then (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)) else (if i < 425 then decide (2 ≤ count423 b) else decide (1 ≤ count425 b))))) else (if i < 433 then (if i < 429 then (if i < 427 then decide (2 ≤ count425 b) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b))) else (if i < 431 then (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)))) else (if i < 436 then (if i < 434 then decide (1 ≤ count433 b) else (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b))) else (if i < 438 then (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b)) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b)))))))))) else (if i < 660 then (if i < 550 then (if i < 495 then (if i < 467 then (if i < 453 then (if i < 446 then (if i < 443 then (if i < 441 then decide (2 ≤ count439 b) else (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b))) else (if i < 444 then decide (1 ≤ count443 b) else (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)))) else (if i < 449 then (if i < 447 then decide (2 ≤ count445 b) else (if i < 448 then decide (1 ≤ count447 b) else decide (2 ≤ count447 b))) else (if i < 451 then (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b))))) else (if i < 460 then (if i < 456 then (if i < 454 then decide (1 ≤ count453 b) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b))) else (if i < 458 then (if i < 457 then decide (2 ≤ count455 b) else decide (1 ≤ count457 b)) else (if i < 459 then decide (2 ≤ count457 b) else decide (1 ≤ count459 b)))) else (if i < 463 then (if i < 461 then decide (2 ≤ count459 b) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b))) else (if i < 465 then (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b)) else (if i < 466 then decide (1 ≤ count465 b) else decide (2 ≤ count465 b)))))) else (if i < 481 then (if i < 474 then (if i < 470 then (if i < 468 then decide (1 ≤ count467 b) else (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b))) else (if i < 472 then (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b)) else (if i < 473 then decide (2 ≤ count471 b) else decide (1 ≤ count473 b)))) else (if i < 477 then (if i < 475 then decide (2 ≤ count473 b) else (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b))) else (if i < 479 then (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b)) else (if i < 480 then decide (1 ≤ count479 b) else decide (2 ≤ count479 b))))) else (if i < 488 then (if i < 484 then (if i < 482 then decide (1 ≤ count481 b) else (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b))) else (if i < 486 then (if i < 485 then decide (2 ≤ count483 b) else decide (3 ≤ count483 b)) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b)))) else (if i < 491 then (if i < 489 then decide (1 ≤ count488 b) else (if i < 490 then decide (2 ≤ count488 b) else decide (1 ≤ count490 b))) else (if i < 493 then (if i < 492 then decide (2 ≤ count490 b) else decide (3 ≤ count490 b)) else (if i < 494 then decide (4 ≤ count490 b) else decide (1 ≤ count494 b))))))) else (if i < 522 then (if i < 508 then (if i < 501 then (if i < 498 then (if i < 496 then decide (2 ≤ count494 b) else (if i < 497 then decide (3 ≤ count494 b) else decide (4 ≤ count494 b))) else (if i < 499 then decide (5 ≤ count494 b) else (if i < 500 then decide (6 ≤ count494 b) else decide (7 ≤ count494 b)))) else (if i < 504 then (if i < 502 then decide (1 ≤ count501 b) else (if i < 503 then decide (2 ≤ count501 b) else decide (1 ≤ count503 b))) else (if i < 506 then (if i < 505 then decide (2 ≤ count503 b) else decide (1 ≤ count505 b)) else (if i < 507 then decide (2 ≤ count505 b) else decide (3 ≤ count505 b))))) else (if i < 515 then (if i < 511 then (if i < 509 then decide (4 ≤ count505 b) else (if i < 510 then decide (1 ≤ count509 b) else decide (2 ≤ count509 b))) else (if i < 513 then (if i < 512 then decide (1 ≤ count511 b) else decide (2 ≤ count511 b)) else (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b)))) else (if i < 518 then (if i < 516 then decide (3 ≤ count513 b) else (if i < 517 then decide (4 ≤ count513 b) else decide (1 ≤ count517 b))) else (if i < 520 then (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b)) else (if i < 521 then decide (4 ≤ count517 b) else decide (5 ≤ count517 b)))))) else (if i < 536 then (if i < 529 then (if i < 525 then (if i < 523 then decide (6 ≤ count517 b) else (if i < 524 then decide (7 ≤ count517 b) else decide (8 ≤ count517 b))) else (if i < 527 then (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b)) else (if i < 528 then decide (3 ≤ count525 b) else decide (4 ≤ count525 b)))) else (if i < 532 then (if i < 530 then decide (5 ≤ count525 b) else (if i < 531 then decide (6 ≤ count525 b) else decide (7 ≤ count525 b))) else (if i < 534 then (if i < 533 then decide (8 ≤ count525 b) else decide (9 ≤ count525 b)) else (if i < 535 then decide (10 ≤ count525 b) else decide (11 ≤ count525 b))))) else (if i < 543 then (if i < 539 then (if i < 537 then decide (12 ≤ count525 b) else (if i < 538 then decide (13 ≤ count525 b) else decide (14 ≤ count525 b))) else (if i < 541 then (if i < 540 then decide (15 ≤ count525 b) else decide (1 ≤ count540 b)) else (if i < 542 then decide (2 ≤ count540 b) else decide (1 ≤ count542 b)))) else (if i < 546 then (if i < 544 then decide (2 ≤ count542 b) else (if i < 545 then decide (1 ≤ count544 b) else decide (2 ≤ count544 b))) else (if i < 548 then (if i < 547 then decide (3 ≤ count544 b) else decide (4 ≤ count544 b)) else (if i < 549 then decide (1 ≤ count548 b) else decide (2 ≤ count548 b)))))))) else (if i < 605 then (if i < 577 then (if i < 563 then (if i < 556 then (if i < 553 then (if i < 551 then decide (1 ≤ count550 b) else (if i < 552 then decide (2 ≤ count550 b) else decide (1 ≤ count552 b))) else (if i < 554 then decide (2 ≤ count552 b) else (if i < 555 then decide (3 ≤ count552 b) else decide (4 ≤ count552 b)))) else (if i < 559 then (if i < 557 then decide (1 ≤ count556 b) else (if i < 558 then decide (2 ≤ count556 b) else decide (3 ≤ count556 b))) else (if i < 561 then (if i < 560 then decide (4 ≤ count556 b) else decide (5 ≤ count556 b)) else (if i < 562 then decide (6 ≤ count556 b) else decide (7 ≤ count556 b))))) else (if i < 570 then (if i < 566 then (if i < 564 then decide (8 ≤ count556 b) else (if i < 565 then decide (1 ≤ count564 b) else decide (2 ≤ count564 b))) else (if i < 568 then (if i < 567 then decide (1 ≤ count566 b) else decide (2 ≤ count566 b)) else (if i < 569 then decide (1 ≤ count568 b) else decide (2 ≤ count568 b)))) else (if i < 573 then (if i < 571 then decide (3 ≤ count568 b) else (if i < 572 then decide (4 ≤ count568 b) else decide (1 ≤ count572 b))) else (if i < 575 then (if i < 574 then decide (2 ≤ count572 b) else decide (1 ≤ count574 b)) else (if i < 576 then decide (2 ≤ count574 b) else decide (1 ≤ count576 b)))))) else (if i < 591 then (if i < 584 then (if i < 580 then (if i < 578 then decide (2 ≤ count576 b) else (if i < 579 then decide (3 ≤ count576 b) else decide (4 ≤ count576 b))) else (if i < 582 then (if i < 581 then decide (1 ≤ count580 b) else decide (2 ≤ count580 b)) else (if i < 583 then decide (3 ≤ count580 b) else decide (4 ≤ count580 b)))) else (if i < 587 then (if i < 585 then decide (5 ≤ count580 b) else (if i < 586 then decide (6 ≤ count580 b) else decide (7 ≤ count580 b))) else (if i < 589 then (if i < 588 then decide (8 ≤ count580 b) else decide (1 ≤ count588 b)) else (if i < 590 then decide (2 ≤ count588 b) else decide (3 ≤ count588 b))))) else (if i < 598 then (if i < 594 then (if i < 592 then decide (4 ≤ count588 b) else (if i < 593 then decide (5 ≤ count588 b) else decide (6 ≤ count588 b))) else (if i < 596 then (if i < 595 then decide (7 ≤ count588 b) else decide (8 ≤ count588 b)) else (if i < 597 then decide (9 ≤ count588 b) else decide (10 ≤ count588 b)))) else (if i < 601 then (if i < 599 then decide (11 ≤ count588 b) else (if i < 600 then decide (12 ≤ count588 b) else decide (13 ≤ count588 b))) else (if i < 603 then (if i < 602 then decide (14 ≤ count588 b) else decide (15 ≤ count588 b)) else (if i < 604 then decide (16 ≤ count588 b) else decide (1 ≤ count604 b))))))) else (if i < 632 then (if i < 618 then (if i < 611 then (if i < 608 then (if i < 606 then decide (2 ≤ count604 b) else (if i < 607 then decide (3 ≤ count604 b) else decide (4 ≤ count604 b))) else (if i < 609 then decide (5 ≤ count604 b) else (if i < 610 then decide (6 ≤ count604 b) else decide (7 ≤ count604 b)))) else (if i < 614 then (if i < 612 then decide (8 ≤ count604 b) else (if i < 613 then decide (9 ≤ count604 b) else decide (10 ≤ count604 b))) else (if i < 616 then (if i < 615 then decide (11 ≤ count604 b) else decide (12 ≤ count604 b)) else (if i < 617 then decide (13 ≤ count604 b) else decide (14 ≤ count604 b))))) else (if i < 625 then (if i < 621 then (if i < 619 then decide (15 ≤ count604 b) else (if i < 620 then decide (16 ≤ count604 b) else decide (17 ≤ count604 b))) else (if i < 623 then (if i < 622 then decide (18 ≤ count604 b) else decide (19 ≤ count604 b)) else (if i < 624 then decide (20 ≤ count604 b) else decide (21 ≤ count604 b)))) else (if i < 628 then (if i < 626 then decide (22 ≤ count604 b) else (if i < 627 then decide (23 ≤ count604 b) else decide (24 ≤ count604 b))) else (if i < 630 then (if i < 629 then decide (25 ≤ count604 b) else decide (26 ≤ count604 b)) else (if i < 631 then decide (27 ≤ count604 b) else decide (28 ≤ count604 b)))))) else (if i < 646 then (if i < 639 then (if i < 635 then (if i < 633 then decide (29 ≤ count604 b) else (if i < 634 then decide (30 ≤ count604 b) else decide (31 ≤ count604 b))) else (if i < 637 then (if i < 636 then decide (1 ≤ count635 b) else decide (2 ≤ count635 b)) else (if i < 638 then decide (1 ≤ count637 b) else decide (2 ≤ count637 b)))) else (if i < 642 then (if i < 640 then decide (3 ≤ count637 b) else (if i < 641 then decide (1 ≤ count640 b) else decide (2 ≤ count640 b))) else (if i < 644 then (if i < 643 then decide (1 ≤ count642 b) else decide (2 ≤ count642 b)) else (if i < 645 then decide (1 ≤ count644 b) else decide (2 ≤ count644 b))))) else (if i < 653 then (if i < 649 then (if i < 647 then decide (3 ≤ count644 b) else (if i < 648 then decide (4 ≤ count644 b) else decide (1 ≤ count648 b))) else (if i < 651 then (if i < 650 then decide (2 ≤ count648 b) else decide (3 ≤ count648 b)) else (if i < 652 then decide (4 ≤ count648 b) else decide (5 ≤ count648 b)))) else (if i < 656 then (if i < 654 then decide (6 ≤ count648 b) else (if i < 655 then decide (7 ≤ count648 b) else decide (1 ≤ count655 b))) else (if i < 658 then (if i < 657 then decide (2 ≤ count655 b) else decide (1 ≤ count657 b)) else (if i < 659 then decide (2 ≤ count657 b) else decide (1 ≤ count659 b))))))))) else (if i < 770 then (if i < 715 then (if i < 687 then (if i < 673 then (if i < 666 then (if i < 663 then (if i < 661 then decide (2 ≤ count659 b) else (if i < 662 then decide (3 ≤ count659 b) else decide (4 ≤ count659 b))) else (if i < 664 then decide (1 ≤ count663 b) else (if i < 665 then decide (2 ≤ count663 b) else decide (1 ≤ count665 b)))) else (if i < 669 then (if i < 667 then decide (2 ≤ count665 b) else (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b))) else (if i < 671 then (if i < 670 then decide (3 ≤ count667 b) else decide (4 ≤ count667 b)) else (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b))))) else (if i < 680 then (if i < 676 then (if i < 674 then decide (3 ≤ count671 b) else (if i < 675 then decide (4 ≤ count671 b) else decide (5 ≤ count671 b))) else (if i < 678 then (if i < 677 then decide (6 ≤ count671 b) else decide (7 ≤ count671 b)) else (if i < 679 then decide (8 ≤ count671 b) else decide (1 ≤ count679 b)))) else (if i < 683 then (if i < 681 then decide (2 ≤ count679 b) else (if i < 682 then decide (3 ≤ count679 b) else decide (4 ≤ count679 b))) else (if i < 685 then (if i < 684 then decide (5 ≤ count679 b) else decide (6 ≤ count679 b)) else (if i < 686 then decide (7 ≤ count679 b) else decide (8 ≤ count679 b)))))) else (if i < 701 then (if i < 694 then (if i < 690 then (if i < 688 then decide (9 ≤ count679 b) else (if i < 689 then decide (10 ≤ count679 b) else decide (11 ≤ count679 b))) else (if i < 692 then (if i < 691 then decide (12 ≤ count679 b) else decide (13 ≤ count679 b)) else (if i < 693 then decide (14 ≤ count679 b) else decide (15 ≤ count679 b)))) else (if i < 697 then (if i < 695 then decide (1 ≤ count694 b) else (if i < 696 then decide (2 ≤ count694 b) else decide (1 ≤ count696 b))) else (if i < 699 then (if i < 698 then decide (2 ≤ count696 b) else decide (1 ≤ count698 b)) else (if i < 700 then decide (2 ≤ count698 b) else decide (3 ≤ count698 b))))) else (if i < 708 then (if i < 704 then (if i < 702 then decide (4 ≤ count698 b) else (if i < 703 then decide (1 ≤ count702 b) else decide (2 ≤ count702 b))) else (if i < 706 then (if i < 705 then decide (1 ≤ count704 b) else decide (2 ≤ count704 b)) else (if i < 707 then decide (1 ≤ count706 b) else decide (2 ≤ count706 b)))) else (if i < 711 then (if i < 709 then decide (3 ≤ count706 b) else (if i < 710 then decide (4 ≤ count706 b) else decide (1 ≤ count710 b))) else (if i < 713 then (if i < 712 then decide (2 ≤ count710 b) else decide (3 ≤ count710 b)) else (if i < 714 then decide (4 ≤ count710 b) else decide (5 ≤ count710 b))))))) else (if i < 742 then (if i < 728 then (if i < 721 then (if i < 718 then (if i < 716 then decide (6 ≤ count710 b) else (if i < 717 then decide (7 ≤ count710 b) else decide (8 ≤ count710 b))) else (if i < 719 then decide (1 ≤ count718 b) else (if i < 720 then decide (2 ≤ count718 b) else decide (1 ≤ count720 b)))) else (if i < 724 then (if i < 722 then decide (2 ≤ count720 b) else (if i < 723 then decide (1 ≤ count722 b) else decide (2 ≤ count722 b))) else (if i < 726 then (if i < 725 then decide (3 ≤ count722 b) else decide (4 ≤ count722 b)) else (if i < 727 then decide (1 ≤ count726 b) else decide (2 ≤ count726 b))))) else (if i < 735 then (if i < 731 then (if i < 729 then decide (1 ≤ count728 b) else (if i < 730 then decide (2 ≤ count728 b) else decide (1 ≤ count730 b))) else (if i < 733 then (if i < 732 then decide (2 ≤ count730 b) else decide (3 ≤ count730 b)) else (if i < 734 then decide (4 ≤ count730 b) else decide (1 ≤ count734 b)))) else (if i < 738 then (if i < 736 then decide (2 ≤ count734 b) else (if i < 737 then decide (3 ≤ count734 b) else decide (4 ≤ count734 b))) else (if i < 740 then (if i < 739 then decide (5 ≤ count734 b) else decide (6 ≤ count734 b)) else (if i < 741 then decide (7 ≤ count734 b) else decide (8 ≤ count734 b)))))) else (if i < 756 then (if i < 749 then (if i < 745 then (if i < 743 then decide (1 ≤ count742 b) else (if i < 744 then decide (2 ≤ count742 b) else decide (3 ≤ count742 b))) else (if i < 747 then (if i < 746 then decide (4 ≤ count742 b) else decide (5 ≤ count742 b)) else (if i < 748 then decide (6 ≤ count742 b) else decide (7 ≤ count742 b)))) else (if i < 752 then (if i < 750 then decide (8 ≤ count742 b) else (if i < 751 then decide (9 ≤ count742 b) else decide (10 ≤ count742 b))) else (if i < 754 then (if i < 753 then decide (11 ≤ count742 b) else decide (12 ≤ count742 b)) else (if i < 755 then decide (13 ≤ count742 b) else decide (14 ≤ count742 b))))) else (if i < 763 then (if i < 759 then (if i < 757 then decide (15 ≤ count742 b) else (if i < 758 then decide (16 ≤ count742 b) else decide (1 ≤ count758 b))) else (if i < 761 then (if i < 760 then decide (2 ≤ count758 b) else decide (3 ≤ count758 b)) else (if i < 762 then decide (4 ≤ count758 b) else decide (5 ≤ count758 b)))) else (if i < 766 then (if i < 764 then decide (6 ≤ count758 b) else (if i < 765 then decide (7 ≤ count758 b) else decide (8 ≤ count758 b))) else (if i < 768 then (if i < 767 then decide (9 ≤ count758 b) else decide (10 ≤ count758 b)) else (if i < 769 then decide (11 ≤ count758 b) else decide (12 ≤ count758 b)))))))) else (if i < 825 then (if i < 797 then (if i < 783 then (if i < 776 then (if i < 773 then (if i < 771 then decide (13 ≤ count758 b) else (if i < 772 then decide (14 ≤ count758 b) else decide (15 ≤ count758 b))) else (if i < 774 then decide (16 ≤ count758 b) else (if i < 775 then decide (17 ≤ count758 b) else decide (18 ≤ count758 b)))) else (if i < 779 then (if i < 777 then decide (19 ≤ count758 b) else (if i < 778 then decide (20 ≤ count758 b) else decide (21 ≤ count758 b))) else (if i < 781 then (if i < 780 then decide (22 ≤ count758 b) else decide (23 ≤ count758 b)) else (if i < 782 then decide (24 ≤ count758 b) else decide (25 ≤ count758 b))))) else (if i < 790 then (if i < 786 then (if i < 784 then decide (26 ≤ count758 b) else (if i < 785 then decide (27 ≤ count758 b) else decide (28 ≤ count758 b))) else (if i < 788 then (if i < 787 then decide (29 ≤ count758 b) else decide (30 ≤ count758 b)) else (if i < 789 then decide (31 ≤ count758 b) else decide (1 ≤ count789 b)))) else (if i < 793 then (if i < 791 then decide (2 ≤ count789 b) else (if i < 792 then decide (3 ≤ count789 b) else decide (4 ≤ count789 b))) else (if i < 795 then (if i < 794 then decide (5 ≤ count789 b) else decide (6 ≤ count789 b)) else (if i < 796 then decide (7 ≤ count789 b) else decide (8 ≤ count789 b)))))) else (if i < 811 then (if i < 804 then (if i < 800 then (if i < 798 then decide (9 ≤ count789 b) else (if i < 799 then decide (10 ≤ count789 b) else decide (11 ≤ count789 b))) else (if i < 802 then (if i < 801 then decide (12 ≤ count789 b) else decide (13 ≤ count789 b)) else (if i < 803 then decide (14 ≤ count789 b) else decide (15 ≤ count789 b)))) else (if i < 807 then (if i < 805 then decide (16 ≤ count789 b) else (if i < 806 then decide (17 ≤ count789 b) else decide (18 ≤ count789 b))) else (if i < 809 then (if i < 808 then decide (19 ≤ count789 b) else decide (20 ≤ count789 b)) else (if i < 810 then decide (21 ≤ count789 b) else decide (22 ≤ count789 b))))) else (if i < 818 then (if i < 814 then (if i < 812 then decide (23 ≤ count789 b) else (if i < 813 then decide (24 ≤ count789 b) else decide (25 ≤ count789 b))) else (if i < 816 then (if i < 815 then decide (26 ≤ count789 b) else decide (27 ≤ count789 b)) else (if i < 817 then decide (28 ≤ count789 b) else decide (29 ≤ count789 b)))) else (if i < 821 then (if i < 819 then decide (30 ≤ count789 b) else (if i < 820 then decide (31 ≤ count789 b) else decide (32 ≤ count789 b))) else (if i < 823 then (if i < 822 then decide (33 ≤ count789 b) else decide (34 ≤ count789 b)) else (if i < 824 then decide (35 ≤ count789 b) else decide (36 ≤ count789 b))))))) else (if i < 853 then (if i < 839 then (if i < 832 then (if i < 828 then (if i < 826 then decide (37 ≤ count789 b) else (if i < 827 then decide (38 ≤ count789 b) else decide (39 ≤ count789 b))) else (if i < 830 then (if i < 829 then decide (40 ≤ count789 b) else decide (41 ≤ count789 b)) else (if i < 831 then decide (42 ≤ count789 b) else decide (1 ≤ count831 b)))) else (if i < 835 then (if i < 833 then decide (2 ≤ count831 b) else (if i < 834 then decide (1 ≤ count833 b) else decide (2 ≤ count833 b))) else (if i < 837 then (if i < 836 then decide (3 ≤ count833 b) else decide (1 ≤ count836 b)) else (if i < 838 then decide (2 ≤ count836 b) else decide (1 ≤ count838 b))))) else (if i < 846 then (if i < 842 then (if i < 840 then decide (2 ≤ count838 b) else (if i < 841 then decide (1 ≤ count840 b) else decide (2 ≤ count840 b))) else (if i < 844 then (if i < 843 then decide (3 ≤ count840 b) else decide (4 ≤ count840 b)) else (if i < 845 then decide (1 ≤ count844 b) else decide (2 ≤ count844 b)))) else (if i < 849 then (if i < 847 then decide (3 ≤ count844 b) else (if i < 848 then decide (4 ≤ count844 b) else decide (5 ≤ count844 b))) else (if i < 851 then (if i < 850 then decide (6 ≤ count844 b) else decide (7 ≤ count844 b)) else (if i < 852 then decide (1 ≤ count851 b) else decide (2 ≤ count851 b)))))) else (if i < 867 then (if i < 860 then (if i < 856 then (if i < 854 then decide (1 ≤ count853 b) else (if i < 855 then decide (2 ≤ count853 b) else decide (1 ≤ count855 b))) else (if i < 858 then (if i < 857 then decide (2 ≤ count855 b) else decide (3 ≤ count855 b)) else (if i < 859 then decide (4 ≤ count855 b) else decide (1 ≤ count859 b)))) else (if i < 863 then (if i < 861 then decide (2 ≤ count859 b) else (if i < 862 then decide (1 ≤ count861 b) else decide (2 ≤ count861 b))) else (if i < 865 then (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b)) else (if i < 866 then decide (3 ≤ count863 b) else decide (4 ≤ count863 b))))) else (if i < 874 then (if i < 870 then (if i < 868 then decide (1 ≤ count867 b) else (if i < 869 then decide (2 ≤ count867 b) else decide (3 ≤ count867 b))) else (if i < 872 then (if i < 871 then decide (4 ≤ count867 b) else decide (5 ≤ count867 b)) else (if i < 873 then decide (6 ≤ count867 b) else decide (7 ≤ count867 b)))) else (if i < 877 then (if i < 875 then decide (8 ≤ count867 b) else (if i < 876 then decide (1 ≤ count875 b) else decide (2 ≤ count875 b))) else (if i < 879 then (if i < 878 then decide (3 ≤ count875 b) else decide (4 ≤ count875 b)) else (if i < 880 then decide (5 ≤ count875 b) else decide (6 ≤ count875 b))))))))))) else (if i < 1322 then (if i < 1101 then (if i < 991 then (if i < 936 then (if i < 908 then (if i < 894 then (if i < 887 then (if i < 884 then (if i < 882 then decide (7 ≤ count875 b) else (if i < 883 then decide (8 ≤ count875 b) else decide (9 ≤ count875 b))) else (if i < 885 then decide (10 ≤ count875 b) else (if i < 886 then decide (11 ≤ count875 b) else decide (12 ≤ count875 b)))) else (if i < 890 then (if i < 888 then decide (13 ≤ count875 b) else (if i < 889 then decide (14 ≤ count875 b) else decide (15 ≤ count875 b))) else (if i < 892 then (if i < 891 then decide (1 ≤ count890 b) else decide (2 ≤ count890 b)) else (if i < 893 then decide (1 ≤ count892 b) else decide (2 ≤ count892 b))))) else (if i < 901 then (if i < 897 then (if i < 895 then decide (1 ≤ count894 b) else (if i < 896 then decide (2 ≤ count894 b) else decide (3 ≤ count894 b))) else (if i < 899 then (if i < 898 then decide (4 ≤ count894 b) else decide (1 ≤ count898 b)) else (if i < 900 then decide (2 ≤ count898 b) else decide (1 ≤ count900 b)))) else (if i < 904 then (if i < 902 then decide (2 ≤ count900 b) else (if i < 903 then decide (1 ≤ count902 b) else decide (2 ≤ count902 b))) else (if i < 906 then (if i < 905 then decide (3 ≤ count902 b) else decide (4 ≤ count902 b)) else (if i < 907 then decide (1 ≤ count906 b) else decide (2 ≤ count906 b)))))) else (if i < 922 then (if i < 915 then (if i < 911 then (if i < 909 then decide (3 ≤ count906 b) else (if i < 910 then decide (4 ≤ count906 b) else decide (5 ≤ count906 b))) else (if i < 913 then (if i < 912 then decide (6 ≤ count906 b) else decide (7 ≤ count906 b)) else (if i < 914 then decide (8 ≤ count906 b) else decide (1 ≤ count914 b)))) else (if i < 918 then (if i < 916 then decide (2 ≤ count914 b) else (if i < 917 then decide (1 ≤ count916 b) else decide (2 ≤ count916 b))) else (if i < 920 then (if i < 919 then decide (1 ≤ count918 b) else decide (2 ≤ count918 b)) else (if i < 921 then decide (3 ≤ count918 b) else decide (4 ≤ count918 b))))) else (if i < 929 then (if i < 925 then (if i < 923 then decide (1 ≤ count922 b) else (if i < 924 then decide (2 ≤ count922 b) else decide (1 ≤ count924 b))) else (if i < 927 then (if i < 926 then decide (2 ≤ count924 b) else decide (1 ≤ count926 b)) else (if i < 928 then decide (2 ≤ count926 b) else decide (3 ≤ count926 b)))) else (if i < 932 then (if i < 930 then decide (4 ≤ count926 b) else (if i < 931 then decide (1 ≤ count930 b) else decide (2 ≤ count930 b))) else (if i < 934 then (if i < 933 then decide (3 ≤ count930 b) else decide (4 ≤ count930 b)) else (if i < 935 then decide (5 ≤ count930 b) else decide (6 ≤ count930 b))))))) else (if i < 963 then (if i < 949 then (if i < 942 then (if i < 939 then (if i < 937 then decide (7 ≤ count930 b) else (if i < 938 then decide (8 ≤ count930 b) else decide (1 ≤ count938 b))) else (if i < 940 then decide (2 ≤ count938 b) else (if i < 941 then decide (3 ≤ count938 b) else decide (4 ≤ count938 b)))) else (if i < 945 then (if i < 943 then decide (5 ≤ count938 b) else (if i < 944 then decide (6 ≤ count938 b) else decide (7 ≤ count938 b))) else (if i < 947 then (if i < 946 then decide (8 ≤ count938 b) else decide (9 ≤ count938 b)) else (if i < 948 then decide (10 ≤ count938 b) else decide (11 ≤ count938 b))))) else (if i < 956 then (if i < 952 then (if i < 950 then decide (12 ≤ count938 b) else (if i < 951 then decide (13 ≤ count938 b) else decide (14 ≤ count938 b))) else (if i < 954 then (if i < 953 then decide (15 ≤ count938 b) else decide (16 ≤ count938 b)) else (if i < 955 then decide (1 ≤ count954 b) else decide (2 ≤ count954 b)))) else (if i < 959 then (if i < 957 then decide (3 ≤ count954 b) else (if i < 958 then decide (4 ≤ count954 b) else decide (5 ≤ count954 b))) else (if i < 961 then (if i < 960 then decide (6 ≤ count954 b) else decide (7 ≤ count954 b)) else (if i < 962 then decide (8 ≤ count954 b) else decide (9 ≤ count954 b)))))) else (if i < 977 then (if i < 970 then (if i < 966 then (if i < 964 then decide (10 ≤ count954 b) else (if i < 965 then decide (11 ≤ count954 b) else decide (12 ≤ count954 b))) else (if i < 968 then (if i < 967 then decide (13 ≤ count954 b) else decide (14 ≤ count954 b)) else (if i < 969 then decide (15 ≤ count954 b) else decide (16 ≤ count954 b)))) else (if i < 973 then (if i < 971 then decide (17 ≤ count954 b) else (if i < 972 then decide (18 ≤ count954 b) else decide (19 ≤ count954 b))) else (if i < 975 then (if i < 974 then decide (20 ≤ count954 b) else decide (21 ≤ count954 b)) else (if i < 976 then decide (22 ≤ count954 b) else decide (1 ≤ count976 b))))) else (if i < 984 then (if i < 980 then (if i < 978 then decide (2 ≤ count976 b) else (if i < 979 then decide (1 ≤ count978 b) else decide (2 ≤ count978 b))) else (if i < 982 then (if i < 981 then decide (3 ≤ count978 b) else decide (1 ≤ count981 b)) else (if i < 983 then decide (2 ≤ count981 b) else decide (1 ≤ count983 b)))) else (if i < 987 then (if i < 985 then decide (2 ≤ count983 b) else (if i < 986 then decide (1 ≤ count985 b) else decide (2 ≤ count985 b))) else (if i < 989 then (if i < 988 then decide (3 ≤ count985 b) else decide (4 ≤ count985 b)) else (if i < 990 then decide (1 ≤ count989 b) else decide (2 ≤ count989 b)))))))) else (if i < 1046 then (if i < 1018 then (if i < 1004 then (if i < 997 then (if i < 994 then (if i < 992 then decide (3 ≤ count989 b) else (if i < 993 then decide (4 ≤ count989 b) else decide (5 ≤ count989 b))) else (if i < 995 then decide (6 ≤ count989 b) else (if i < 996 then decide (7 ≤ count989 b) else decide (1 ≤ count996 b)))) else (if i < 1000 then (if i < 998 then decide (2 ≤ count996 b) else (if i < 999 then decide (1 ≤ count998 b) else decide (2 ≤ count998 b))) else (if i < 1002 then (if i < 1001 then decide (1 ≤ count1000 b) else decide (2 ≤ count1000 b)) else (if i < 1003 then decide (3 ≤ count1000 b) else decide (4 ≤ count1000 b))))) else (if i < 1011 then (if i < 1007 then (if i < 1005 then decide (1 ≤ count1004 b) else (if i < 1006 then decide (2 ≤ count1004 b) else decide (1 ≤ count1006 b))) else (if i < 1009 then (if i < 1008 then decide (2 ≤ count1006 b) else decide (1 ≤ count1008 b)) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (3 ≤ count1008 b)))) else (if i < 1014 then (if i < 1012 then decide (4 ≤ count1008 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b))) else (if i < 1016 then (if i < 1015 then decide (3 ≤ count1012 b) else decide (4 ≤ count1012 b)) else (if i < 1017 then decide (5 ≤ count1012 b) else decide (6 ≤ count1012 b)))))) else (if i < 1032 then (if i < 1025 then (if i < 1021 then (if i < 1019 then decide (7 ≤ count1012 b) else (if i < 1020 then decide (8 ≤ count1012 b) else decide (1 ≤ count1020 b))) else (if i < 1023 then (if i < 1022 then decide (2 ≤ count1020 b) else decide (3 ≤ count1020 b)) else (if i < 1024 then decide (4 ≤ count1020 b) else decide (5 ≤ count1020 b)))) else (if i < 1028 then (if i < 1026 then decide (6 ≤ count1020 b) else (if i < 1027 then decide (7 ≤ count1020 b) else decide (8 ≤ count1020 b))) else (if i < 1030 then (if i < 1029 then decide (9 ≤ count1020 b) else decide (10 ≤ count1020 b)) else (if i < 1031 then decide (11 ≤ count1020 b) else decide (12 ≤ count1020 b))))) else (if i < 1039 then (if i < 1035 then (if i < 1033 then decide (13 ≤ count1020 b) else (if i < 1034 then decide (14 ≤ count1020 b) else decide (15 ≤ count1020 b))) else (if i < 1037 then (if i < 1036 then decide (1 ≤ count1035 b) else decide (2 ≤ count1035 b)) else (if i < 1038 then decide (1 ≤ count1037 b) else decide (2 ≤ count1037 b)))) else (if i < 1042 then (if i < 1040 then decide (1 ≤ count1039 b) else (if i < 1041 then decide (2 ≤ count1039 b) else decide (3 ≤ count1039 b))) else (if i < 1044 then (if i < 1043 then decide (4 ≤ count1039 b) else decide (1 ≤ count1043 b)) else (if i < 1045 then decide (2 ≤ count1043 b) else decide (1 ≤ count1045 b))))))) else (if i < 1073 then (if i < 1059 then (if i < 1052 then (if i < 1049 then (if i < 1047 then decide (2 ≤ count1045 b) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b))) else (if i < 1050 then decide (3 ≤ count1047 b) else (if i < 1051 then decide (4 ≤ count1047 b) else decide (1 ≤ count1051 b)))) else (if i < 1055 then (if i < 1053 then decide (2 ≤ count1051 b) else (if i < 1054 then decide (3 ≤ count1051 b) else decide (4 ≤ count1051 b))) else (if i < 1057 then (if i < 1056 then decide (5 ≤ count1051 b) else decide (6 ≤ count1051 b)) else (if i < 1058 then decide (7 ≤ count1051 b) else decide (8 ≤ count1051 b))))) else (if i < 1066 then (if i < 1062 then (if i < 1060 then decide (1 ≤ count1059 b) else (if i < 1061 then decide (2 ≤ count1059 b) else decide (1 ≤ count1061 b))) else (if i < 1064 then (if i < 1063 then decide (2 ≤ count1061 b) else decide (1 ≤ count1063 b)) else (if i < 1065 then decide (2 ≤ count1063 b) else decide (3 ≤ count1063 b)))) else (if i < 1069 then (if i < 1067 then decide (4 ≤ count1063 b) else (if i < 1068 then decide (1 ≤ count1067 b) else decide (2 ≤ count1067 b))) else (if i < 1071 then (if i < 1070 then decide (1 ≤ count1069 b) else decide (2 ≤ count1069 b)) else (if i < 1072 then decide (1 ≤ count1071 b) else decide (2 ≤ count1071 b)))))) else (if i < 1087 then (if i < 1080 then (if i < 1076 then (if i < 1074 then decide (3 ≤ count1071 b) else (if i < 1075 then decide (4 ≤ count1071 b) else decide (1 ≤ count1075 b))) else (if i < 1078 then (if i < 1077 then decide (2 ≤ count1075 b) else decide (3 ≤ count1075 b)) else (if i < 1079 then decide (4 ≤ count1075 b) else decide (5 ≤ count1075 b)))) else (if i < 1083 then (if i < 1081 then decide (6 ≤ count1075 b) else (if i < 1082 then decide (7 ≤ count1075 b) else decide (8 ≤ count1075 b))) else (if i < 1085 then (if i < 1084 then decide (1 ≤ count1083 b) else decide (2 ≤ count1083 b)) else (if i < 1086 then decide (3 ≤ count1083 b) else decide (4 ≤ count1083 b))))) else (if i < 1094 then (if i < 1090 then (if i < 1088 then decide (5 ≤ count1083 b) else (if i < 1089 then decide (6 ≤ count1083 b) else decide (7 ≤ count1083 b))) else (if i < 1092 then (if i < 1091 then decide (8 ≤ count1083 b) else decide (9 ≤ count1083 b)) else (if i < 1093 then decide (10 ≤ count1083 b) else decide (11 ≤ count1083 b)))) else (if i < 1097 then (if i < 1095 then decide (12 ≤ count1083 b) else (if i < 1096 then decide (13 ≤ count1083 b) else decide (14 ≤ count1083 b))) else (if i < 1099 then (if i < 1098 then decide (15 ≤ count1083 b) else decide (16 ≤ count1083 b)) else (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b))))))))) else (if i < 1211 then (if i < 1156 then (if i < 1128 then (if i < 1114 then (if i < 1107 then (if i < 1104 then (if i < 1102 then decide (3 ≤ count1099 b) else (if i < 1103 then decide (4 ≤ count1099 b) else decide (5 ≤ count1099 b))) else (if i < 1105 then decide (6 ≤ count1099 b) else (if i < 1106 then decide (7 ≤ count1099 b) else decide (8 ≤ count1099 b)))) else (if i < 1110 then (if i < 1108 then decide (9 ≤ count1099 b) else (if i < 1109 then decide (10 ≤ count1099 b) else decide (11 ≤ count1099 b))) else (if i < 1112 then (if i < 1111 then decide (12 ≤ count1099 b) else decide (13 ≤ count1099 b)) else (if i < 1113 then decide (14 ≤ count1099 b) else decide (15 ≤ count1099 b))))) else (if i < 1121 then (if i < 1117 then (if i < 1115 then decide (16 ≤ count1099 b) else (if i < 1116 then decide (17 ≤ count1099 b) else decide (18 ≤ count1099 b))) else (if i < 1119 then (if i < 1118 then decide (19 ≤ count1099 b) else decide (20 ≤ count1099 b)) else (if i < 1120 then decide (21 ≤ count1099 b) else decide (22 ≤ count1099 b)))) else (if i < 1124 then (if i < 1122 then decide (1 ≤ count1121 b) else (if i < 1123 then decide (2 ≤ count1121 b) else decide (3 ≤ count1121 b))) else (if i < 1126 then (if i < 1125 then decide (4 ≤ count1121 b) else decide (5 ≤ count1121 b)) else (if i < 1127 then decide (6 ≤ count1121 b) else decide (7 ≤ count1121 b)))))) else (if i < 1142 then (if i < 1135 then (if i < 1131 then (if i < 1129 then decide (8 ≤ count1121 b) else (if i < 1130 then decide (9 ≤ count1121 b) else decide (10 ≤ count1121 b))) else (if i < 1133 then (if i < 1132 then decide (11 ≤ count1121 b) else decide (12 ≤ count1121 b)) else (if i < 1134 then decide (13 ≤ count1121 b) else decide (14 ≤ count1121 b)))) else (if i < 1138 then (if i < 1136 then decide (15 ≤ count1121 b) else (if i < 1137 then decide (16 ≤ count1121 b) else decide (17 ≤ count1121 b))) else (if i < 1140 then (if i < 1139 then decide (18 ≤ count1121 b) else decide (19 ≤ count1121 b)) else (if i < 1141 then decide (20 ≤ count1121 b) else decide (21 ≤ count1121 b))))) else (if i < 1149 then (if i < 1145 then (if i < 1143 then decide (22 ≤ count1121 b) else (if i < 1144 then decide (1 ≤ count1143 b) else decide (2 ≤ count1143 b))) else (if i < 1147 then (if i < 1146 then decide (1 ≤ count1145 b) else decide (2 ≤ count1145 b)) else (if i < 1148 then decide (3 ≤ count1145 b) else decide (1 ≤ count1148 b)))) else (if i < 1152 then (if i < 1150 then decide (2 ≤ count1148 b) else (if i < 1151 then decide (1 ≤ count1150 b) else decide (2 ≤ count1150 b))) else (if i < 1154 then (if i < 1153 then decide (1 ≤ count1152 b) else decide (2 ≤ count1152 b)) else (if i < 1155 then decide (3 ≤ count1152 b) else decide (4 ≤ count1152 b))))))) else (if i < 1183 then (if i < 1169 then (if i < 1162 then (if i < 1159 then (if i < 1157 then decide (1 ≤ count1156 b) else (if i < 1158 then decide (2 ≤ count1156 b) else decide (3 ≤ count1156 b))) else (if i < 1160 then decide (4 ≤ count1156 b) else (if i < 1161 then decide (5 ≤ count1156 b) else decide (6 ≤ count1156 b)))) else (if i < 1165 then (if i < 1163 then decide (7 ≤ count1156 b) else (if i < 1164 then decide (1 ≤ count1163 b) else decide (2 ≤ count1163 b))) else (if i < 1167 then (if i < 1166 then decide (1 ≤ count1165 b) else decide (2 ≤ count1165 b)) else (if i < 1168 then decide (3 ≤ count1165 b) else decide (1 ≤ count1168 b))))) else (if i < 1176 then (if i < 1172 then (if i < 1170 then decide (2 ≤ count1168 b) else (if i < 1171 then decide (1 ≤ count1170 b) else decide (2 ≤ count1170 b))) else (if i < 1174 then (if i < 1173 then decide (1 ≤ count1172 b) else decide (2 ≤ count1172 b)) else (if i < 1175 then decide (3 ≤ count1172 b) else decide (4 ≤ count1172 b)))) else (if i < 1179 then (if i < 1177 then decide (1 ≤ count1176 b) else (if i < 1178 then decide (2 ≤ count1176 b) else decide (3 ≤ count1176 b))) else (if i < 1181 then (if i < 1180 then decide (4 ≤ count1176 b) else decide (5 ≤ count1176 b)) else (if i < 1182 then decide (6 ≤ count1176 b) else decide (7 ≤ count1176 b)))))) else (if i < 1197 then (if i < 1190 then (if i < 1186 then (if i < 1184 then decide (1 ≤ count1183 b) else (if i < 1185 then decide (2 ≤ count1183 b) else decide (3 ≤ count1183 b))) else (if i < 1188 then (if i < 1187 then decide (4 ≤ count1183 b) else decide (5 ≤ count1183 b)) else (if i < 1189 then decide (6 ≤ count1183 b) else decide (7 ≤ count1183 b)))) else (if i < 1193 then (if i < 1191 then decide (8 ≤ count1183 b) else (if i < 1192 then decide (9 ≤ count1183 b) else decide (10 ≤ count1183 b))) else (if i < 1195 then (if i < 1194 then decide (11 ≤ count1183 b) else decide (12 ≤ count1183 b)) else (if i < 1196 then decide (13 ≤ count1183 b) else decide (14 ≤ count1183 b))))) else (if i < 1204 then (if i < 1200 then (if i < 1198 then decide (1 ≤ count1197 b) else (if i < 1199 then decide (2 ≤ count1197 b) else decide (1 ≤ count1199 b))) else (if i < 1202 then (if i < 1201 then decide (2 ≤ count1199 b) else decide (3 ≤ count1199 b)) else (if i < 1203 then decide (1 ≤ count1202 b) else decide (2 ≤ count1202 b)))) else (if i < 1207 then (if i < 1205 then decide (1 ≤ count1204 b) else (if i < 1206 then decide (2 ≤ count1204 b) else decide (1 ≤ count1206 b))) else (if i < 1209 then (if i < 1208 then decide (2 ≤ count1206 b) else decide (3 ≤ count1206 b)) else (if i < 1210 then decide (4 ≤ count1206 b) else decide (1 ≤ count1210 b)))))))) else (if i < 1266 then (if i < 1238 then (if i < 1224 then (if i < 1217 then (if i < 1214 then (if i < 1212 then decide (2 ≤ count1210 b) else (if i < 1213 then decide (3 ≤ count1210 b) else decide (4 ≤ count1210 b))) else (if i < 1215 then decide (5 ≤ count1210 b) else (if i < 1216 then decide (6 ≤ count1210 b) else decide (7 ≤ count1210 b)))) else (if i < 1220 then (if i < 1218 then decide (1 ≤ count1217 b) else (if i < 1219 then decide (2 ≤ count1217 b) else decide (1 ≤ count1219 b))) else (if i < 1222 then (if i < 1221 then decide (2 ≤ count1219 b) else decide (1 ≤ count1221 b)) else (if i < 1223 then decide (2 ≤ count1221 b) else decide (3 ≤ count1221 b))))) else (if i < 1231 then (if i < 1227 then (if i < 1225 then decide (4 ≤ count1221 b) else (if i < 1226 then decide (1 ≤ count1225 b) else decide (2 ≤ count1225 b))) else (if i < 1229 then (if i < 1228 then decide (1 ≤ count1227 b) else decide (2 ≤ count1227 b)) else (if i < 1230 then decide (1 ≤ count1229 b) else decide (2 ≤ count1229 b)))) else (if i < 1234 then (if i < 1232 then decide (3 ≤ count1229 b) else (if i < 1233 then decide (4 ≤ count1229 b) else decide (1 ≤ count1233 b))) else (if i < 1236 then (if i < 1235 then decide (2 ≤ count1233 b) else decide (3 ≤ count1233 b)) else (if i < 1237 then decide (4 ≤ count1233 b) else decide (5 ≤ count1233 b)))))) else (if i < 1252 then (if i < 1245 then (if i < 1241 then (if i < 1239 then decide (6 ≤ count1233 b) else (if i < 1240 then decide (7 ≤ count1233 b) else decide (8 ≤ count1233 b))) else (if i < 1243 then (if i < 1242 then decide (1 ≤ count1241 b) else decide (2 ≤ count1241 b)) else (if i < 1244 then decide (3 ≤ count1241 b) else decide (4 ≤ count1241 b)))) else (if i < 1248 then (if i < 1246 then decide (5 ≤ count1241 b) else (if i < 1247 then decide (6 ≤ count1241 b) else decide (7 ≤ count1241 b))) else (if i < 1250 then (if i < 1249 then decide (8 ≤ count1241 b) else decide (9 ≤ count1241 b)) else (if i < 1251 then decide (10 ≤ count1241 b) else decide (11 ≤ count1241 b))))) else (if i < 1259 then (if i < 1255 then (if i < 1253 then decide (12 ≤ count1241 b) else (if i < 1254 then decide (13 ≤ count1241 b) else decide (14 ≤ count1241 b))) else (if i < 1257 then (if i < 1256 then decide (15 ≤ count1241 b) else decide (1 ≤ count1256 b)) else (if i < 1258 then decide (2 ≤ count1256 b) else decide (3 ≤ count1256 b)))) else (if i < 1262 then (if i < 1260 then decide (4 ≤ count1256 b) else (if i < 1261 then decide (5 ≤ count1256 b) else decide (6 ≤ count1256 b))) else (if i < 1264 then (if i < 1263 then decide (7 ≤ count1256 b) else decide (8 ≤ count1256 b)) else (if i < 1265 then decide (9 ≤ count1256 b) else decide (10 ≤ count1256 b))))))) else (if i < 1294 then (if i < 1280 then (if i < 1273 then (if i < 1269 then (if i < 1267 then decide (11 ≤ count1256 b) else (if i < 1268 then decide (12 ≤ count1256 b) else decide (13 ≤ count1256 b))) else (if i < 1271 then (if i < 1270 then decide (14 ≤ count1256 b) else decide (15 ≤ count1256 b)) else (if i < 1272 then decide (16 ≤ count1256 b) else decide (17 ≤ count1256 b)))) else (if i < 1276 then (if i < 1274 then decide (18 ≤ count1256 b) else (if i < 1275 then decide (19 ≤ count1256 b) else decide (20 ≤ count1256 b))) else (if i < 1278 then (if i < 1277 then decide (21 ≤ count1256 b) else decide (22 ≤ count1256 b)) else (if i < 1279 then decide (23 ≤ count1256 b) else decide (24 ≤ count1256 b))))) else (if i < 1287 then (if i < 1283 then (if i < 1281 then decide (25 ≤ count1256 b) else (if i < 1282 then decide (26 ≤ count1256 b) else decide (27 ≤ count1256 b))) else (if i < 1285 then (if i < 1284 then decide (28 ≤ count1256 b) else decide (29 ≤ count1256 b)) else (if i < 1286 then decide (1 ≤ count1285 b) else decide (2 ≤ count1285 b)))) else (if i < 1290 then (if i < 1288 then decide (1 ≤ count1287 b) else (if i < 1289 then decide (2 ≤ count1287 b) else decide (3 ≤ count1287 b))) else (if i < 1292 then (if i < 1291 then decide (1 ≤ count1290 b) else decide (2 ≤ count1290 b)) else (if i < 1293 then decide (1 ≤ count1292 b) else decide (2 ≤ count1292 b)))))) else (if i < 1308 then (if i < 1301 then (if i < 1297 then (if i < 1295 then decide (1 ≤ count1294 b) else (if i < 1296 then decide (2 ≤ count1294 b) else decide (3 ≤ count1294 b))) else (if i < 1299 then (if i < 1298 then decide (4 ≤ count1294 b) else decide (1 ≤ count1298 b)) else (if i < 1300 then decide (2 ≤ count1298 b) else decide (3 ≤ count1298 b)))) else (if i < 1304 then (if i < 1302 then decide (4 ≤ count1298 b) else (if i < 1303 then decide (5 ≤ count1298 b) else decide (6 ≤ count1298 b))) else (if i < 1306 then (if i < 1305 then decide (7 ≤ count1298 b) else decide (1 ≤ count1305 b)) else (if i < 1307 then decide (2 ≤ count1305 b) else decide (1 ≤ count1307 b))))) else (if i < 1315 then (if i < 1311 then (if i < 1309 then decide (2 ≤ count1307 b) else (if i < 1310 then decide (1 ≤ count1309 b) else decide (2 ≤ count1309 b))) else (if i < 1313 then (if i < 1312 then decide (3 ≤ count1309 b) else decide (4 ≤ count1309 b)) else (if i < 1314 then decide (1 ≤ count1313 b) else decide (2 ≤ count1313 b)))) else (if i < 1318 then (if i < 1316 then decide (1 ≤ count1315 b) else (if i < 1317 then decide (2 ≤ count1315 b) else decide (1 ≤ count1317 b))) else (if i < 1320 then (if i < 1319 then decide (2 ≤ count1317 b) else decide (3 ≤ count1317 b)) else (if i < 1321 then decide (4 ≤ count1317 b) else decide (1 ≤ count1321 b)))))))))) else (if i < 1542 then (if i < 1432 then (if i < 1377 then (if i < 1349 then (if i < 1335 then (if i < 1328 then (if i < 1325 then (if i < 1323 then decide (2 ≤ count1321 b) else (if i < 1324 then decide (3 ≤ count1321 b) else decide (4 ≤ count1321 b))) else (if i < 1326 then decide (5 ≤ count1321 b) else (if i < 1327 then decide (6 ≤ count1321 b) else decide (7 ≤ count1321 b)))) else (if i < 1331 then (if i < 1329 then decide (8 ≤ count1321 b) else (if i < 1330 then decide (1 ≤ count1329 b) else decide (2 ≤ count1329 b))) else (if i < 1333 then (if i < 1332 then decide (3 ≤ count1329 b) else decide (4 ≤ count1329 b)) else (if i < 1334 then decide (5 ≤ count1329 b) else decide (6 ≤ count1329 b))))) else (if i < 1342 then (if i < 1338 then (if i < 1336 then decide (7 ≤ count1329 b) else (if i < 1337 then decide (8 ≤ count1329 b) else decide (9 ≤ count1329 b))) else (if i < 1340 then (if i < 1339 then decide (10 ≤ count1329 b) else decide (11 ≤ count1329 b)) else (if i < 1341 then decide (12 ≤ count1329 b) else decide (13 ≤ count1329 b)))) else (if i < 1345 then (if i < 1343 then decide (14 ≤ count1329 b) else (if i < 1344 then decide (15 ≤ count1329 b) else decide (1 ≤ count1344 b))) else (if i < 1347 then (if i < 1346 then decide (2 ≤ count1344 b) else decide (1 ≤ count1346 b)) else (if i < 1348 then decide (2 ≤ count1346 b) else decide (3 ≤ count1346 b)))))) else (if i < 1363 then (if i < 1356 then (if i < 1352 then (if i < 1350 then decide (1 ≤ count1349 b) else (if i < 1351 then decide (2 ≤ count1349 b) else decide (1 ≤ count1351 b))) else (if i < 1354 then (if i < 1353 then decide (2 ≤ count1351 b) else decide (1 ≤ count1353 b)) else (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b)))) else (if i < 1359 then (if i < 1357 then decide (4 ≤ count1353 b) else (if i < 1358 then decide (1 ≤ count1357 b) else decide (2 ≤ count1357 b))) else (if i < 1361 then (if i < 1360 then decide (3 ≤ count1357 b) else decide (4 ≤ count1357 b)) else (if i < 1362 then decide (5 ≤ count1357 b) else decide (6 ≤ count1357 b))))) else (if i < 1370 then (if i < 1366 then (if i < 1364 then decide (7 ≤ count1357 b) else (if i < 1365 then decide (1 ≤ count1364 b) else decide (2 ≤ count1364 b))) else (if i < 1368 then (if i < 1367 then decide (1 ≤ count1366 b) else decide (2 ≤ count1366 b)) else (if i < 1369 then decide (1 ≤ count1368 b) else decide (2 ≤ count1368 b)))) else (if i < 1373 then (if i < 1371 then decide (3 ≤ count1368 b) else (if i < 1372 then decide (4 ≤ count1368 b) else decide (1 ≤ count1372 b))) else (if i < 1375 then (if i < 1374 then decide (2 ≤ count1372 b) else decide (1 ≤ count1374 b)) else (if i < 1376 then decide (2 ≤ count1374 b) else decide (1 ≤ count1376 b))))))) else (if i < 1404 then (if i < 1390 then (if i < 1383 then (if i < 1380 then (if i < 1378 then decide (2 ≤ count1376 b) else (if i < 1379 then decide (3 ≤ count1376 b) else decide (4 ≤ count1376 b))) else (if i < 1381 then decide (1 ≤ count1380 b) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (3 ≤ count1380 b)))) else (if i < 1386 then (if i < 1384 then decide (4 ≤ count1380 b) else (if i < 1385 then decide (5 ≤ count1380 b) else decide (6 ≤ count1380 b))) else (if i < 1388 then (if i < 1387 then decide (7 ≤ count1380 b) else decide (8 ≤ count1380 b)) else (if i < 1389 then decide (1 ≤ count1388 b) else decide (2 ≤ count1388 b))))) else (if i < 1397 then (if i < 1393 then (if i < 1391 then decide (3 ≤ count1388 b) else (if i < 1392 then decide (4 ≤ count1388 b) else decide (5 ≤ count1388 b))) else (if i < 1395 then (if i < 1394 then decide (6 ≤ count1388 b) else decide (7 ≤ count1388 b)) else (if i < 1396 then decide (8 ≤ count1388 b) else decide (9 ≤ count1388 b)))) else (if i < 1400 then (if i < 1398 then decide (10 ≤ count1388 b) else (if i < 1399 then decide (11 ≤ count1388 b) else decide (12 ≤ count1388 b))) else (if i < 1402 then (if i < 1401 then decide (13 ≤ count1388 b) else decide (14 ≤ count1388 b)) else (if i < 1403 then decide (15 ≤ count1388 b) else decide (1 ≤ count1403 b)))))) else (if i < 1418 then (if i < 1411 then (if i < 1407 then (if i < 1405 then decide (2 ≤ count1403 b) else (if i < 1406 then decide (3 ≤ count1403 b) else decide (4 ≤ count1403 b))) else (if i < 1409 then (if i < 1408 then decide (5 ≤ count1403 b) else decide (6 ≤ count1403 b)) else (if i < 1410 then decide (7 ≤ count1403 b) else decide (8 ≤ count1403 b)))) else (if i < 1414 then (if i < 1412 then decide (9 ≤ count1403 b) else (if i < 1413 then decide (10 ≤ count1403 b) else decide (11 ≤ count1403 b))) else (if i < 1416 then (if i < 1415 then decide (12 ≤ count1403 b) else decide (13 ≤ count1403 b)) else (if i < 1417 then decide (14 ≤ count1403 b) else decide (15 ≤ count1403 b))))) else (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (16 ≤ count1403 b) else (if i < 1420 then decide (17 ≤ count1403 b) else decide (18 ≤ count1403 b))) else (if i < 1423 then (if i < 1422 then decide (19 ≤ count1403 b) else decide (20 ≤ count1403 b)) else (if i < 1424 then decide (21 ≤ count1403 b) else decide (22 ≤ count1403 b)))) else (if i < 1428 then (if i < 1426 then decide (23 ≤ count1403 b) else (if i < 1427 then decide (24 ≤ count1403 b) else decide (25 ≤ count1403 b))) else (if i < 1430 then (if i < 1429 then decide (26 ≤ count1403 b) else decide (27 ≤ count1403 b)) else (if i < 1431 then decide (28 ≤ count1403 b) else decide (29 ≤ count1403 b)))))))) else (if i < 1487 then (if i < 1459 then (if i < 1445 then (if i < 1438 then (if i < 1435 then (if i < 1433 then decide (30 ≤ count1403 b) else (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b))) else (if i < 1436 then decide (3 ≤ count1433 b) else (if i < 1437 then decide (4 ≤ count1433 b) else decide (5 ≤ count1433 b)))) else (if i < 1441 then (if i < 1439 then decide (6 ≤ count1433 b) else (if i < 1440 then decide (7 ≤ count1433 b) else decide (8 ≤ count1433 b))) else (if i < 1443 then (if i < 1442 then decide (9 ≤ count1433 b) else decide (10 ≤ count1433 b)) else (if i < 1444 then decide (11 ≤ count1433 b) else decide (12 ≤ count1433 b))))) else (if i < 1452 then (if i < 1448 then (if i < 1446 then decide (13 ≤ count1433 b) else (if i < 1447 then decide (14 ≤ count1433 b) else decide (15 ≤ count1433 b))) else (if i < 1450 then (if i < 1449 then decide (16 ≤ count1433 b) else decide (17 ≤ count1433 b)) else (if i < 1451 then decide (18 ≤ count1433 b) else decide (19 ≤ count1433 b)))) else (if i < 1455 then (if i < 1453 then decide (20 ≤ count1433 b) else (if i < 1454 then decide (21 ≤ count1433 b) else decide (22 ≤ count1433 b))) else (if i < 1457 then (if i < 1456 then decide (23 ≤ count1433 b) else decide (24 ≤ count1433 b)) else (if i < 1458 then decide (25 ≤ count1433 b) else decide (26 ≤ count1433 b)))))) else (if i < 1473 then (if i < 1466 then (if i < 1462 then (if i < 1460 then decide (27 ≤ count1433 b) else (if i < 1461 then decide (28 ≤ count1433 b) else decide (29 ≤ count1433 b))) else (if i < 1464 then (if i < 1463 then decide (30 ≤ count1433 b) else decide (31 ≤ count1433 b)) else (if i < 1465 then decide (32 ≤ count1433 b) else decide (33 ≤ count1433 b)))) else (if i < 1469 then (if i < 1467 then decide (34 ≤ count1433 b) else (if i < 1468 then decide (35 ≤ count1433 b) else decide (36 ≤ count1433 b))) else (if i < 1471 then (if i < 1470 then decide (37 ≤ count1433 b) else decide (38 ≤ count1433 b)) else (if i < 1472 then decide (39 ≤ count1433 b) else decide (40 ≤ count1433 b))))) else (if i < 1480 then (if i < 1476 then (if i < 1474 then decide (41 ≤ count1433 b) else (if i < 1475 then decide (42 ≤ count1433 b) else decide (1 ≤ count1475 b))) else (if i < 1478 then (if i < 1477 then decide (2 ≤ count1475 b) else decide (1 ≤ count1477 b)) else (if i < 1479 then decide (2 ≤ count1477 b) else decide (3 ≤ count1477 b)))) else (if i < 1483 then (if i < 1481 then decide (1 ≤ count1480 b) else (if i < 1482 then decide (2 ≤ count1480 b) else decide (1 ≤ count1482 b))) else (if i < 1485 then (if i < 1484 then decide (2 ≤ count1482 b) else decide (1 ≤ count1484 b)) else (if i < 1486 then decide (2 ≤ count1484 b) else decide (3 ≤ count1484 b))))))) else (if i < 1514 then (if i < 1500 then (if i < 1493 then (if i < 1490 then (if i < 1488 then decide (4 ≤ count1484 b) else (if i < 1489 then decide (1 ≤ count1488 b) else decide (2 ≤ count1488 b))) else (if i < 1491 then decide (3 ≤ count1488 b) else (if i < 1492 then decide (4 ≤ count1488 b) else decide (5 ≤ count1488 b)))) else (if i < 1496 then (if i < 1494 then decide (6 ≤ count1488 b) else (if i < 1495 then decide (7 ≤ count1488 b) else decide (1 ≤ count1495 b))) else (if i < 1498 then (if i < 1497 then decide (2 ≤ count1495 b) else decide (1 ≤ count1497 b)) else (if i < 1499 then decide (2 ≤ count1497 b) else decide (3 ≤ count1497 b))))) else (if i < 1507 then (if i < 1503 then (if i < 1501 then decide (1 ≤ count1500 b) else (if i < 1502 then decide (2 ≤ count1500 b) else decide (1 ≤ count1502 b))) else (if i < 1505 then (if i < 1504 then decide (2 ≤ count1502 b) else decide (1 ≤ count1504 b)) else (if i < 1506 then decide (2 ≤ count1504 b) else decide (3 ≤ count1504 b)))) else (if i < 1510 then (if i < 1508 then decide (4 ≤ count1504 b) else (if i < 1509 then decide (1 ≤ count1508 b) else decide (2 ≤ count1508 b))) else (if i < 1512 then (if i < 1511 then decide (3 ≤ count1508 b) else decide (4 ≤ count1508 b)) else (if i < 1513 then decide (5 ≤ count1508 b) else decide (6 ≤ count1508 b)))))) else (if i < 1528 then (if i < 1521 then (if i < 1517 then (if i < 1515 then decide (7 ≤ count1508 b) else (if i < 1516 then decide (1 ≤ count1515 b) else decide (2 ≤ count1515 b))) else (if i < 1519 then (if i < 1518 then decide (3 ≤ count1515 b) else decide (4 ≤ count1515 b)) else (if i < 1520 then decide (5 ≤ count1515 b) else decide (6 ≤ count1515 b)))) else (if i < 1524 then (if i < 1522 then decide (7 ≤ count1515 b) else (if i < 1523 then decide (8 ≤ count1515 b) else decide (9 ≤ count1515 b))) else (if i < 1526 then (if i < 1525 then decide (10 ≤ count1515 b) else decide (11 ≤ count1515 b)) else (if i < 1527 then decide (12 ≤ count1515 b) else decide (13 ≤ count1515 b))))) else (if i < 1535 then (if i < 1531 then (if i < 1529 then decide (14 ≤ count1515 b) else (if i < 1530 then decide (1 ≤ count1529 b) else decide (2 ≤ count1529 b))) else (if i < 1533 then (if i < 1532 then decide (1 ≤ count1531 b) else decide (2 ≤ count1531 b)) else (if i < 1534 then decide (3 ≤ count1531 b) else decide (1 ≤ count1534 b)))) else (if i < 1538 then (if i < 1536 then decide (2 ≤ count1534 b) else (if i < 1537 then decide (1 ≤ count1536 b) else decide (2 ≤ count1536 b))) else (if i < 1540 then (if i < 1539 then decide (1 ≤ count1538 b) else decide (2 ≤ count1538 b)) else (if i < 1541 then decide (3 ≤ count1538 b) else decide (4 ≤ count1538 b))))))))) else (if i < 1652 then (if i < 1597 then (if i < 1569 then (if i < 1555 then (if i < 1548 then (if i < 1545 then (if i < 1543 then decide (1 ≤ count1542 b) else (if i < 1544 then decide (2 ≤ count1542 b) else decide (3 ≤ count1542 b))) else (if i < 1546 then decide (4 ≤ count1542 b) else (if i < 1547 then decide (5 ≤ count1542 b) else decide (6 ≤ count1542 b)))) else (if i < 1551 then (if i < 1549 then decide (7 ≤ count1542 b) else (if i < 1550 then decide (1 ≤ count1549 b) else decide (2 ≤ count1549 b))) else (if i < 1553 then (if i < 1552 then decide (1 ≤ count1551 b) else decide (2 ≤ count1551 b)) else (if i < 1554 then decide (1 ≤ count1553 b) else decide (2 ≤ count1553 b))))) else (if i < 1562 then (if i < 1558 then (if i < 1556 then decide (3 ≤ count1553 b) else (if i < 1557 then decide (4 ≤ count1553 b) else decide (1 ≤ count1557 b))) else (if i < 1560 then (if i < 1559 then decide (2 ≤ count1557 b) else decide (1 ≤ count1559 b)) else (if i < 1561 then decide (2 ≤ count1559 b) else decide (1 ≤ count1561 b)))) else (if i < 1565 then (if i < 1563 then decide (2 ≤ count1561 b) else (if i < 1564 then decide (3 ≤ count1561 b) else decide (4 ≤ count1561 b))) else (if i < 1567 then (if i < 1566 then decide (1 ≤ count1565 b) else decide (2 ≤ count1565 b)) else (if i < 1568 then decide (3 ≤ count1565 b) else decide (4 ≤ count1565 b)))))) else (if i < 1583 then (if i < 1576 then (if i < 1572 then (if i < 1570 then decide (5 ≤ count1565 b) else (if i < 1571 then decide (6 ≤ count1565 b) else decide (7 ≤ count1565 b))) else (if i < 1574 then (if i < 1573 then decide (8 ≤ count1565 b) else decide (1 ≤ count1573 b)) else (if i < 1575 then decide (2 ≤ count1573 b) else decide (3 ≤ count1573 b)))) else (if i < 1579 then (if i < 1577 then decide (4 ≤ count1573 b) else (if i < 1578 then decide (5 ≤ count1573 b) else decide (6 ≤ count1573 b))) else (if i < 1581 then (if i < 1580 then decide (7 ≤ count1573 b) else decide (8 ≤ count1573 b)) else (if i < 1582 then decide (9 ≤ count1573 b) else decide (10 ≤ count1573 b))))) else (if i < 1590 then (if i < 1586 then (if i < 1584 then decide (11 ≤ count1573 b) else (if i < 1585 then decide (12 ≤ count1573 b) else decide (13 ≤ count1573 b))) else (if i < 1588 then (if i < 1587 then decide (14 ≤ count1573 b) else decide (15 ≤ count1573 b)) else (if i < 1589 then decide (1 ≤ count1588 b) else decide (2 ≤ count1588 b)))) else (if i < 1593 then (if i < 1591 then decide (3 ≤ count1588 b) else (if i < 1592 then decide (4 ≤ count1588 b) else decide (5 ≤ count1588 b))) else (if i < 1595 then (if i < 1594 then decide (6 ≤ count1588 b) else decide (7 ≤ count1588 b)) else (if i < 1596 then decide (8 ≤ count1588 b) else decide (9 ≤ count1588 b))))))) else (if i < 1624 then (if i < 1610 then (if i < 1603 then (if i < 1600 then (if i < 1598 then decide (10 ≤ count1588 b) else (if i < 1599 then decide (11 ≤ count1588 b) else decide (12 ≤ count1588 b))) else (if i < 1601 then decide (13 ≤ count1588 b) else (if i < 1602 then decide (14 ≤ count1588 b) else decide (15 ≤ count1588 b)))) else (if i < 1606 then (if i < 1604 then decide (16 ≤ count1588 b) else (if i < 1605 then decide (17 ≤ count1588 b) else decide (18 ≤ count1588 b))) else (if i < 1608 then (if i < 1607 then decide (19 ≤ count1588 b) else decide (1 ≤ count1607 b)) else (if i < 1609 then decide (2 ≤ count1607 b) else decide (1 ≤ count1609 b))))) else (if i < 1617 then (if i < 1613 then (if i < 1611 then decide (2 ≤ count1609 b) else (if i < 1612 then decide (3 ≤ count1609 b) else decide (1 ≤ count1612 b))) else (if i < 1615 then (if i < 1614 then decide (2 ≤ count1612 b) else decide (1 ≤ count1614 b)) else (if i < 1616 then decide (2 ≤ count1614 b) else decide (1 ≤ count1616 b)))) else (if i < 1620 then (if i < 1618 then decide (2 ≤ count1616 b) else (if i < 1619 then decide (3 ≤ count1616 b) else decide (4 ≤ count1616 b))) else (if i < 1622 then (if i < 1621 then decide (1 ≤ count1620 b) else decide (2 ≤ count1620 b)) else (if i < 1623 then decide (3 ≤ count1620 b) else decide (4 ≤ count1620 b)))))) else (if i < 1638 then (if i < 1631 then (if i < 1627 then (if i < 1625 then decide (5 ≤ count1620 b) else (if i < 1626 then decide (6 ≤ count1620 b) else decide (7 ≤ count1620 b))) else (if i < 1629 then (if i < 1628 then decide (1 ≤ count1627 b) else decide (2 ≤ count1627 b)) else (if i < 1630 then decide (1 ≤ count1629 b) else decide (2 ≤ count1629 b)))) else (if i < 1634 then (if i < 1632 then decide (1 ≤ count1631 b) else (if i < 1633 then decide (2 ≤ count1631 b) else decide (3 ≤ count1631 b))) else (if i < 1636 then (if i < 1635 then decide (4 ≤ count1631 b) else decide (1 ≤ count1635 b)) else (if i < 1637 then decide (2 ≤ count1635 b) else decide (1 ≤ count1637 b))))) else (if i < 1645 then (if i < 1641 then (if i < 1639 then decide (2 ≤ count1637 b) else (if i < 1640 then decide (1 ≤ count1639 b) else decide (2 ≤ count1639 b))) else (if i < 1643 then (if i < 1642 then decide (3 ≤ count1639 b) else decide (4 ≤ count1639 b)) else (if i < 1644 then decide (1 ≤ count1643 b) else decide (2 ≤ count1643 b)))) else (if i < 1648 then (if i < 1646 then decide (3 ≤ count1643 b) else (if i < 1647 then decide (4 ≤ count1643 b) else decide (5 ≤ count1643 b))) else (if i < 1650 then (if i < 1649 then decide (6 ≤ count1643 b) else decide (7 ≤ count1643 b)) else (if i < 1651 then decide (8 ≤ count1643 b) else decide (1 ≤ count1651 b)))))))) else (if i < 1707 then (if i < 1679 then (if i < 1665 then (if i < 1658 then (if i < 1655 then (if i < 1653 then decide (2 ≤ count1651 b) else (if i < 1654 then decide (3 ≤ count1651 b) else decide (4 ≤ count1651 b))) else (if i < 1656 then decide (5 ≤ count1651 b) else (if i < 1657 then decide (6 ≤ count1651 b) else decide (7 ≤ count1651 b)))) else (if i < 1661 then (if i < 1659 then decide (8 ≤ count1651 b) else (if i < 1660 then decide (9 ≤ count1651 b) else decide (10 ≤ count1651 b))) else (if i < 1663 then (if i < 1662 then decide (11 ≤ count1651 b) else decide (12 ≤ count1651 b)) else (if i < 1664 then decide (13 ≤ count1651 b) else decide (14 ≤ count1651 b))))) else (if i < 1672 then (if i < 1668 then (if i < 1666 then decide (15 ≤ count1651 b) else (if i < 1667 then decide (1 ≤ count1666 b) else decide (2 ≤ count1666 b))) else (if i < 1670 then (if i < 1669 then decide (1 ≤ count1668 b) else decide (2 ≤ count1668 b)) else (if i < 1671 then decide (3 ≤ count1668 b) else decide (1 ≤ count1671 b)))) else (if i < 1675 then (if i < 1673 then decide (2 ≤ count1671 b) else (if i < 1674 then decide (1 ≤ count1673 b) else decide (2 ≤ count1673 b))) else (if i < 1677 then (if i < 1676 then decide (1 ≤ count1675 b) else decide (2 ≤ count1675 b)) else (if i < 1678 then decide (3 ≤ count1675 b) else decide (4 ≤ count1675 b)))))) else (if i < 1693 then (if i < 1686 then (if i < 1682 then (if i < 1680 then decide (1 ≤ count1679 b) else (if i < 1681 then decide (2 ≤ count1679 b) else decide (3 ≤ count1679 b))) else (if i < 1684 then (if i < 1683 then decide (4 ≤ count1679 b) else decide (5 ≤ count1679 b)) else (if i < 1685 then decide (6 ≤ count1679 b) else decide (7 ≤ count1679 b)))) else (if i < 1689 then (if i < 1687 then decide (1 ≤ count1686 b) else (if i < 1688 then decide (2 ≤ count1686 b) else decide (1 ≤ count1688 b))) else (if i < 1691 then (if i < 1690 then decide (2 ≤ count1688 b) else decide (1 ≤ count1690 b)) else (if i < 1692 then decide (2 ≤ count1690 b) else decide (3 ≤ count1690 b))))) else (if i < 1700 then (if i < 1696 then (if i < 1694 then decide (4 ≤ count1690 b) else (if i < 1695 then decide (1 ≤ count1694 b) else decide (2 ≤ count1694 b))) else (if i < 1698 then (if i < 1697 then decide (1 ≤ count1696 b) else decide (2 ≤ count1696 b)) else (if i < 1699 then decide (1 ≤ count1698 b) else decide (2 ≤ count1698 b)))) else (if i < 1703 then (if i < 1701 then decide (3 ≤ count1698 b) else (if i < 1702 then decide (4 ≤ count1698 b) else decide (1 ≤ count1702 b))) else (if i < 1705 then (if i < 1704 then decide (2 ≤ count1702 b) else decide (3 ≤ count1702 b)) else (if i < 1706 then decide (4 ≤ count1702 b) else decide (5 ≤ count1702 b))))))) else (if i < 1735 then (if i < 1721 then (if i < 1714 then (if i < 1710 then (if i < 1708 then decide (6 ≤ count1702 b) else (if i < 1709 then decide (7 ≤ count1702 b) else decide (8 ≤ count1702 b))) else (if i < 1712 then (if i < 1711 then decide (1 ≤ count1710 b) else decide (2 ≤ count1710 b)) else (if i < 1713 then decide (3 ≤ count1710 b) else decide (4 ≤ count1710 b)))) else (if i < 1717 then (if i < 1715 then decide (5 ≤ count1710 b) else (if i < 1716 then decide (6 ≤ count1710 b) else decide (7 ≤ count1710 b))) else (if i < 1719 then (if i < 1718 then decide (8 ≤ count1710 b) else decide (9 ≤ count1710 b)) else (if i < 1720 then decide (10 ≤ count1710 b) else decide (11 ≤ count1710 b))))) else (if i < 1728 then (if i < 1724 then (if i < 1722 then decide (12 ≤ count1710 b) else (if i < 1723 then decide (13 ≤ count1710 b) else decide (14 ≤ count1710 b))) else (if i < 1726 then (if i < 1725 then decide (15 ≤ count1710 b) else decide (1 ≤ count1725 b)) else (if i < 1727 then decide (2 ≤ count1725 b) else decide (3 ≤ count1725 b)))) else (if i < 1731 then (if i < 1729 then decide (4 ≤ count1725 b) else (if i < 1730 then decide (5 ≤ count1725 b) else decide (6 ≤ count1725 b))) else (if i < 1733 then (if i < 1732 then decide (7 ≤ count1725 b) else decide (8 ≤ count1725 b)) else (if i < 1734 then decide (9 ≤ count1725 b) else decide (10 ≤ count1725 b)))))) else (if i < 1749 then (if i < 1742 then (if i < 1738 then (if i < 1736 then decide (11 ≤ count1725 b) else (if i < 1737 then decide (12 ≤ count1725 b) else decide (13 ≤ count1725 b))) else (if i < 1740 then (if i < 1739 then decide (14 ≤ count1725 b) else decide (15 ≤ count1725 b)) else (if i < 1741 then decide (16 ≤ count1725 b) else decide (17 ≤ count1725 b)))) else (if i < 1745 then (if i < 1743 then decide (18 ≤ count1725 b) else (if i < 1744 then decide (19 ≤ count1725 b) else decide (1 ≤ count1744 b))) else (if i < 1747 then (if i < 1746 then decide (2 ≤ count1744 b) else decide (3 ≤ count1744 b)) else (if i < 1748 then decide (4 ≤ count1744 b) else decide (5 ≤ count1744 b))))) else (if i < 1756 then (if i < 1752 then (if i < 1750 then decide (6 ≤ count1744 b) else (if i < 1751 then decide (7 ≤ count1744 b) else decide (8 ≤ count1744 b))) else (if i < 1754 then (if i < 1753 then decide (9 ≤ count1744 b) else decide (10 ≤ count1744 b)) else (if i < 1755 then decide (11 ≤ count1744 b) else decide (12 ≤ count1744 b)))) else (if i < 1759 then (if i < 1757 then decide (13 ≤ count1744 b) else (if i < 1758 then decide (14 ≤ count1744 b) else decide (15 ≤ count1744 b))) else (if i < 1761 then (if i < 1760 then decide (16 ≤ count1744 b) else decide (17 ≤ count1744 b)) else (if i < 1762 then decide (18 ≤ count1744 b) else decide (19 ≤ count1744 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (4 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (10 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (12 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (14 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (66 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (67 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (68 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (69 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (71 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (74 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (75 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (77 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (79 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (80 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (81 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (83 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (84 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (88 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (92 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (94 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (95 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (130 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (131 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (132 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (133 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (135 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (138 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (139 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (141 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (143 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (144 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (145 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (147 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (148 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (152 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (156 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (158 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (159 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (192 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (193 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (198 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (199 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (200 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (201 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (203 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (204 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (206 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (210 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (212 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (213 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (214 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (215 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (217 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (218 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (219 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (221 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (266 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (282 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (284 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (286 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (320 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (321 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (324 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (326 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (328 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (331 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (332 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (334 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (338 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (341 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (342 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (343 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (344 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (345 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (346 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (347 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (349 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (384 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (385 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (386 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (388 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (389 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (390 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (392 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (394 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (395 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (396 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (398 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (402 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (405 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (406 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (407 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (408 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (409 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (411 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (413 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (415 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (448 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (449 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (450 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (451 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (453 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (455 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (456 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (459 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (460 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (461 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (462 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (463 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (464 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (465 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (466 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (467 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (468 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (472 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (474 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (475 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (476 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (478 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (479 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (4 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (12 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (67 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (68 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (71 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (74 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (75 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (77 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (81 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (83 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (92 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (141 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (143 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (145 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (147 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (156 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (198 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (203 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (210 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (212 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (213 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (215 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (219 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (286 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (324 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (326 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (334 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (343 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (344 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (347 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (388 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (389 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (390 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (392 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (394 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (395 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (396 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (398 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (402 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (405 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (408 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (411 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (415 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (448 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (449 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (450 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (455 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (456 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (459 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (461 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (463 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (465 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (466 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (467 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (474 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (476 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (478 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (479 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (2 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
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
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value298 (q : Snake 81) : valuation q 298 = decide (2 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value300 (q : Snake 81) : valuation q 300 = decide (2 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value318 (q : Snake 81) : valuation q 318 = decide (2 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value326 (q : Snake 81) : valuation q 326 = decide (2 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value332 (q : Snake 81) : valuation q 332 = decide (2 ≤ count331 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value336 (q : Snake 81) : valuation q 336 = decide (2 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value340 (q : Snake 81) : valuation q 340 = decide (2 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
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
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value364 (q : Snake 81) : valuation q 364 = decide (2 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value370 (q : Snake 81) : valuation q 370 = decide (2 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value382 (q : Snake 81) : valuation q 382 = decide (2 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value384 (q : Snake 81) : valuation q 384 = decide (2 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value398 (q : Snake 81) : valuation q 398 = decide (2 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value414 (q : Snake 81) : valuation q 414 = decide (2 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value430 (q : Snake 81) : valuation q 430 = decide (2 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value444 (q : Snake 81) : valuation q 444 = decide (2 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value446 (q : Snake 81) : valuation q 446 = decide (2 ≤ count445 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value456 (q : Snake 81) : valuation q 456 = decide (2 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value458 (q : Snake 81) : valuation q 458 = decide (2 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value464 (q : Snake 81) : valuation q 464 = decide (2 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value471 (q : Snake 81) : valuation q 471 = decide (1 ≤ count471 (baseVal q)) := rfl
theorem value472 (q : Snake 81) : valuation q 472 = decide (2 ≤ count471 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value474 (q : Snake 81) : valuation q 474 = decide (2 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value476 (q : Snake 81) : valuation q 476 = decide (2 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value478 (q : Snake 81) : valuation q 478 = decide (2 ≤ count477 (baseVal q)) := rfl
theorem value480 (q : Snake 81) : valuation q 480 = decide (2 ≤ count479 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (1 ≤ count1475 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (2 ≤ count1475 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (1 ≤ count1477 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (2 ≤ count1477 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (3 ≤ count1477 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (1 ≤ count1480 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (2 ≤ count1480 (baseVal q)) := rfl
theorem value1482 (q : Snake 81) : valuation q 1482 = decide (1 ≤ count1482 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (2 ≤ count1482 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (1 ≤ count1484 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (2 ≤ count1484 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (3 ≤ count1484 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (4 ≤ count1484 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (1 ≤ count1488 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (2 ≤ count1488 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (3 ≤ count1488 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (4 ≤ count1488 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (5 ≤ count1488 (baseVal q)) := rfl
theorem value1495 (q : Snake 81) : valuation q 1495 = decide (1 ≤ count1495 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (2 ≤ count1495 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (1 ≤ count1497 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (2 ≤ count1497 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (3 ≤ count1497 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (1 ≤ count1500 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (2 ≤ count1500 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (1 ≤ count1502 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (2 ≤ count1502 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (1 ≤ count1504 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (2 ≤ count1504 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (3 ≤ count1504 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (4 ≤ count1504 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (1 ≤ count1508 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (2 ≤ count1508 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (3 ≤ count1508 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (4 ≤ count1508 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (5 ≤ count1508 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (1 ≤ count1515 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (2 ≤ count1515 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (3 ≤ count1515 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (4 ≤ count1515 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (5 ≤ count1515 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (6 ≤ count1515 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (7 ≤ count1515 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (8 ≤ count1515 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (9 ≤ count1515 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (1 ≤ count1529 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (2 ≤ count1529 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (1 ≤ count1531 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (2 ≤ count1531 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (3 ≤ count1531 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (1 ≤ count1534 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (2 ≤ count1534 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (1 ≤ count1536 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (2 ≤ count1536 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (1 ≤ count1538 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (2 ≤ count1538 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (3 ≤ count1538 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (4 ≤ count1538 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (1 ≤ count1542 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (2 ≤ count1542 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (3 ≤ count1542 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (4 ≤ count1542 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (5 ≤ count1542 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (1 ≤ count1549 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (2 ≤ count1549 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (2 ≤ count1551 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (1 ≤ count1553 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (2 ≤ count1553 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (3 ≤ count1553 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (4 ≤ count1553 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (1 ≤ count1557 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (2 ≤ count1557 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (1 ≤ count1559 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (1 ≤ count1561 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (2 ≤ count1561 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (3 ≤ count1561 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (1 ≤ count1565 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (2 ≤ count1565 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (3 ≤ count1565 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (4 ≤ count1565 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (5 ≤ count1565 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (6 ≤ count1565 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (1 ≤ count1573 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (2 ≤ count1573 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (3 ≤ count1573 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (4 ≤ count1573 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (5 ≤ count1573 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (6 ≤ count1573 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (7 ≤ count1573 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (8 ≤ count1573 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (4 ≤ count1588 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (5 ≤ count1588 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (6 ≤ count1588 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (7 ≤ count1588 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (8 ≤ count1588 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (9 ≤ count1588 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (10 ≤ count1588 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (11 ≤ count1588 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (12 ≤ count1588 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (13 ≤ count1588 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (1 ≤ count1607 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (2 ≤ count1607 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (1 ≤ count1609 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (2 ≤ count1609 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (3 ≤ count1609 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (1 ≤ count1612 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (2 ≤ count1612 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (1 ≤ count1614 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (2 ≤ count1614 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (1 ≤ count1616 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (2 ≤ count1616 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (3 ≤ count1616 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (4 ≤ count1616 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (1 ≤ count1620 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (2 ≤ count1620 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (3 ≤ count1620 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (4 ≤ count1620 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (5 ≤ count1620 (baseVal q)) := rfl
theorem value1625 (q : Snake 81) : valuation q 1625 = decide (6 ≤ count1620 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (1 ≤ count1627 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (2 ≤ count1627 (baseVal q)) := rfl
theorem value1629 (q : Snake 81) : valuation q 1629 = decide (1 ≤ count1629 (baseVal q)) := rfl
theorem value1630 (q : Snake 81) : valuation q 1630 = decide (2 ≤ count1629 (baseVal q)) := rfl
theorem value1631 (q : Snake 81) : valuation q 1631 = decide (1 ≤ count1631 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (2 ≤ count1631 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (3 ≤ count1631 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (4 ≤ count1631 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (1 ≤ count1635 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (2 ≤ count1635 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (1 ≤ count1637 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (2 ≤ count1637 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (1 ≤ count1639 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (2 ≤ count1639 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (3 ≤ count1639 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (4 ≤ count1639 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (1 ≤ count1643 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (2 ≤ count1643 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (3 ≤ count1643 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (4 ≤ count1643 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (5 ≤ count1643 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (6 ≤ count1643 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (7 ≤ count1643 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (1 ≤ count1651 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (2 ≤ count1651 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (3 ≤ count1651 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (4 ≤ count1651 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (5 ≤ count1651 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (6 ≤ count1651 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (7 ≤ count1651 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (8 ≤ count1651 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (9 ≤ count1651 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (10 ≤ count1651 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (1 ≤ count1666 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (2 ≤ count1666 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (1 ≤ count1668 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (2 ≤ count1668 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (3 ≤ count1668 (baseVal q)) := rfl
theorem value1671 (q : Snake 81) : valuation q 1671 = decide (1 ≤ count1671 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (2 ≤ count1671 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (1 ≤ count1673 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (2 ≤ count1673 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (1 ≤ count1675 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (2 ≤ count1675 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (3 ≤ count1675 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (4 ≤ count1675 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (1 ≤ count1679 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (2 ≤ count1679 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (3 ≤ count1679 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (4 ≤ count1679 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (5 ≤ count1679 (baseVal q)) := rfl
theorem value1684 (q : Snake 81) : valuation q 1684 = decide (6 ≤ count1679 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (1 ≤ count1686 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (2 ≤ count1686 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (1 ≤ count1688 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (2 ≤ count1688 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (1 ≤ count1690 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (2 ≤ count1690 (baseVal q)) := rfl
theorem value1692 (q : Snake 81) : valuation q 1692 = decide (3 ≤ count1690 (baseVal q)) := rfl
theorem value1693 (q : Snake 81) : valuation q 1693 = decide (4 ≤ count1690 (baseVal q)) := rfl
theorem value1694 (q : Snake 81) : valuation q 1694 = decide (1 ≤ count1694 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (2 ≤ count1694 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (1 ≤ count1696 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (2 ≤ count1696 (baseVal q)) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (1 ≤ count1698 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (2 ≤ count1698 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (3 ≤ count1698 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (4 ≤ count1698 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (1 ≤ count1702 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (2 ≤ count1702 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (3 ≤ count1702 (baseVal q)) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (4 ≤ count1702 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (5 ≤ count1702 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (6 ≤ count1702 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (7 ≤ count1702 (baseVal q)) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (3 ≤ count1710 (baseVal q)) := rfl
theorem value1713 (q : Snake 81) : valuation q 1713 = decide (4 ≤ count1710 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (5 ≤ count1710 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (6 ≤ count1710 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (7 ≤ count1710 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (8 ≤ count1710 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (9 ≤ count1710 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (10 ≤ count1710 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (11 ≤ count1710 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (6 ≤ count1725 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (7 ≤ count1725 (baseVal q)) := rfl
theorem value1732 (q : Snake 81) : valuation q 1732 = decide (8 ≤ count1725 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (9 ≤ count1725 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (10 ≤ count1725 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (11 ≤ count1725 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (12 ≤ count1725 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (13 ≤ count1725 (baseVal q)) := rfl
theorem value1738 (q : Snake 81) : valuation q 1738 = decide (14 ≤ count1725 (baseVal q)) := rfl
theorem value1739 (q : Snake 81) : valuation q 1739 = decide (15 ≤ count1725 (baseVal q)) := rfl
theorem value1762 (q : Snake 81) : valuation q 1762 = decide (19 ≤ count1744 (baseVal q)) := rfl
theorem meaningNeg120 (b : Nat → Bool) : literal (valuationOf b) (-120) = decide (1 ≤ countLit b [-120]) := by
  change literal b (-120) = decide (1 ≤ countLit b [-120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-120) <;> decide
theorem meaningNeg118 (b : Nat → Bool) : literal (valuationOf b) (-118) = decide (1 ≤ countLit b [-118]) := by
  change literal b (-118) = decide (1 ≤ countLit b [-118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-118) <;> decide
theorem meaningNeg116 (b : Nat → Bool) : literal (valuationOf b) (-116) = decide (1 ≤ countLit b [-116]) := by
  change literal b (-116) = decide (1 ≤ countLit b [-116])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-116) <;> decide
theorem meaningNeg115 (b : Nat → Bool) : literal (valuationOf b) (-115) = decide (1 ≤ countLit b [-115]) := by
  change literal b (-115) = decide (1 ≤ countLit b [-115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-115) <;> decide
theorem meaningNeg113 (b : Nat → Bool) : literal (valuationOf b) (-113) = decide (1 ≤ countLit b [-113]) := by
  change literal b (-113) = decide (1 ≤ countLit b [-113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-113) <;> decide
theorem meaningNeg112 (b : Nat → Bool) : literal (valuationOf b) (-112) = decide (1 ≤ countLit b [-112]) := by
  change literal b (-112) = decide (1 ≤ countLit b [-112])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-112) <;> decide
theorem meaningNeg110 (b : Nat → Bool) : literal (valuationOf b) (-110) = decide (1 ≤ countLit b [-110]) := by
  change literal b (-110) = decide (1 ≤ countLit b [-110])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-110) <;> decide
theorem meaningNeg107 (b : Nat → Bool) : literal (valuationOf b) (-107) = decide (1 ≤ countLit b [-107]) := by
  change literal b (-107) = decide (1 ≤ countLit b [-107])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-107) <;> decide
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
theorem meaningNeg63 (b : Nat → Bool) : literal (valuationOf b) (-63) = decide (1 ≤ countLit b [-63]) := by
  change literal b (-63) = decide (1 ≤ countLit b [-63])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-63) <;> decide
theorem meaningNeg58 (b : Nat → Bool) : literal (valuationOf b) (-58) = decide (1 ≤ countLit b [-58]) := by
  change literal b (-58) = decide (1 ≤ countLit b [-58])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-58) <;> decide
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
theorem meaningNeg31 (b : Nat → Bool) : literal (valuationOf b) (-31) = decide (1 ≤ countLit b [-31]) := by
  change literal b (-31) = decide (1 ≤ countLit b [-31])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-31) <;> decide
theorem meaningNeg28 (b : Nat → Bool) : literal (valuationOf b) (-28) = decide (1 ≤ countLit b [-28]) := by
  change literal b (-28) = decide (1 ≤ countLit b [-28])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-28) <;> decide
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
theorem meaningNeg18 (b : Nat → Bool) : literal (valuationOf b) (-18) = decide (1 ≤ countLit b [-18]) := by
  change literal b (-18) = decide (1 ≤ countLit b [-18])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-18) <;> decide
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
theorem meaning123 (b : Nat → Bool) : literal (valuationOf b) (123) = decide (1 ≤ countLit b [123]) := by
  change literal b (123) = decide (1 ≤ countLit b [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (123) <;> decide
theorem meaning126 (b : Nat → Bool) : literal (valuationOf b) (126) = decide (1 ≤ countLit b [126]) := by
  change literal b (126) = decide (1 ≤ countLit b [126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (126) <;> decide
theorem meaning128 (b : Nat → Bool) : literal (valuationOf b) (128) = decide (1 ≤ countLit b [128]) := by
  change literal b (128) = decide (1 ≤ countLit b [128])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (128) <;> decide
theorem meaning130 (b : Nat → Bool) : literal (valuationOf b) (130) = decide (1 ≤ countLit b [130]) := by
  change literal b (130) = decide (1 ≤ countLit b [130])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (130) <;> decide
theorem meaning132 (b : Nat → Bool) : literal (valuationOf b) (132) = decide (1 ≤ countLit b [132]) := by
  change literal b (132) = decide (1 ≤ countLit b [132])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (132) <;> decide
theorem meaning135 (b : Nat → Bool) : literal (valuationOf b) (135) = decide (1 ≤ countLit b [135]) := by
  change literal b (135) = decide (1 ≤ countLit b [135])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (135) <;> decide
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
theorem meaning145 (b : Nat → Bool) : literal (valuationOf b) (145) = decide (1 ≤ countLit b [145]) := by
  change literal b (145) = decide (1 ≤ countLit b [145])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (145) <;> decide
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
theorem meaning152 (b : Nat → Bool) : literal (valuationOf b) (152) = decide (1 ≤ countLit b [152]) := by
  change literal b (152) = decide (1 ≤ countLit b [152])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (152) <;> decide
theorem meaning154 (b : Nat → Bool) : literal (valuationOf b) (154) = decide (1 ≤ countLit b [154]) := by
  change literal b (154) = decide (1 ≤ countLit b [154])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (154) <;> decide
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
theorem meaning159 (b : Nat → Bool) : literal (valuationOf b) (159) = decide (1 ≤ countLit b [159]) := by
  change literal b (159) = decide (1 ≤ countLit b [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (159) <;> decide
theorem meaning162 (b : Nat → Bool) : literal (valuationOf b) (162) = decide (1 ≤ countLit b [162]) := by
  change literal b (162) = decide (1 ≤ countLit b [162])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (162) <;> decide
theorem meaning164 (b : Nat → Bool) : literal (valuationOf b) (164) = decide (1 ≤ countLit b [164]) := by
  change literal b (164) = decide (1 ≤ countLit b [164])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (164) <;> decide
theorem meaning165 (b : Nat → Bool) : literal (valuationOf b) (165) = decide (1 ≤ countLit b [165]) := by
  change literal b (165) = decide (1 ≤ countLit b [165])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (165) <;> decide
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
theorem meaning179 (b : Nat → Bool) : literal (valuationOf b) (179) = decide (1 ≤ countLit b [179]) := by
  change literal b (179) = decide (1 ≤ countLit b [179])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (179) <;> decide
theorem meaning182 (b : Nat → Bool) : literal (valuationOf b) (182) = decide (1 ≤ countLit b [182]) := by
  change literal b (182) = decide (1 ≤ countLit b [182])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (182) <;> decide
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
theorem meaning193 (b : Nat → Bool) : literal (valuationOf b) (193) = decide (1 ≤ countLit b [193]) := by
  change literal b (193) = decide (1 ≤ countLit b [193])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (193) <;> decide
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
theorem meaning208 (b : Nat → Bool) : literal (valuationOf b) (208) = decide (1 ≤ countLit b [208]) := by
  change literal b (208) = decide (1 ≤ countLit b [208])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (208) <;> decide
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
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
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) (219) = decide (1 ≤ countLit b [219]) := by
  change literal b (219) = decide (1 ≤ countLit b [219])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (219) <;> decide
theorem meaning220 (b : Nat → Bool) : literal (valuationOf b) (220) = decide (1 ≤ countLit b [220]) := by
  change literal b (220) = decide (1 ≤ countLit b [220])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (220) <;> decide
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) (223) = decide (1 ≤ countLit b [223]) := by
  change literal b (223) = decide (1 ≤ countLit b [223])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (223) <;> decide
theorem meaning224 (b : Nat → Bool) : literal (valuationOf b) (224) = decide (1 ≤ countLit b [224]) := by
  change literal b (224) = decide (1 ≤ countLit b [224])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (224) <;> decide
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) (228) = decide (1 ≤ countLit b [228]) := by
  change literal b (228) = decide (1 ≤ countLit b [228])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (228) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) (233) = decide (1 ≤ countLit b [233]) := by
  change literal b (233) = decide (1 ≤ countLit b [233])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (233) <;> decide
theorem meaning234 (b : Nat → Bool) : literal (valuationOf b) (234) = decide (1 ≤ countLit b [234]) := by
  change literal b (234) = decide (1 ≤ countLit b [234])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (234) <;> decide
theorem meaning236 (b : Nat → Bool) : literal (valuationOf b) (236) = decide (1 ≤ countLit b [236]) := by
  change literal b (236) = decide (1 ≤ countLit b [236])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (236) <;> decide
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) (237) = decide (1 ≤ countLit b [237]) := by
  change literal b (237) = decide (1 ≤ countLit b [237])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (237) <;> decide
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) (239) = decide (1 ≤ countLit b [239]) := by
  change literal b (239) = decide (1 ≤ countLit b [239])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (239) <;> decide
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) (241) = decide (1 ≤ countLit b [241]) := by
  change literal b (241) = decide (1 ≤ countLit b [241])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (241) <;> decide
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) 252 = decide (2 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
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
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning298 (b : Nat → Bool) : literal (valuationOf b) 298 = decide (2 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning300 (b : Nat → Bool) : literal (valuationOf b) 300 = decide (2 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning318 (b : Nat → Bool) : literal (valuationOf b) 318 = decide (2 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning326 (b : Nat → Bool) : literal (valuationOf b) 326 = decide (2 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning332 (b : Nat → Bool) : literal (valuationOf b) 332 = decide (2 ≤ count331 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning336 (b : Nat → Bool) : literal (valuationOf b) 336 = decide (2 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning338 (b : Nat → Bool) : literal (valuationOf b) 338 = decide (2 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning340 (b : Nat → Bool) : literal (valuationOf b) 340 = decide (2 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
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
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning364 (b : Nat → Bool) : literal (valuationOf b) 364 = decide (2 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning370 (b : Nat → Bool) : literal (valuationOf b) 370 = decide (2 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning382 (b : Nat → Bool) : literal (valuationOf b) 382 = decide (2 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning384 (b : Nat → Bool) : literal (valuationOf b) 384 = decide (2 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning398 (b : Nat → Bool) : literal (valuationOf b) 398 = decide (2 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning414 (b : Nat → Bool) : literal (valuationOf b) 414 = decide (2 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning430 (b : Nat → Bool) : literal (valuationOf b) 430 = decide (2 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning444 (b : Nat → Bool) : literal (valuationOf b) 444 = decide (2 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning446 (b : Nat → Bool) : literal (valuationOf b) 446 = decide (2 ≤ count445 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning456 (b : Nat → Bool) : literal (valuationOf b) 456 = decide (2 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning458 (b : Nat → Bool) : literal (valuationOf b) 458 = decide (2 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning464 (b : Nat → Bool) : literal (valuationOf b) 464 = decide (2 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning471 (b : Nat → Bool) : literal (valuationOf b) 471 = decide (1 ≤ count471 b) := rfl
theorem meaning472 (b : Nat → Bool) : literal (valuationOf b) 472 = decide (2 ≤ count471 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning474 (b : Nat → Bool) : literal (valuationOf b) 474 = decide (2 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning476 (b : Nat → Bool) : literal (valuationOf b) 476 = decide (2 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning478 (b : Nat → Bool) : literal (valuationOf b) 478 = decide (2 ≤ count477 b) := rfl
theorem meaning480 (b : Nat → Bool) : literal (valuationOf b) 480 = decide (2 ≤ count479 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (1 ≤ count1475 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (2 ≤ count1475 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (1 ≤ count1477 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (2 ≤ count1477 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (3 ≤ count1477 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (1 ≤ count1480 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (2 ≤ count1480 b) := rfl
theorem meaning1482 (b : Nat → Bool) : literal (valuationOf b) 1482 = decide (1 ≤ count1482 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (2 ≤ count1482 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (1 ≤ count1484 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (2 ≤ count1484 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (3 ≤ count1484 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (4 ≤ count1484 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (1 ≤ count1488 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (2 ≤ count1488 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (3 ≤ count1488 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (4 ≤ count1488 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (5 ≤ count1488 b) := rfl
theorem meaning1495 (b : Nat → Bool) : literal (valuationOf b) 1495 = decide (1 ≤ count1495 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (2 ≤ count1495 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (1 ≤ count1497 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (2 ≤ count1497 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (3 ≤ count1497 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (1 ≤ count1500 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (2 ≤ count1500 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (1 ≤ count1502 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (2 ≤ count1502 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (1 ≤ count1504 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (2 ≤ count1504 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (3 ≤ count1504 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (4 ≤ count1504 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (1 ≤ count1508 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (2 ≤ count1508 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (3 ≤ count1508 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (4 ≤ count1508 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (5 ≤ count1508 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (1 ≤ count1515 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (2 ≤ count1515 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (3 ≤ count1515 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (4 ≤ count1515 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (5 ≤ count1515 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (6 ≤ count1515 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (7 ≤ count1515 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (8 ≤ count1515 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (9 ≤ count1515 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (1 ≤ count1529 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (2 ≤ count1529 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (1 ≤ count1531 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (2 ≤ count1531 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (3 ≤ count1531 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (1 ≤ count1534 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (2 ≤ count1534 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (1 ≤ count1536 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (2 ≤ count1536 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (1 ≤ count1538 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (2 ≤ count1538 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (3 ≤ count1538 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (4 ≤ count1538 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (1 ≤ count1542 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (2 ≤ count1542 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (3 ≤ count1542 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (4 ≤ count1542 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (5 ≤ count1542 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (1 ≤ count1549 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (2 ≤ count1549 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (2 ≤ count1551 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (1 ≤ count1553 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (2 ≤ count1553 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (3 ≤ count1553 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (4 ≤ count1553 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (1 ≤ count1557 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (2 ≤ count1557 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (1 ≤ count1559 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (1 ≤ count1561 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (2 ≤ count1561 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (3 ≤ count1561 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (1 ≤ count1565 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (2 ≤ count1565 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (3 ≤ count1565 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (4 ≤ count1565 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (5 ≤ count1565 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (6 ≤ count1565 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (1 ≤ count1573 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (2 ≤ count1573 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (3 ≤ count1573 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (4 ≤ count1573 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (5 ≤ count1573 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (6 ≤ count1573 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (7 ≤ count1573 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (8 ≤ count1573 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (4 ≤ count1588 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (5 ≤ count1588 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (6 ≤ count1588 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (7 ≤ count1588 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (8 ≤ count1588 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (9 ≤ count1588 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (10 ≤ count1588 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (11 ≤ count1588 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (12 ≤ count1588 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (13 ≤ count1588 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (1 ≤ count1607 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (2 ≤ count1607 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (1 ≤ count1609 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (2 ≤ count1609 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (3 ≤ count1609 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (1 ≤ count1612 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (2 ≤ count1612 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (1 ≤ count1614 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (2 ≤ count1614 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (1 ≤ count1616 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (2 ≤ count1616 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (3 ≤ count1616 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (4 ≤ count1616 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (1 ≤ count1620 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (2 ≤ count1620 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (3 ≤ count1620 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (4 ≤ count1620 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (5 ≤ count1620 b) := rfl
theorem meaning1625 (b : Nat → Bool) : literal (valuationOf b) 1625 = decide (6 ≤ count1620 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (1 ≤ count1627 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (2 ≤ count1627 b) := rfl
theorem meaning1629 (b : Nat → Bool) : literal (valuationOf b) 1629 = decide (1 ≤ count1629 b) := rfl
theorem meaning1630 (b : Nat → Bool) : literal (valuationOf b) 1630 = decide (2 ≤ count1629 b) := rfl
theorem meaning1631 (b : Nat → Bool) : literal (valuationOf b) 1631 = decide (1 ≤ count1631 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (2 ≤ count1631 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (3 ≤ count1631 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (4 ≤ count1631 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (1 ≤ count1635 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (2 ≤ count1635 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (1 ≤ count1637 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (2 ≤ count1637 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (1 ≤ count1639 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (2 ≤ count1639 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (3 ≤ count1639 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (4 ≤ count1639 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (1 ≤ count1643 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (2 ≤ count1643 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (3 ≤ count1643 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (4 ≤ count1643 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (5 ≤ count1643 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (6 ≤ count1643 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (7 ≤ count1643 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (1 ≤ count1651 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (2 ≤ count1651 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (3 ≤ count1651 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (4 ≤ count1651 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (5 ≤ count1651 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (6 ≤ count1651 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (7 ≤ count1651 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (8 ≤ count1651 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (9 ≤ count1651 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (10 ≤ count1651 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (1 ≤ count1666 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (2 ≤ count1666 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (1 ≤ count1668 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (2 ≤ count1668 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (3 ≤ count1668 b) := rfl
theorem meaning1671 (b : Nat → Bool) : literal (valuationOf b) 1671 = decide (1 ≤ count1671 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (2 ≤ count1671 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (1 ≤ count1673 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (2 ≤ count1673 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (1 ≤ count1675 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (2 ≤ count1675 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (3 ≤ count1675 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (4 ≤ count1675 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (1 ≤ count1679 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (2 ≤ count1679 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (3 ≤ count1679 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (4 ≤ count1679 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (5 ≤ count1679 b) := rfl
theorem meaning1684 (b : Nat → Bool) : literal (valuationOf b) 1684 = decide (6 ≤ count1679 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (1 ≤ count1686 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (2 ≤ count1686 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (1 ≤ count1688 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (2 ≤ count1688 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (1 ≤ count1690 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (2 ≤ count1690 b) := rfl
theorem meaning1692 (b : Nat → Bool) : literal (valuationOf b) 1692 = decide (3 ≤ count1690 b) := rfl
theorem meaning1693 (b : Nat → Bool) : literal (valuationOf b) 1693 = decide (4 ≤ count1690 b) := rfl
theorem meaning1694 (b : Nat → Bool) : literal (valuationOf b) 1694 = decide (1 ≤ count1694 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (2 ≤ count1694 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (1 ≤ count1696 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (2 ≤ count1696 b) := rfl
theorem meaning1698 (b : Nat → Bool) : literal (valuationOf b) 1698 = decide (1 ≤ count1698 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (2 ≤ count1698 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (3 ≤ count1698 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (4 ≤ count1698 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (1 ≤ count1702 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (2 ≤ count1702 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (3 ≤ count1702 b) := rfl
theorem meaning1705 (b : Nat → Bool) : literal (valuationOf b) 1705 = decide (4 ≤ count1702 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (5 ≤ count1702 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (6 ≤ count1702 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (7 ≤ count1702 b) := rfl
theorem meaning1712 (b : Nat → Bool) : literal (valuationOf b) 1712 = decide (3 ≤ count1710 b) := rfl
theorem meaning1713 (b : Nat → Bool) : literal (valuationOf b) 1713 = decide (4 ≤ count1710 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (5 ≤ count1710 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (6 ≤ count1710 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (7 ≤ count1710 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (8 ≤ count1710 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (9 ≤ count1710 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (10 ≤ count1710 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (11 ≤ count1710 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (6 ≤ count1725 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (7 ≤ count1725 b) := rfl
theorem meaning1732 (b : Nat → Bool) : literal (valuationOf b) 1732 = decide (8 ≤ count1725 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (9 ≤ count1725 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (10 ≤ count1725 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (11 ≤ count1725 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (12 ≤ count1725 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (13 ≤ count1725 b) := rfl
theorem meaning1738 (b : Nat → Bool) : literal (valuationOf b) 1738 = decide (14 ≤ count1725 b) := rfl
theorem meaning1739 (b : Nat → Bool) : literal (valuationOf b) 1739 = decide (15 ≤ count1725 b) := rfl
theorem meaning1762 (b : Nat → Bool) : literal (valuationOf b) 1762 = decide (19 ≤ count1744 b) := rfl
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
end Snake9.Regrowth.E112019
