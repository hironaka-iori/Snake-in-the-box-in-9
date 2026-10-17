import E112090Data
namespace Snake9.Regrowth.E112090
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 109 then (if i < 54 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (99 : Vertex)) else decide (InPath q (106 : Vertex)))) else (if i < 4 then decide (InPath q (107 : Vertex)) else (if i < 5 then decide (InPath q (117 : Vertex)) else decide (InPath q (118 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (119 : Vertex)) else (if i < 8 then decide (InPath q (120 : Vertex)) else decide (InPath q (121 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (122 : Vertex)) else decide (InPath q (125 : Vertex))) else (if i < 12 then decide (InPath q (129 : Vertex)) else decide (InPath q (130 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (131 : Vertex)) else (if i < 15 then decide (InPath q (133 : Vertex)) else decide (InPath q (135 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (137 : Vertex)) else decide (InPath q (139 : Vertex))) else (if i < 19 then decide (InPath q (140 : Vertex)) else decide (InPath q (141 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (143 : Vertex)) else (if i < 22 then decide (InPath q (144 : Vertex)) else decide (InPath q (145 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (146 : Vertex)) else decide (InPath q (148 : Vertex))) else (if i < 26 then decide (InPath q (150 : Vertex)) else decide (InPath q (156 : Vertex))))))) else (if i < 40 then (if i < 33 then (if i < 30 then (if i < 28 then decide (InPath q (158 : Vertex)) else (if i < 29 then decide (InPath q (159 : Vertex)) else decide (InPath q (194 : Vertex)))) else (if i < 31 then decide (InPath q (195 : Vertex)) else (if i < 32 then decide (InPath q (196 : Vertex)) else decide (InPath q (198 : Vertex))))) else (if i < 36 then (if i < 34 then decide (InPath q (205 : Vertex)) else (if i < 35 then decide (InPath q (209 : Vertex)) else decide (InPath q (213 : Vertex)))) else (if i < 38 then (if i < 37 then decide (InPath q (214 : Vertex)) else decide (InPath q (215 : Vertex))) else (if i < 39 then decide (InPath q (221 : Vertex)) else decide (InPath q (227 : Vertex)))))) else (if i < 47 then (if i < 43 then (if i < 41 then decide (InPath q (229 : Vertex)) else (if i < 42 then decide (InPath q (231 : Vertex)) else decide (InPath q (233 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (237 : Vertex)) else decide (InPath q (257 : Vertex))) else (if i < 46 then decide (InPath q (259 : Vertex)) else decide (InPath q (261 : Vertex))))) else (if i < 50 then (if i < 48 then decide (InPath q (263 : Vertex)) else (if i < 49 then decide (InPath q (265 : Vertex)) else decide (InPath q (267 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (268 : Vertex)) else decide (InPath q (269 : Vertex))) else (if i < 53 then decide (InPath q (271 : Vertex)) else decide (InPath q (272 : Vertex)))))))) else (if i < 81 then (if i < 67 then (if i < 60 then (if i < 57 then (if i < 55 then decide (InPath q (273 : Vertex)) else (if i < 56 then decide (InPath q (274 : Vertex)) else decide (InPath q (276 : Vertex)))) else (if i < 58 then decide (InPath q (284 : Vertex)) else (if i < 59 then decide (InPath q (286 : Vertex)) else decide (InPath q (287 : Vertex))))) else (if i < 63 then (if i < 61 then decide (InPath q (320 : Vertex)) else (if i < 62 then decide (InPath q (322 : Vertex)) else decide (InPath q (323 : Vertex)))) else (if i < 65 then (if i < 64 then decide (InPath q (324 : Vertex)) else decide (InPath q (326 : Vertex))) else (if i < 66 then decide (InPath q (330 : Vertex)) else decide (InPath q (331 : Vertex)))))) else (if i < 74 then (if i < 70 then (if i < 68 then decide (InPath q (332 : Vertex)) else (if i < 69 then decide (InPath q (333 : Vertex)) else decide (InPath q (337 : Vertex)))) else (if i < 72 then (if i < 71 then decide (InPath q (341 : Vertex)) else decide (InPath q (342 : Vertex))) else (if i < 73 then decide (InPath q (343 : Vertex)) else decide (InPath q (344 : Vertex))))) else (if i < 77 then (if i < 75 then decide (InPath q (345 : Vertex)) else (if i < 76 then decide (InPath q (346 : Vertex)) else decide (InPath q (349 : Vertex)))) else (if i < 79 then (if i < 78 then decide (InPath q (384 : Vertex)) else decide (InPath q (386 : Vertex))) else (if i < 80 then decide (InPath q (387 : Vertex)) else decide (InPath q (388 : Vertex))))))) else (if i < 95 then (if i < 88 then (if i < 84 then (if i < 82 then decide (InPath q (390 : Vertex)) else (if i < 83 then decide (InPath q (394 : Vertex)) else decide (InPath q (395 : Vertex)))) else (if i < 86 then (if i < 85 then decide (InPath q (396 : Vertex)) else decide (InPath q (397 : Vertex))) else (if i < 87 then decide (InPath q (401 : Vertex)) else decide (InPath q (405 : Vertex))))) else (if i < 91 then (if i < 89 then decide (InPath q (406 : Vertex)) else (if i < 90 then decide (InPath q (407 : Vertex)) else decide (InPath q (408 : Vertex)))) else (if i < 93 then (if i < 92 then decide (InPath q (409 : Vertex)) else decide (InPath q (410 : Vertex))) else (if i < 94 then decide (InPath q (413 : Vertex)) else decide (InPath q (482 : Vertex)))))) else (if i < 102 then (if i < 98 then (if i < 96 then decide (InPath q (483 : Vertex)) else (if i < 97 then decide (InPath q (484 : Vertex)) else decide (InPath q (486 : Vertex)))) else (if i < 100 then (if i < 99 then decide (InPath q (490 : Vertex)) else decide (InPath q (491 : Vertex))) else (if i < 101 then decide (InPath q (492 : Vertex)) else decide (InPath q (493 : Vertex))))) else (if i < 105 then (if i < 103 then decide (InPath q (497 : Vertex)) else (if i < 104 then decide (InPath q (501 : Vertex)) else decide (InPath q (502 : Vertex)))) else (if i < 107 then (if i < 106 then decide (InPath q (503 : Vertex)) else decide (InPath q (504 : Vertex))) else (if i < 108 then decide (InPath q (505 : Vertex)) else decide (InPath q (506 : Vertex))))))))) else (if i < 164 then (if i < 136 then (if i < 122 then (if i < 115 then (if i < 112 then (if i < 110 then decide (InPath q (509 : Vertex)) else (if i < 111 then decide (BallClauseLogic.Endpoint q (99 : Vertex)) else decide (BallClauseLogic.Endpoint q (106 : Vertex)))) else (if i < 113 then decide (BallClauseLogic.Endpoint q (107 : Vertex)) else (if i < 114 then decide (BallClauseLogic.Endpoint q (117 : Vertex)) else decide (BallClauseLogic.Endpoint q (118 : Vertex))))) else (if i < 118 then (if i < 116 then decide (BallClauseLogic.Endpoint q (119 : Vertex)) else (if i < 117 then decide (BallClauseLogic.Endpoint q (120 : Vertex)) else decide (BallClauseLogic.Endpoint q (121 : Vertex)))) else (if i < 120 then (if i < 119 then decide (BallClauseLogic.Endpoint q (122 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex))) else (if i < 121 then decide (BallClauseLogic.Endpoint q (129 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex)))))) else (if i < 129 then (if i < 125 then (if i < 123 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (135 : Vertex)))) else (if i < 127 then (if i < 126 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex))) else (if i < 128 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (141 : Vertex))))) else (if i < 132 then (if i < 130 then decide (BallClauseLogic.Endpoint q (143 : Vertex)) else (if i < 131 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (145 : Vertex)))) else (if i < 134 then (if i < 133 then decide (BallClauseLogic.Endpoint q (146 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))) else (if i < 135 then decide (BallClauseLogic.Endpoint q (150 : Vertex)) else decide (BallClauseLogic.Endpoint q (156 : Vertex))))))) else (if i < 150 then (if i < 143 then (if i < 139 then (if i < 137 then decide (BallClauseLogic.Endpoint q (158 : Vertex)) else (if i < 138 then decide (BallClauseLogic.Endpoint q (159 : Vertex)) else decide (BallClauseLogic.Endpoint q (194 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (195 : Vertex)) else decide (BallClauseLogic.Endpoint q (196 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex))))) else (if i < 146 then (if i < 144 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else (if i < 145 then decide (BallClauseLogic.Endpoint q (213 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex)))) else (if i < 148 then (if i < 147 then decide (BallClauseLogic.Endpoint q (215 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex))) else (if i < 149 then decide (BallClauseLogic.Endpoint q (227 : Vertex)) else decide (BallClauseLogic.Endpoint q (229 : Vertex)))))) else (if i < 157 then (if i < 153 then (if i < 151 then decide (BallClauseLogic.Endpoint q (231 : Vertex)) else (if i < 152 then decide (BallClauseLogic.Endpoint q (233 : Vertex)) else decide (BallClauseLogic.Endpoint q (237 : Vertex)))) else (if i < 155 then (if i < 154 then decide (BallClauseLogic.Endpoint q (257 : Vertex)) else decide (BallClauseLogic.Endpoint q (259 : Vertex))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (263 : Vertex))))) else (if i < 160 then (if i < 158 then decide (BallClauseLogic.Endpoint q (265 : Vertex)) else (if i < 159 then decide (BallClauseLogic.Endpoint q (267 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex)))) else (if i < 162 then (if i < 161 then decide (BallClauseLogic.Endpoint q (269 : Vertex)) else decide (BallClauseLogic.Endpoint q (271 : Vertex))) else (if i < 163 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (273 : Vertex)))))))) else (if i < 191 then (if i < 177 then (if i < 170 then (if i < 167 then (if i < 165 then decide (BallClauseLogic.Endpoint q (274 : Vertex)) else (if i < 166 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (284 : Vertex)))) else (if i < 168 then decide (BallClauseLogic.Endpoint q (286 : Vertex)) else (if i < 169 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex))))) else (if i < 173 then (if i < 171 then decide (BallClauseLogic.Endpoint q (322 : Vertex)) else (if i < 172 then decide (BallClauseLogic.Endpoint q (323 : Vertex)) else decide (BallClauseLogic.Endpoint q (324 : Vertex)))) else (if i < 175 then (if i < 174 then decide (BallClauseLogic.Endpoint q (326 : Vertex)) else decide (BallClauseLogic.Endpoint q (330 : Vertex))) else (if i < 176 then decide (BallClauseLogic.Endpoint q (331 : Vertex)) else decide (BallClauseLogic.Endpoint q (332 : Vertex)))))) else (if i < 184 then (if i < 180 then (if i < 178 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else (if i < 179 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (341 : Vertex)))) else (if i < 182 then (if i < 181 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (343 : Vertex))) else (if i < 183 then decide (BallClauseLogic.Endpoint q (344 : Vertex)) else decide (BallClauseLogic.Endpoint q (345 : Vertex))))) else (if i < 187 then (if i < 185 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else (if i < 186 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex)))) else (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (386 : Vertex)) else decide (BallClauseLogic.Endpoint q (387 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (388 : Vertex)) else decide (BallClauseLogic.Endpoint q (390 : Vertex))))))) else (if i < 205 then (if i < 198 then (if i < 194 then (if i < 192 then decide (BallClauseLogic.Endpoint q (394 : Vertex)) else (if i < 193 then decide (BallClauseLogic.Endpoint q (395 : Vertex)) else decide (BallClauseLogic.Endpoint q (396 : Vertex)))) else (if i < 196 then (if i < 195 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else decide (BallClauseLogic.Endpoint q (401 : Vertex))) else (if i < 197 then decide (BallClauseLogic.Endpoint q (405 : Vertex)) else decide (BallClauseLogic.Endpoint q (406 : Vertex))))) else (if i < 201 then (if i < 199 then decide (BallClauseLogic.Endpoint q (407 : Vertex)) else (if i < 200 then decide (BallClauseLogic.Endpoint q (408 : Vertex)) else decide (BallClauseLogic.Endpoint q (409 : Vertex)))) else (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (410 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (482 : Vertex)) else decide (BallClauseLogic.Endpoint q (483 : Vertex)))))) else (if i < 212 then (if i < 208 then (if i < 206 then decide (BallClauseLogic.Endpoint q (484 : Vertex)) else (if i < 207 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (490 : Vertex)))) else (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (491 : Vertex)) else decide (BallClauseLogic.Endpoint q (492 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (497 : Vertex))))) else (if i < 215 then (if i < 213 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else (if i < 214 then decide (BallClauseLogic.Endpoint q (502 : Vertex)) else decide (BallClauseLogic.Endpoint q (503 : Vertex)))) else (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (504 : Vertex)) else decide (BallClauseLogic.Endpoint q (505 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count219 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count221 (b : Nat → Bool) : Nat := countLit b [110, 111, 112]
def count223 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count225 (b : Nat → Bool) : Nat := countLit b [113, 115, 116]
def count227 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 115, 116]
def count229 (b : Nat → Bool) : Nat := countLit b [118, 119]
def count231 (b : Nat → Bool) : Nat := countLit b [117, 118, 119]
def count233 (b : Nat → Bool) : Nat := countLit b [120, 121]
def count235 (b : Nat → Bool) : Nat := countLit b [122, 123]
def count237 (b : Nat → Bool) : Nat := countLit b [120, 121, 122, 123]
def count239 (b : Nat → Bool) : Nat := countLit b [117, 118, 119, 120, 121, 122, 123]
def count241 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123]
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
def count269 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
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
def count323 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164]
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
def count431 (b : Nat → Bool) : Nat := countLit b [110, 111, 112, 113, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count433 (b : Nat → Bool) : Nat := countLit b [2, 6]
def count435 (b : Nat → Bool) : Nat := countLit b [1, 2, 6]
def count438 (b : Nat → Bool) : Nat := countLit b [10, 11]
def count440 (b : Nat → Bool) : Nat := countLit b [7, 10, 11]
def count443 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11]
def count449 (b : Nat → Bool) : Nat := countLit b [15, 17]
def count451 (b : Nat → Bool) : Nat := countLit b [12, 15, 17]
def count454 (b : Nat → Bool) : Nat := countLit b [19, 21]
def count456 (b : Nat → Bool) : Nat := countLit b [25, 26]
def count458 (b : Nat → Bool) : Nat := countLit b [19, 21, 25, 26]
def count462 (b : Nat → Bool) : Nat := countLit b [12, 15, 17, 19, 21, 25, 26]
def count469 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11, 12, 15, 17, 19, 21, 25, 26]
def count482 (b : Nat → Bool) : Nat := countLit b [30, 32]
def count484 (b : Nat → Bool) : Nat := countLit b [28, 30, 32]
def count487 (b : Nat → Bool) : Nat := countLit b [34, 37]
def count489 (b : Nat → Bool) : Nat := countLit b [38, 41]
def count491 (b : Nat → Bool) : Nat := countLit b [34, 37, 38, 41]
def count495 (b : Nat → Bool) : Nat := countLit b [28, 30, 32, 34, 37, 38, 41]
def count502 (b : Nat → Bool) : Nat := countLit b [44, 47]
def count504 (b : Nat → Bool) : Nat := countLit b [43, 44, 47]
def count507 (b : Nat → Bool) : Nat := countLit b [49, 51]
def count509 (b : Nat → Bool) : Nat := countLit b [53, 57]
def count511 (b : Nat → Bool) : Nat := countLit b [49, 51, 53, 57]
def count515 (b : Nat → Bool) : Nat := countLit b [43, 44, 47, 49, 51, 53, 57]
def count522 (b : Nat → Bool) : Nat := countLit b [28, 30, 32, 34, 37, 38, 41, 43, 44, 47, 49, 51, 53, 57]
def count536 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11, 12, 15, 17, 19, 21, 25, 26, 28, 30, 32, 34, 37, 38, 41, 43, 44, 47, 49, 51, 53, 57]
def count563 (b : Nat → Bool) : Nat := countLit b [60, 62]
def count565 (b : Nat → Bool) : Nat := countLit b [59, 60, 62]
def count568 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count570 (b : Nat → Bool) : Nat := countLit b [64, 65, 67]
def count573 (b : Nat → Bool) : Nat := countLit b [59, 60, 62, 64, 65, 67]
def count579 (b : Nat → Bool) : Nat := countLit b [72, 73]
def count581 (b : Nat → Bool) : Nat := countLit b [69, 72, 73]
def count584 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count586 (b : Nat → Bool) : Nat := countLit b [79, 81]
def count588 (b : Nat → Bool) : Nat := countLit b [76, 77, 79, 81]
def count592 (b : Nat → Bool) : Nat := countLit b [69, 72, 73, 76, 77, 79, 81]
def count599 (b : Nat → Bool) : Nat := countLit b [59, 60, 62, 64, 65, 67, 69, 72, 73, 76, 77, 79, 81]
def count612 (b : Nat → Bool) : Nat := countLit b [84, 86]
def count614 (b : Nat → Bool) : Nat := countLit b [82, 84, 86]
def count617 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count619 (b : Nat → Bool) : Nat := countLit b [93, 95]
def count621 (b : Nat → Bool) : Nat := countLit b [89, 90, 93, 95]
def count625 (b : Nat → Bool) : Nat := countLit b [82, 84, 86, 89, 90, 93, 95]
def count632 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count634 (b : Nat → Bool) : Nat := countLit b [97, 98, 100]
def count637 (b : Nat → Bool) : Nat := countLit b [102, 105]
def count639 (b : Nat → Bool) : Nat := countLit b [106, 109]
def count641 (b : Nat → Bool) : Nat := countLit b [102, 105, 106, 109]
def count645 (b : Nat → Bool) : Nat := countLit b [97, 98, 100, 102, 105, 106, 109]
def count652 (b : Nat → Bool) : Nat := countLit b [82, 84, 86, 89, 90, 93, 95, 97, 98, 100, 102, 105, 106, 109]
def count666 (b : Nat → Bool) : Nat := countLit b [59, 60, 62, 64, 65, 67, 69, 72, 73, 76, 77, 79, 81, 82, 84, 86, 89, 90, 93, 95, 97, 98, 100, 102, 105, 106, 109]
def count693 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 7, 10, 11, 12, 15, 17, 19, 21, 25, 26, 28, 30, 32, 34, 37, 38, 41, 43, 44, 47, 49, 51, 53, 57, 59, 60, 62, 64, 65, 67, 69, 72, 73, 76, 77, 79, 81, 82, 84, 86, 89, 90, 93, 95, 97, 98, 100, 102, 105, 106, 109]
def count735 (b : Nat → Bool) : Nat := countLit b [-2, -6]
def count737 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6]
def count740 (b : Nat → Bool) : Nat := countLit b [-10, -11]
def count742 (b : Nat → Bool) : Nat := countLit b [-7, -10, -11]
def count745 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11]
def count751 (b : Nat → Bool) : Nat := countLit b [-15, -17]
def count753 (b : Nat → Bool) : Nat := countLit b [-12, -15, -17]
def count756 (b : Nat → Bool) : Nat := countLit b [-19, -21]
def count758 (b : Nat → Bool) : Nat := countLit b [-25, -26]
def count760 (b : Nat → Bool) : Nat := countLit b [-19, -21, -25, -26]
def count764 (b : Nat → Bool) : Nat := countLit b [-12, -15, -17, -19, -21, -25, -26]
def count771 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11, -12, -15, -17, -19, -21, -25, -26]
def count784 (b : Nat → Bool) : Nat := countLit b [-30, -32]
def count786 (b : Nat → Bool) : Nat := countLit b [-28, -30, -32]
def count789 (b : Nat → Bool) : Nat := countLit b [-34, -37]
def count791 (b : Nat → Bool) : Nat := countLit b [-38, -41]
def count793 (b : Nat → Bool) : Nat := countLit b [-34, -37, -38, -41]
def count797 (b : Nat → Bool) : Nat := countLit b [-28, -30, -32, -34, -37, -38, -41]
def count804 (b : Nat → Bool) : Nat := countLit b [-44, -47]
def count806 (b : Nat → Bool) : Nat := countLit b [-43, -44, -47]
def count809 (b : Nat → Bool) : Nat := countLit b [-49, -51]
def count811 (b : Nat → Bool) : Nat := countLit b [-53, -57]
def count813 (b : Nat → Bool) : Nat := countLit b [-49, -51, -53, -57]
def count817 (b : Nat → Bool) : Nat := countLit b [-43, -44, -47, -49, -51, -53, -57]
def count824 (b : Nat → Bool) : Nat := countLit b [-28, -30, -32, -34, -37, -38, -41, -43, -44, -47, -49, -51, -53, -57]
def count838 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11, -12, -15, -17, -19, -21, -25, -26, -28, -30, -32, -34, -37, -38, -41, -43, -44, -47, -49, -51, -53, -57]
def count852 (b : Nat → Bool) : Nat := countLit b [-60, -62]
def count854 (b : Nat → Bool) : Nat := countLit b [-59, -60, -62]
def count857 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count859 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67]
def count862 (b : Nat → Bool) : Nat := countLit b [-59, -60, -62, -64, -65, -67]
def count868 (b : Nat → Bool) : Nat := countLit b [-72, -73]
def count870 (b : Nat → Bool) : Nat := countLit b [-69, -72, -73]
def count873 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count875 (b : Nat → Bool) : Nat := countLit b [-79, -81]
def count877 (b : Nat → Bool) : Nat := countLit b [-76, -77, -79, -81]
def count881 (b : Nat → Bool) : Nat := countLit b [-69, -72, -73, -76, -77, -79, -81]
def count888 (b : Nat → Bool) : Nat := countLit b [-59, -60, -62, -64, -65, -67, -69, -72, -73, -76, -77, -79, -81]
def count901 (b : Nat → Bool) : Nat := countLit b [-84, -86]
def count903 (b : Nat → Bool) : Nat := countLit b [-82, -84, -86]
def count906 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count908 (b : Nat → Bool) : Nat := countLit b [-93, -95]
def count910 (b : Nat → Bool) : Nat := countLit b [-89, -90, -93, -95]
def count914 (b : Nat → Bool) : Nat := countLit b [-82, -84, -86, -89, -90, -93, -95]
def count921 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count923 (b : Nat → Bool) : Nat := countLit b [-97, -98, -100]
def count926 (b : Nat → Bool) : Nat := countLit b [-102, -105]
def count928 (b : Nat → Bool) : Nat := countLit b [-106, -109]
def count930 (b : Nat → Bool) : Nat := countLit b [-102, -105, -106, -109]
def count934 (b : Nat → Bool) : Nat := countLit b [-97, -98, -100, -102, -105, -106, -109]
def count941 (b : Nat → Bool) : Nat := countLit b [-82, -84, -86, -89, -90, -93, -95, -97, -98, -100, -102, -105, -106, -109]
def count955 (b : Nat → Bool) : Nat := countLit b [-59, -60, -62, -64, -65, -67, -69, -72, -73, -76, -77, -79, -81, -82, -84, -86, -89, -90, -93, -95, -97, -98, -100, -102, -105, -106, -109]
def count969 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -7, -10, -11, -12, -15, -17, -19, -21, -25, -26, -28, -30, -32, -34, -37, -38, -41, -43, -44, -47, -49, -51, -53, -57, -59, -60, -62, -64, -65, -67, -69, -72, -73, -76, -77, -79, -81, -82, -84, -86, -89, -90, -93, -95, -97, -98, -100, -102, -105, -106, -109]
def count983 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count985 (b : Nat → Bool) : Nat := countLit b [3, 4, 5]
def count988 (b : Nat → Bool) : Nat := countLit b [9, 13]
def count990 (b : Nat → Bool) : Nat := countLit b [8, 9, 13]
def count993 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 13]
def count999 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count1001 (b : Nat → Bool) : Nat := countLit b [14, 16, 18]
def count1004 (b : Nat → Bool) : Nat := countLit b [20, 22]
def count1006 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count1008 (b : Nat → Bool) : Nat := countLit b [20, 22, 23, 24]
def count1012 (b : Nat → Bool) : Nat := countLit b [14, 16, 18, 20, 22, 23, 24]
def count1019 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 13, 14, 16, 18, 20, 22, 23, 24]
def count1032 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count1034 (b : Nat → Bool) : Nat := countLit b [27, 29, 31]
def count1037 (b : Nat → Bool) : Nat := countLit b [33, 35]
def count1039 (b : Nat → Bool) : Nat := countLit b [36, 39]
def count1041 (b : Nat → Bool) : Nat := countLit b [33, 35, 36, 39]
def count1045 (b : Nat → Bool) : Nat := countLit b [27, 29, 31, 33, 35, 36, 39]
def count1052 (b : Nat → Bool) : Nat := countLit b [42, 45]
def count1054 (b : Nat → Bool) : Nat := countLit b [40, 42, 45]
def count1057 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count1059 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count1061 (b : Nat → Bool) : Nat := countLit b [46, 48, 50, 52]
def count1065 (b : Nat → Bool) : Nat := countLit b [40, 42, 45, 46, 48, 50, 52]
def count1072 (b : Nat → Bool) : Nat := countLit b [27, 29, 31, 33, 35, 36, 39, 40, 42, 45, 46, 48, 50, 52]
def count1086 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 13, 14, 16, 18, 20, 22, 23, 24, 27, 29, 31, 33, 35, 36, 39, 40, 42, 45, 46, 48, 50, 52]
def count1113 (b : Nat → Bool) : Nat := countLit b [55, 56]
def count1115 (b : Nat → Bool) : Nat := countLit b [54, 55, 56]
def count1118 (b : Nat → Bool) : Nat := countLit b [58, 61]
def count1120 (b : Nat → Bool) : Nat := countLit b [63, 66]
def count1122 (b : Nat → Bool) : Nat := countLit b [58, 61, 63, 66]
def count1126 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 58, 61, 63, 66]
def count1133 (b : Nat → Bool) : Nat := countLit b [70, 71]
def count1135 (b : Nat → Bool) : Nat := countLit b [68, 70, 71]
def count1138 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count1140 (b : Nat → Bool) : Nat := countLit b [78, 80]
def count1142 (b : Nat → Bool) : Nat := countLit b [74, 75, 78, 80]
def count1146 (b : Nat → Bool) : Nat := countLit b [68, 70, 71, 74, 75, 78, 80]
def count1153 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 58, 61, 63, 66, 68, 70, 71, 74, 75, 78, 80]
def count1167 (b : Nat → Bool) : Nat := countLit b [85, 87]
def count1169 (b : Nat → Bool) : Nat := countLit b [83, 85, 87]
def count1172 (b : Nat → Bool) : Nat := countLit b [88, 91]
def count1174 (b : Nat → Bool) : Nat := countLit b [92, 94]
def count1176 (b : Nat → Bool) : Nat := countLit b [88, 91, 92, 94]
def count1180 (b : Nat → Bool) : Nat := countLit b [83, 85, 87, 88, 91, 92, 94]
def count1187 (b : Nat → Bool) : Nat := countLit b [99, 101]
def count1189 (b : Nat → Bool) : Nat := countLit b [96, 99, 101]
def count1192 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count1194 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count1196 (b : Nat → Bool) : Nat := countLit b [103, 104, 107, 108]
def count1200 (b : Nat → Bool) : Nat := countLit b [96, 99, 101, 103, 104, 107, 108]
def count1207 (b : Nat → Bool) : Nat := countLit b [83, 85, 87, 88, 91, 92, 94, 96, 99, 101, 103, 104, 107, 108]
def count1221 (b : Nat → Bool) : Nat := countLit b [54, 55, 56, 58, 61, 63, 66, 68, 70, 71, 74, 75, 78, 80, 83, 85, 87, 88, 91, 92, 94, 96, 99, 101, 103, 104, 107, 108]
def count1249 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 8, 9, 13, 14, 16, 18, 20, 22, 23, 24, 27, 29, 31, 33, 35, 36, 39, 40, 42, 45, 46, 48, 50, 52, 54, 55, 56, 58, 61, 63, 66, 68, 70, 71, 74, 75, 78, 80, 83, 85, 87, 88, 91, 92, 94, 96, 99, 101, 103, 104, 107, 108]
def count1291 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1293 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5]
def count1296 (b : Nat → Bool) : Nat := countLit b [-9, -13]
def count1298 (b : Nat → Bool) : Nat := countLit b [-8, -9, -13]
def count1301 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -13]
def count1307 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1309 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18]
def count1312 (b : Nat → Bool) : Nat := countLit b [-20, -22]
def count1314 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count1316 (b : Nat → Bool) : Nat := countLit b [-20, -22, -23, -24]
def count1320 (b : Nat → Bool) : Nat := countLit b [-14, -16, -18, -20, -22, -23, -24]
def count1327 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]
def count1340 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count1342 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31]
def count1345 (b : Nat → Bool) : Nat := countLit b [-33, -35]
def count1347 (b : Nat → Bool) : Nat := countLit b [-36, -39]
def count1349 (b : Nat → Bool) : Nat := countLit b [-33, -35, -36, -39]
def count1353 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31, -33, -35, -36, -39]
def count1360 (b : Nat → Bool) : Nat := countLit b [-42, -45]
def count1362 (b : Nat → Bool) : Nat := countLit b [-40, -42, -45]
def count1365 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count1367 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count1369 (b : Nat → Bool) : Nat := countLit b [-46, -48, -50, -52]
def count1373 (b : Nat → Bool) : Nat := countLit b [-40, -42, -45, -46, -48, -50, -52]
def count1380 (b : Nat → Bool) : Nat := countLit b [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]
def count1394 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]
def count1409 (b : Nat → Bool) : Nat := countLit b [-55, -56]
def count1411 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56]
def count1414 (b : Nat → Bool) : Nat := countLit b [-58, -61]
def count1416 (b : Nat → Bool) : Nat := countLit b [-63, -66]
def count1418 (b : Nat → Bool) : Nat := countLit b [-58, -61, -63, -66]
def count1422 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -58, -61, -63, -66]
def count1429 (b : Nat → Bool) : Nat := countLit b [-70, -71]
def count1431 (b : Nat → Bool) : Nat := countLit b [-68, -70, -71]
def count1434 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count1436 (b : Nat → Bool) : Nat := countLit b [-78, -80]
def count1438 (b : Nat → Bool) : Nat := countLit b [-74, -75, -78, -80]
def count1442 (b : Nat → Bool) : Nat := countLit b [-68, -70, -71, -74, -75, -78, -80]
def count1449 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80]
def count1463 (b : Nat → Bool) : Nat := countLit b [-85, -87]
def count1465 (b : Nat → Bool) : Nat := countLit b [-83, -85, -87]
def count1468 (b : Nat → Bool) : Nat := countLit b [-88, -91]
def count1470 (b : Nat → Bool) : Nat := countLit b [-92, -94]
def count1472 (b : Nat → Bool) : Nat := countLit b [-88, -91, -92, -94]
def count1476 (b : Nat → Bool) : Nat := countLit b [-83, -85, -87, -88, -91, -92, -94]
def count1483 (b : Nat → Bool) : Nat := countLit b [-99, -101]
def count1485 (b : Nat → Bool) : Nat := countLit b [-96, -99, -101]
def count1488 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1490 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1492 (b : Nat → Bool) : Nat := countLit b [-103, -104, -107, -108]
def count1496 (b : Nat → Bool) : Nat := countLit b [-96, -99, -101, -103, -104, -107, -108]
def count1503 (b : Nat → Bool) : Nat := countLit b [-83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]
def count1517 (b : Nat → Bool) : Nat := countLit b [-54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]
def count1532 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24, -27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52, -54, -55, -56, -58, -61, -63, -66, -68, -70, -71, -74, -75, -78, -80, -83, -85, -87, -88, -91, -92, -94, -96, -99, -101, -103, -104, -107, -108]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 773 then (if i < 386 then (if i < 193 then (if i < 96 then (if i < 48 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 22 then b 21 else (if i < 23 then b 22 else b 23))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then b 24 else (if i < 26 then b 25 else b 26)) else (if i < 28 then b 27 else (if i < 29 then b 28 else b 29))) else (if i < 33 then (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)))) else (if i < 42 then (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41))) else (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)))))) else (if i < 72 then (if i < 60 then (if i < 54 then (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 52 then b 51 else (if i < 53 then b 52 else b 53))) else (if i < 57 then (if i < 55 then b 54 else (if i < 56 then b 55 else b 56)) else (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)))) else (if i < 66 then (if i < 63 then (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)) else (if i < 64 then b 63 else (if i < 65 then b 64 else b 65))) else (if i < 69 then (if i < 67 then b 66 else (if i < 68 then b 67 else b 68)) else (if i < 70 then b 69 else (if i < 71 then b 70 else b 71))))) else (if i < 84 then (if i < 78 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 76 then b 75 else (if i < 77 then b 76 else b 77))) else (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83)))) else (if i < 90 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 88 then b 87 else (if i < 89 then b 88 else b 89))) else (if i < 93 then (if i < 91 then b 90 else (if i < 92 then b 91 else b 92)) else (if i < 94 then b 93 else (if i < 95 then b 94 else b 95))))))) else (if i < 144 then (if i < 120 then (if i < 108 then (if i < 102 then (if i < 99 then (if i < 97 then b 96 else (if i < 98 then b 97 else b 98)) else (if i < 100 then b 99 else (if i < 101 then b 100 else b 101))) else (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 106 then b 105 else (if i < 107 then b 106 else b 107)))) else (if i < 114 then (if i < 111 then (if i < 109 then b 108 else (if i < 110 then b 109 else b 110)) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113))) else (if i < 117 then (if i < 115 then b 114 else (if i < 116 then b 115 else b 116)) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119))))) else (if i < 132 then (if i < 126 then (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 124 then b 123 else (if i < 125 then b 124 else b 125))) else (if i < 129 then (if i < 127 then b 126 else (if i < 128 then b 127 else b 128)) else (if i < 130 then b 129 else (if i < 131 then b 130 else b 131)))) else (if i < 138 then (if i < 135 then (if i < 133 then b 132 else (if i < 134 then b 133 else b 134)) else (if i < 136 then b 135 else (if i < 137 then b 136 else b 137))) else (if i < 141 then (if i < 139 then b 138 else (if i < 140 then b 139 else b 140)) else (if i < 142 then b 141 else (if i < 143 then b 142 else b 143)))))) else (if i < 168 then (if i < 156 then (if i < 150 then (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 148 then b 147 else (if i < 149 then b 148 else b 149))) else (if i < 153 then (if i < 151 then b 150 else (if i < 152 then b 151 else b 152)) else (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)))) else (if i < 162 then (if i < 159 then (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)) else (if i < 160 then b 159 else (if i < 161 then b 160 else b 161))) else (if i < 165 then (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)) else (if i < 166 then b 165 else (if i < 167 then b 166 else b 167))))) else (if i < 180 then (if i < 174 then (if i < 171 then (if i < 169 then b 168 else (if i < 170 then b 169 else b 170)) else (if i < 172 then b 171 else (if i < 173 then b 172 else b 173))) else (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)))) else (if i < 186 then (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 184 then b 183 else (if i < 185 then b 184 else b 185))) else (if i < 189 then (if i < 187 then b 186 else (if i < 188 then b 187 else b 188)) else (if i < 191 then (if i < 190 then b 189 else b 190) else (if i < 192 then b 191 else b 192)))))))) else (if i < 289 then (if i < 241 then (if i < 217 then (if i < 205 then (if i < 199 then (if i < 196 then (if i < 194 then b 193 else (if i < 195 then b 194 else b 195)) else (if i < 197 then b 196 else (if i < 198 then b 197 else b 198))) else (if i < 202 then (if i < 200 then b 199 else (if i < 201 then b 200 else b 201)) else (if i < 203 then b 202 else (if i < 204 then b 203 else b 204)))) else (if i < 211 then (if i < 208 then (if i < 206 then b 205 else (if i < 207 then b 206 else b 207)) else (if i < 209 then b 208 else (if i < 210 then b 209 else b 210))) else (if i < 214 then (if i < 212 then b 211 else (if i < 213 then b 212 else b 213)) else (if i < 215 then b 214 else (if i < 216 then b 215 else b 216))))) else (if i < 229 then (if i < 223 then (if i < 220 then (if i < 218 then b 217 else (if i < 219 then b 218 else decide (1 ≤ count219 b))) else (if i < 221 then decide (2 ≤ count219 b) else (if i < 222 then decide (1 ≤ count221 b) else decide (2 ≤ count221 b)))) else (if i < 226 then (if i < 224 then decide (1 ≤ count223 b) else (if i < 225 then decide (2 ≤ count223 b) else decide (1 ≤ count225 b))) else (if i < 227 then decide (2 ≤ count225 b) else (if i < 228 then decide (1 ≤ count227 b) else decide (2 ≤ count227 b))))) else (if i < 235 then (if i < 232 then (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b))) else (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))) else (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 239 then decide (2 ≤ count237 b) else (if i < 240 then decide (1 ≤ count239 b) else decide (2 ≤ count239 b))))))) else (if i < 265 then (if i < 253 then (if i < 247 then (if i < 244 then (if i < 242 then decide (1 ≤ count241 b) else (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b))) else (if i < 245 then decide (2 ≤ count243 b) else (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)))) else (if i < 250 then (if i < 248 then decide (1 ≤ count247 b) else (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b))) else (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b))))) else (if i < 259 then (if i < 256 then (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b))) else (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b)))) else (if i < 262 then (if i < 260 then decide (1 ≤ count259 b) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b))) else (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b)))))) else (if i < 277 then (if i < 271 then (if i < 268 then (if i < 266 then decide (1 ≤ count265 b) else (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b))) else (if i < 269 then decide (2 ≤ count267 b) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)))) else (if i < 274 then (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))) else (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))))) else (if i < 283 then (if i < 280 then (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))) else (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)))) else (if i < 286 then (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b))) else (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)))))))) else (if i < 337 then (if i < 313 then (if i < 301 then (if i < 295 then (if i < 292 then (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b))) else (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)))) else (if i < 298 then (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))) else (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))))) else (if i < 307 then (if i < 304 then (if i < 302 then decide (1 ≤ count301 b) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b))) else (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)))) else (if i < 310 then (if i < 308 then decide (1 ≤ count307 b) else (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b))) else (if i < 311 then decide (2 ≤ count309 b) else (if i < 312 then decide (1 ≤ count311 b) else decide (2 ≤ count311 b)))))) else (if i < 325 then (if i < 319 then (if i < 316 then (if i < 314 then decide (1 ≤ count313 b) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b)))) else (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))) else (if i < 331 then (if i < 328 then (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))) else (if i < 329 then decide (2 ≤ count327 b) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)))) else (if i < 334 then (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b))) else (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b))))))) else (if i < 361 then (if i < 349 then (if i < 343 then (if i < 340 then (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))) else (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)))) else (if i < 346 then (if i < 344 then decide (1 ≤ count343 b) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 347 then decide (2 ≤ count345 b) else (if i < 348 then decide (1 ≤ count347 b) else decide (2 ≤ count347 b))))) else (if i < 355 then (if i < 352 then (if i < 350 then decide (1 ≤ count349 b) else (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b))) else (if i < 353 then decide (2 ≤ count351 b) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)))) else (if i < 358 then (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b))) else (if i < 359 then decide (2 ≤ count357 b) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))))) else (if i < 373 then (if i < 367 then (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)))) else (if i < 370 then (if i < 368 then decide (1 ≤ count367 b) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))) else (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))))) else (if i < 379 then (if i < 376 then (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b))) else (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)))) else (if i < 382 then (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))) else (if i < 384 then (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)))))))))) else (if i < 579 then (if i < 482 then (if i < 434 then (if i < 410 then (if i < 398 then (if i < 392 then (if i < 389 then (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))) else (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b)))) else (if i < 395 then (if i < 393 then decide (2 ≤ count391 b) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b))) else (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))))) else (if i < 404 then (if i < 401 then (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b))) else (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))) else (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 408 then decide (1 ≤ count407 b) else (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)))))) else (if i < 422 then (if i < 416 then (if i < 413 then (if i < 411 then decide (2 ≤ count409 b) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))) else (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)))) else (if i < 419 then (if i < 417 then decide (2 ≤ count415 b) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b))) else (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))))) else (if i < 428 then (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b)))) else (if i < 431 then (if i < 429 then decide (2 ≤ count427 b) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))) else (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))))))) else (if i < 458 then (if i < 446 then (if i < 440 then (if i < 437 then (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b))) else (if i < 438 then decide (3 ≤ count435 b) else (if i < 439 then decide (1 ≤ count438 b) else decide (2 ≤ count438 b)))) else (if i < 443 then (if i < 441 then decide (1 ≤ count440 b) else (if i < 442 then decide (2 ≤ count440 b) else decide (3 ≤ count440 b))) else (if i < 444 then decide (1 ≤ count443 b) else (if i < 445 then decide (2 ≤ count443 b) else decide (3 ≤ count443 b))))) else (if i < 452 then (if i < 449 then (if i < 447 then decide (4 ≤ count443 b) else (if i < 448 then decide (5 ≤ count443 b) else decide (6 ≤ count443 b))) else (if i < 450 then decide (1 ≤ count449 b) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)))) else (if i < 455 then (if i < 453 then decide (2 ≤ count451 b) else (if i < 454 then decide (3 ≤ count451 b) else decide (1 ≤ count454 b))) else (if i < 456 then decide (2 ≤ count454 b) else (if i < 457 then decide (1 ≤ count456 b) else decide (2 ≤ count456 b)))))) else (if i < 470 then (if i < 464 then (if i < 461 then (if i < 459 then decide (1 ≤ count458 b) else (if i < 460 then decide (2 ≤ count458 b) else decide (3 ≤ count458 b))) else (if i < 462 then decide (4 ≤ count458 b) else (if i < 463 then decide (1 ≤ count462 b) else decide (2 ≤ count462 b)))) else (if i < 467 then (if i < 465 then decide (3 ≤ count462 b) else (if i < 466 then decide (4 ≤ count462 b) else decide (5 ≤ count462 b))) else (if i < 468 then decide (6 ≤ count462 b) else (if i < 469 then decide (7 ≤ count462 b) else decide (1 ≤ count469 b))))) else (if i < 476 then (if i < 473 then (if i < 471 then decide (2 ≤ count469 b) else (if i < 472 then decide (3 ≤ count469 b) else decide (4 ≤ count469 b))) else (if i < 474 then decide (5 ≤ count469 b) else (if i < 475 then decide (6 ≤ count469 b) else decide (7 ≤ count469 b)))) else (if i < 479 then (if i < 477 then decide (8 ≤ count469 b) else (if i < 478 then decide (9 ≤ count469 b) else decide (10 ≤ count469 b))) else (if i < 480 then decide (11 ≤ count469 b) else (if i < 481 then decide (12 ≤ count469 b) else decide (13 ≤ count469 b)))))))) else (if i < 530 then (if i < 506 then (if i < 494 then (if i < 488 then (if i < 485 then (if i < 483 then decide (1 ≤ count482 b) else (if i < 484 then decide (2 ≤ count482 b) else decide (1 ≤ count484 b))) else (if i < 486 then decide (2 ≤ count484 b) else (if i < 487 then decide (3 ≤ count484 b) else decide (1 ≤ count487 b)))) else (if i < 491 then (if i < 489 then decide (2 ≤ count487 b) else (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b))) else (if i < 492 then decide (1 ≤ count491 b) else (if i < 493 then decide (2 ≤ count491 b) else decide (3 ≤ count491 b))))) else (if i < 500 then (if i < 497 then (if i < 495 then decide (4 ≤ count491 b) else (if i < 496 then decide (1 ≤ count495 b) else decide (2 ≤ count495 b))) else (if i < 498 then decide (3 ≤ count495 b) else (if i < 499 then decide (4 ≤ count495 b) else decide (5 ≤ count495 b)))) else (if i < 503 then (if i < 501 then decide (6 ≤ count495 b) else (if i < 502 then decide (7 ≤ count495 b) else decide (1 ≤ count502 b))) else (if i < 504 then decide (2 ≤ count502 b) else (if i < 505 then decide (1 ≤ count504 b) else decide (2 ≤ count504 b)))))) else (if i < 518 then (if i < 512 then (if i < 509 then (if i < 507 then decide (3 ≤ count504 b) else (if i < 508 then decide (1 ≤ count507 b) else decide (2 ≤ count507 b))) else (if i < 510 then decide (1 ≤ count509 b) else (if i < 511 then decide (2 ≤ count509 b) else decide (1 ≤ count511 b)))) else (if i < 515 then (if i < 513 then decide (2 ≤ count511 b) else (if i < 514 then decide (3 ≤ count511 b) else decide (4 ≤ count511 b))) else (if i < 516 then decide (1 ≤ count515 b) else (if i < 517 then decide (2 ≤ count515 b) else decide (3 ≤ count515 b))))) else (if i < 524 then (if i < 521 then (if i < 519 then decide (4 ≤ count515 b) else (if i < 520 then decide (5 ≤ count515 b) else decide (6 ≤ count515 b))) else (if i < 522 then decide (7 ≤ count515 b) else (if i < 523 then decide (1 ≤ count522 b) else decide (2 ≤ count522 b)))) else (if i < 527 then (if i < 525 then decide (3 ≤ count522 b) else (if i < 526 then decide (4 ≤ count522 b) else decide (5 ≤ count522 b))) else (if i < 528 then decide (6 ≤ count522 b) else (if i < 529 then decide (7 ≤ count522 b) else decide (8 ≤ count522 b))))))) else (if i < 554 then (if i < 542 then (if i < 536 then (if i < 533 then (if i < 531 then decide (9 ≤ count522 b) else (if i < 532 then decide (10 ≤ count522 b) else decide (11 ≤ count522 b))) else (if i < 534 then decide (12 ≤ count522 b) else (if i < 535 then decide (13 ≤ count522 b) else decide (14 ≤ count522 b)))) else (if i < 539 then (if i < 537 then decide (1 ≤ count536 b) else (if i < 538 then decide (2 ≤ count536 b) else decide (3 ≤ count536 b))) else (if i < 540 then decide (4 ≤ count536 b) else (if i < 541 then decide (5 ≤ count536 b) else decide (6 ≤ count536 b))))) else (if i < 548 then (if i < 545 then (if i < 543 then decide (7 ≤ count536 b) else (if i < 544 then decide (8 ≤ count536 b) else decide (9 ≤ count536 b))) else (if i < 546 then decide (10 ≤ count536 b) else (if i < 547 then decide (11 ≤ count536 b) else decide (12 ≤ count536 b)))) else (if i < 551 then (if i < 549 then decide (13 ≤ count536 b) else (if i < 550 then decide (14 ≤ count536 b) else decide (15 ≤ count536 b))) else (if i < 552 then decide (16 ≤ count536 b) else (if i < 553 then decide (17 ≤ count536 b) else decide (18 ≤ count536 b)))))) else (if i < 566 then (if i < 560 then (if i < 557 then (if i < 555 then decide (19 ≤ count536 b) else (if i < 556 then decide (20 ≤ count536 b) else decide (21 ≤ count536 b))) else (if i < 558 then decide (22 ≤ count536 b) else (if i < 559 then decide (23 ≤ count536 b) else decide (24 ≤ count536 b)))) else (if i < 563 then (if i < 561 then decide (25 ≤ count536 b) else (if i < 562 then decide (26 ≤ count536 b) else decide (27 ≤ count536 b))) else (if i < 564 then decide (1 ≤ count563 b) else (if i < 565 then decide (2 ≤ count563 b) else decide (1 ≤ count565 b))))) else (if i < 572 then (if i < 569 then (if i < 567 then decide (2 ≤ count565 b) else (if i < 568 then decide (3 ≤ count565 b) else decide (1 ≤ count568 b))) else (if i < 570 then decide (2 ≤ count568 b) else (if i < 571 then decide (1 ≤ count570 b) else decide (2 ≤ count570 b)))) else (if i < 575 then (if i < 573 then decide (3 ≤ count570 b) else (if i < 574 then decide (1 ≤ count573 b) else decide (2 ≤ count573 b))) else (if i < 577 then (if i < 576 then decide (3 ≤ count573 b) else decide (4 ≤ count573 b)) else (if i < 578 then decide (5 ≤ count573 b) else decide (6 ≤ count573 b))))))))) else (if i < 676 then (if i < 627 then (if i < 603 then (if i < 591 then (if i < 585 then (if i < 582 then (if i < 580 then decide (1 ≤ count579 b) else (if i < 581 then decide (2 ≤ count579 b) else decide (1 ≤ count581 b))) else (if i < 583 then decide (2 ≤ count581 b) else (if i < 584 then decide (3 ≤ count581 b) else decide (1 ≤ count584 b)))) else (if i < 588 then (if i < 586 then decide (2 ≤ count584 b) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b))) else (if i < 589 then decide (1 ≤ count588 b) else (if i < 590 then decide (2 ≤ count588 b) else decide (3 ≤ count588 b))))) else (if i < 597 then (if i < 594 then (if i < 592 then decide (4 ≤ count588 b) else (if i < 593 then decide (1 ≤ count592 b) else decide (2 ≤ count592 b))) else (if i < 595 then decide (3 ≤ count592 b) else (if i < 596 then decide (4 ≤ count592 b) else decide (5 ≤ count592 b)))) else (if i < 600 then (if i < 598 then decide (6 ≤ count592 b) else (if i < 599 then decide (7 ≤ count592 b) else decide (1 ≤ count599 b))) else (if i < 601 then decide (2 ≤ count599 b) else (if i < 602 then decide (3 ≤ count599 b) else decide (4 ≤ count599 b)))))) else (if i < 615 then (if i < 609 then (if i < 606 then (if i < 604 then decide (5 ≤ count599 b) else (if i < 605 then decide (6 ≤ count599 b) else decide (7 ≤ count599 b))) else (if i < 607 then decide (8 ≤ count599 b) else (if i < 608 then decide (9 ≤ count599 b) else decide (10 ≤ count599 b)))) else (if i < 612 then (if i < 610 then decide (11 ≤ count599 b) else (if i < 611 then decide (12 ≤ count599 b) else decide (13 ≤ count599 b))) else (if i < 613 then decide (1 ≤ count612 b) else (if i < 614 then decide (2 ≤ count612 b) else decide (1 ≤ count614 b))))) else (if i < 621 then (if i < 618 then (if i < 616 then decide (2 ≤ count614 b) else (if i < 617 then decide (3 ≤ count614 b) else decide (1 ≤ count617 b))) else (if i < 619 then decide (2 ≤ count617 b) else (if i < 620 then decide (1 ≤ count619 b) else decide (2 ≤ count619 b)))) else (if i < 624 then (if i < 622 then decide (1 ≤ count621 b) else (if i < 623 then decide (2 ≤ count621 b) else decide (3 ≤ count621 b))) else (if i < 625 then decide (4 ≤ count621 b) else (if i < 626 then decide (1 ≤ count625 b) else decide (2 ≤ count625 b))))))) else (if i < 651 then (if i < 639 then (if i < 633 then (if i < 630 then (if i < 628 then decide (3 ≤ count625 b) else (if i < 629 then decide (4 ≤ count625 b) else decide (5 ≤ count625 b))) else (if i < 631 then decide (6 ≤ count625 b) else (if i < 632 then decide (7 ≤ count625 b) else decide (1 ≤ count632 b)))) else (if i < 636 then (if i < 634 then decide (2 ≤ count632 b) else (if i < 635 then decide (1 ≤ count634 b) else decide (2 ≤ count634 b))) else (if i < 637 then decide (3 ≤ count634 b) else (if i < 638 then decide (1 ≤ count637 b) else decide (2 ≤ count637 b))))) else (if i < 645 then (if i < 642 then (if i < 640 then decide (1 ≤ count639 b) else (if i < 641 then decide (2 ≤ count639 b) else decide (1 ≤ count641 b))) else (if i < 643 then decide (2 ≤ count641 b) else (if i < 644 then decide (3 ≤ count641 b) else decide (4 ≤ count641 b)))) else (if i < 648 then (if i < 646 then decide (1 ≤ count645 b) else (if i < 647 then decide (2 ≤ count645 b) else decide (3 ≤ count645 b))) else (if i < 649 then decide (4 ≤ count645 b) else (if i < 650 then decide (5 ≤ count645 b) else decide (6 ≤ count645 b)))))) else (if i < 663 then (if i < 657 then (if i < 654 then (if i < 652 then decide (7 ≤ count645 b) else (if i < 653 then decide (1 ≤ count652 b) else decide (2 ≤ count652 b))) else (if i < 655 then decide (3 ≤ count652 b) else (if i < 656 then decide (4 ≤ count652 b) else decide (5 ≤ count652 b)))) else (if i < 660 then (if i < 658 then decide (6 ≤ count652 b) else (if i < 659 then decide (7 ≤ count652 b) else decide (8 ≤ count652 b))) else (if i < 661 then decide (9 ≤ count652 b) else (if i < 662 then decide (10 ≤ count652 b) else decide (11 ≤ count652 b))))) else (if i < 669 then (if i < 666 then (if i < 664 then decide (12 ≤ count652 b) else (if i < 665 then decide (13 ≤ count652 b) else decide (14 ≤ count652 b))) else (if i < 667 then decide (1 ≤ count666 b) else (if i < 668 then decide (2 ≤ count666 b) else decide (3 ≤ count666 b)))) else (if i < 672 then (if i < 670 then decide (4 ≤ count666 b) else (if i < 671 then decide (5 ≤ count666 b) else decide (6 ≤ count666 b))) else (if i < 674 then (if i < 673 then decide (7 ≤ count666 b) else decide (8 ≤ count666 b)) else (if i < 675 then decide (9 ≤ count666 b) else decide (10 ≤ count666 b)))))))) else (if i < 724 then (if i < 700 then (if i < 688 then (if i < 682 then (if i < 679 then (if i < 677 then decide (11 ≤ count666 b) else (if i < 678 then decide (12 ≤ count666 b) else decide (13 ≤ count666 b))) else (if i < 680 then decide (14 ≤ count666 b) else (if i < 681 then decide (15 ≤ count666 b) else decide (16 ≤ count666 b)))) else (if i < 685 then (if i < 683 then decide (17 ≤ count666 b) else (if i < 684 then decide (18 ≤ count666 b) else decide (19 ≤ count666 b))) else (if i < 686 then decide (20 ≤ count666 b) else (if i < 687 then decide (21 ≤ count666 b) else decide (22 ≤ count666 b))))) else (if i < 694 then (if i < 691 then (if i < 689 then decide (23 ≤ count666 b) else (if i < 690 then decide (24 ≤ count666 b) else decide (25 ≤ count666 b))) else (if i < 692 then decide (26 ≤ count666 b) else (if i < 693 then decide (27 ≤ count666 b) else decide (1 ≤ count693 b)))) else (if i < 697 then (if i < 695 then decide (2 ≤ count693 b) else (if i < 696 then decide (3 ≤ count693 b) else decide (4 ≤ count693 b))) else (if i < 698 then decide (5 ≤ count693 b) else (if i < 699 then decide (6 ≤ count693 b) else decide (7 ≤ count693 b)))))) else (if i < 712 then (if i < 706 then (if i < 703 then (if i < 701 then decide (8 ≤ count693 b) else (if i < 702 then decide (9 ≤ count693 b) else decide (10 ≤ count693 b))) else (if i < 704 then decide (11 ≤ count693 b) else (if i < 705 then decide (12 ≤ count693 b) else decide (13 ≤ count693 b)))) else (if i < 709 then (if i < 707 then decide (14 ≤ count693 b) else (if i < 708 then decide (15 ≤ count693 b) else decide (16 ≤ count693 b))) else (if i < 710 then decide (17 ≤ count693 b) else (if i < 711 then decide (18 ≤ count693 b) else decide (19 ≤ count693 b))))) else (if i < 718 then (if i < 715 then (if i < 713 then decide (20 ≤ count693 b) else (if i < 714 then decide (21 ≤ count693 b) else decide (22 ≤ count693 b))) else (if i < 716 then decide (23 ≤ count693 b) else (if i < 717 then decide (24 ≤ count693 b) else decide (25 ≤ count693 b)))) else (if i < 721 then (if i < 719 then decide (26 ≤ count693 b) else (if i < 720 then decide (27 ≤ count693 b) else decide (28 ≤ count693 b))) else (if i < 722 then decide (29 ≤ count693 b) else (if i < 723 then decide (30 ≤ count693 b) else decide (31 ≤ count693 b))))))) else (if i < 748 then (if i < 736 then (if i < 730 then (if i < 727 then (if i < 725 then decide (32 ≤ count693 b) else (if i < 726 then decide (33 ≤ count693 b) else decide (34 ≤ count693 b))) else (if i < 728 then decide (35 ≤ count693 b) else (if i < 729 then decide (36 ≤ count693 b) else decide (37 ≤ count693 b)))) else (if i < 733 then (if i < 731 then decide (38 ≤ count693 b) else (if i < 732 then decide (39 ≤ count693 b) else decide (40 ≤ count693 b))) else (if i < 734 then decide (41 ≤ count693 b) else (if i < 735 then decide (42 ≤ count693 b) else decide (1 ≤ count735 b))))) else (if i < 742 then (if i < 739 then (if i < 737 then decide (2 ≤ count735 b) else (if i < 738 then decide (1 ≤ count737 b) else decide (2 ≤ count737 b))) else (if i < 740 then decide (3 ≤ count737 b) else (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b)))) else (if i < 745 then (if i < 743 then decide (1 ≤ count742 b) else (if i < 744 then decide (2 ≤ count742 b) else decide (3 ≤ count742 b))) else (if i < 746 then decide (1 ≤ count745 b) else (if i < 747 then decide (2 ≤ count745 b) else decide (3 ≤ count745 b)))))) else (if i < 760 then (if i < 754 then (if i < 751 then (if i < 749 then decide (4 ≤ count745 b) else (if i < 750 then decide (5 ≤ count745 b) else decide (6 ≤ count745 b))) else (if i < 752 then decide (1 ≤ count751 b) else (if i < 753 then decide (2 ≤ count751 b) else decide (1 ≤ count753 b)))) else (if i < 757 then (if i < 755 then decide (2 ≤ count753 b) else (if i < 756 then decide (3 ≤ count753 b) else decide (1 ≤ count756 b))) else (if i < 758 then decide (2 ≤ count756 b) else (if i < 759 then decide (1 ≤ count758 b) else decide (2 ≤ count758 b))))) else (if i < 766 then (if i < 763 then (if i < 761 then decide (1 ≤ count760 b) else (if i < 762 then decide (2 ≤ count760 b) else decide (3 ≤ count760 b))) else (if i < 764 then decide (4 ≤ count760 b) else (if i < 765 then decide (1 ≤ count764 b) else decide (2 ≤ count764 b)))) else (if i < 769 then (if i < 767 then decide (3 ≤ count764 b) else (if i < 768 then decide (4 ≤ count764 b) else decide (5 ≤ count764 b))) else (if i < 771 then (if i < 770 then decide (6 ≤ count764 b) else decide (7 ≤ count764 b)) else (if i < 772 then decide (1 ≤ count771 b) else decide (2 ≤ count771 b))))))))))) else (if i < 1160 then (if i < 966 then (if i < 869 then (if i < 821 then (if i < 797 then (if i < 785 then (if i < 779 then (if i < 776 then (if i < 774 then decide (3 ≤ count771 b) else (if i < 775 then decide (4 ≤ count771 b) else decide (5 ≤ count771 b))) else (if i < 777 then decide (6 ≤ count771 b) else (if i < 778 then decide (7 ≤ count771 b) else decide (8 ≤ count771 b)))) else (if i < 782 then (if i < 780 then decide (9 ≤ count771 b) else (if i < 781 then decide (10 ≤ count771 b) else decide (11 ≤ count771 b))) else (if i < 783 then decide (12 ≤ count771 b) else (if i < 784 then decide (13 ≤ count771 b) else decide (1 ≤ count784 b))))) else (if i < 791 then (if i < 788 then (if i < 786 then decide (2 ≤ count784 b) else (if i < 787 then decide (1 ≤ count786 b) else decide (2 ≤ count786 b))) else (if i < 789 then decide (3 ≤ count786 b) else (if i < 790 then decide (1 ≤ count789 b) else decide (2 ≤ count789 b)))) else (if i < 794 then (if i < 792 then decide (1 ≤ count791 b) else (if i < 793 then decide (2 ≤ count791 b) else decide (1 ≤ count793 b))) else (if i < 795 then decide (2 ≤ count793 b) else (if i < 796 then decide (3 ≤ count793 b) else decide (4 ≤ count793 b)))))) else (if i < 809 then (if i < 803 then (if i < 800 then (if i < 798 then decide (1 ≤ count797 b) else (if i < 799 then decide (2 ≤ count797 b) else decide (3 ≤ count797 b))) else (if i < 801 then decide (4 ≤ count797 b) else (if i < 802 then decide (5 ≤ count797 b) else decide (6 ≤ count797 b)))) else (if i < 806 then (if i < 804 then decide (7 ≤ count797 b) else (if i < 805 then decide (1 ≤ count804 b) else decide (2 ≤ count804 b))) else (if i < 807 then decide (1 ≤ count806 b) else (if i < 808 then decide (2 ≤ count806 b) else decide (3 ≤ count806 b))))) else (if i < 815 then (if i < 812 then (if i < 810 then decide (1 ≤ count809 b) else (if i < 811 then decide (2 ≤ count809 b) else decide (1 ≤ count811 b))) else (if i < 813 then decide (2 ≤ count811 b) else (if i < 814 then decide (1 ≤ count813 b) else decide (2 ≤ count813 b)))) else (if i < 818 then (if i < 816 then decide (3 ≤ count813 b) else (if i < 817 then decide (4 ≤ count813 b) else decide (1 ≤ count817 b))) else (if i < 819 then decide (2 ≤ count817 b) else (if i < 820 then decide (3 ≤ count817 b) else decide (4 ≤ count817 b))))))) else (if i < 845 then (if i < 833 then (if i < 827 then (if i < 824 then (if i < 822 then decide (5 ≤ count817 b) else (if i < 823 then decide (6 ≤ count817 b) else decide (7 ≤ count817 b))) else (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (3 ≤ count824 b)))) else (if i < 830 then (if i < 828 then decide (4 ≤ count824 b) else (if i < 829 then decide (5 ≤ count824 b) else decide (6 ≤ count824 b))) else (if i < 831 then decide (7 ≤ count824 b) else (if i < 832 then decide (8 ≤ count824 b) else decide (9 ≤ count824 b))))) else (if i < 839 then (if i < 836 then (if i < 834 then decide (10 ≤ count824 b) else (if i < 835 then decide (11 ≤ count824 b) else decide (12 ≤ count824 b))) else (if i < 837 then decide (13 ≤ count824 b) else (if i < 838 then decide (14 ≤ count824 b) else decide (1 ≤ count838 b)))) else (if i < 842 then (if i < 840 then decide (2 ≤ count838 b) else (if i < 841 then decide (3 ≤ count838 b) else decide (4 ≤ count838 b))) else (if i < 843 then decide (5 ≤ count838 b) else (if i < 844 then decide (6 ≤ count838 b) else decide (7 ≤ count838 b)))))) else (if i < 857 then (if i < 851 then (if i < 848 then (if i < 846 then decide (8 ≤ count838 b) else (if i < 847 then decide (9 ≤ count838 b) else decide (10 ≤ count838 b))) else (if i < 849 then decide (11 ≤ count838 b) else (if i < 850 then decide (12 ≤ count838 b) else decide (13 ≤ count838 b)))) else (if i < 854 then (if i < 852 then decide (14 ≤ count838 b) else (if i < 853 then decide (1 ≤ count852 b) else decide (2 ≤ count852 b))) else (if i < 855 then decide (1 ≤ count854 b) else (if i < 856 then decide (2 ≤ count854 b) else decide (3 ≤ count854 b))))) else (if i < 863 then (if i < 860 then (if i < 858 then decide (1 ≤ count857 b) else (if i < 859 then decide (2 ≤ count857 b) else decide (1 ≤ count859 b))) else (if i < 861 then decide (2 ≤ count859 b) else (if i < 862 then decide (3 ≤ count859 b) else decide (1 ≤ count862 b)))) else (if i < 866 then (if i < 864 then decide (2 ≤ count862 b) else (if i < 865 then decide (3 ≤ count862 b) else decide (4 ≤ count862 b))) else (if i < 867 then decide (5 ≤ count862 b) else (if i < 868 then decide (6 ≤ count862 b) else decide (1 ≤ count868 b)))))))) else (if i < 917 then (if i < 893 then (if i < 881 then (if i < 875 then (if i < 872 then (if i < 870 then decide (2 ≤ count868 b) else (if i < 871 then decide (1 ≤ count870 b) else decide (2 ≤ count870 b))) else (if i < 873 then decide (3 ≤ count870 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b)))) else (if i < 878 then (if i < 876 then decide (1 ≤ count875 b) else (if i < 877 then decide (2 ≤ count875 b) else decide (1 ≤ count877 b))) else (if i < 879 then decide (2 ≤ count877 b) else (if i < 880 then decide (3 ≤ count877 b) else decide (4 ≤ count877 b))))) else (if i < 887 then (if i < 884 then (if i < 882 then decide (1 ≤ count881 b) else (if i < 883 then decide (2 ≤ count881 b) else decide (3 ≤ count881 b))) else (if i < 885 then decide (4 ≤ count881 b) else (if i < 886 then decide (5 ≤ count881 b) else decide (6 ≤ count881 b)))) else (if i < 890 then (if i < 888 then decide (7 ≤ count881 b) else (if i < 889 then decide (1 ≤ count888 b) else decide (2 ≤ count888 b))) else (if i < 891 then decide (3 ≤ count888 b) else (if i < 892 then decide (4 ≤ count888 b) else decide (5 ≤ count888 b)))))) else (if i < 905 then (if i < 899 then (if i < 896 then (if i < 894 then decide (6 ≤ count888 b) else (if i < 895 then decide (7 ≤ count888 b) else decide (8 ≤ count888 b))) else (if i < 897 then decide (9 ≤ count888 b) else (if i < 898 then decide (10 ≤ count888 b) else decide (11 ≤ count888 b)))) else (if i < 902 then (if i < 900 then decide (12 ≤ count888 b) else (if i < 901 then decide (13 ≤ count888 b) else decide (1 ≤ count901 b))) else (if i < 903 then decide (2 ≤ count901 b) else (if i < 904 then decide (1 ≤ count903 b) else decide (2 ≤ count903 b))))) else (if i < 911 then (if i < 908 then (if i < 906 then decide (3 ≤ count903 b) else (if i < 907 then decide (1 ≤ count906 b) else decide (2 ≤ count906 b))) else (if i < 909 then decide (1 ≤ count908 b) else (if i < 910 then decide (2 ≤ count908 b) else decide (1 ≤ count910 b)))) else (if i < 914 then (if i < 912 then decide (2 ≤ count910 b) else (if i < 913 then decide (3 ≤ count910 b) else decide (4 ≤ count910 b))) else (if i < 915 then decide (1 ≤ count914 b) else (if i < 916 then decide (2 ≤ count914 b) else decide (3 ≤ count914 b))))))) else (if i < 941 then (if i < 929 then (if i < 923 then (if i < 920 then (if i < 918 then decide (4 ≤ count914 b) else (if i < 919 then decide (5 ≤ count914 b) else decide (6 ≤ count914 b))) else (if i < 921 then decide (7 ≤ count914 b) else (if i < 922 then decide (1 ≤ count921 b) else decide (2 ≤ count921 b)))) else (if i < 926 then (if i < 924 then decide (1 ≤ count923 b) else (if i < 925 then decide (2 ≤ count923 b) else decide (3 ≤ count923 b))) else (if i < 927 then decide (1 ≤ count926 b) else (if i < 928 then decide (2 ≤ count926 b) else decide (1 ≤ count928 b))))) else (if i < 935 then (if i < 932 then (if i < 930 then decide (2 ≤ count928 b) else (if i < 931 then decide (1 ≤ count930 b) else decide (2 ≤ count930 b))) else (if i < 933 then decide (3 ≤ count930 b) else (if i < 934 then decide (4 ≤ count930 b) else decide (1 ≤ count934 b)))) else (if i < 938 then (if i < 936 then decide (2 ≤ count934 b) else (if i < 937 then decide (3 ≤ count934 b) else decide (4 ≤ count934 b))) else (if i < 939 then decide (5 ≤ count934 b) else (if i < 940 then decide (6 ≤ count934 b) else decide (7 ≤ count934 b)))))) else (if i < 953 then (if i < 947 then (if i < 944 then (if i < 942 then decide (1 ≤ count941 b) else (if i < 943 then decide (2 ≤ count941 b) else decide (3 ≤ count941 b))) else (if i < 945 then decide (4 ≤ count941 b) else (if i < 946 then decide (5 ≤ count941 b) else decide (6 ≤ count941 b)))) else (if i < 950 then (if i < 948 then decide (7 ≤ count941 b) else (if i < 949 then decide (8 ≤ count941 b) else decide (9 ≤ count941 b))) else (if i < 951 then decide (10 ≤ count941 b) else (if i < 952 then decide (11 ≤ count941 b) else decide (12 ≤ count941 b))))) else (if i < 959 then (if i < 956 then (if i < 954 then decide (13 ≤ count941 b) else (if i < 955 then decide (14 ≤ count941 b) else decide (1 ≤ count955 b))) else (if i < 957 then decide (2 ≤ count955 b) else (if i < 958 then decide (3 ≤ count955 b) else decide (4 ≤ count955 b)))) else (if i < 962 then (if i < 960 then decide (5 ≤ count955 b) else (if i < 961 then decide (6 ≤ count955 b) else decide (7 ≤ count955 b))) else (if i < 964 then (if i < 963 then decide (8 ≤ count955 b) else decide (9 ≤ count955 b)) else (if i < 965 then decide (10 ≤ count955 b) else decide (11 ≤ count955 b))))))))) else (if i < 1063 then (if i < 1014 then (if i < 990 then (if i < 978 then (if i < 972 then (if i < 969 then (if i < 967 then decide (12 ≤ count955 b) else (if i < 968 then decide (13 ≤ count955 b) else decide (14 ≤ count955 b))) else (if i < 970 then decide (1 ≤ count969 b) else (if i < 971 then decide (2 ≤ count969 b) else decide (3 ≤ count969 b)))) else (if i < 975 then (if i < 973 then decide (4 ≤ count969 b) else (if i < 974 then decide (5 ≤ count969 b) else decide (6 ≤ count969 b))) else (if i < 976 then decide (7 ≤ count969 b) else (if i < 977 then decide (8 ≤ count969 b) else decide (9 ≤ count969 b))))) else (if i < 984 then (if i < 981 then (if i < 979 then decide (10 ≤ count969 b) else (if i < 980 then decide (11 ≤ count969 b) else decide (12 ≤ count969 b))) else (if i < 982 then decide (13 ≤ count969 b) else (if i < 983 then decide (14 ≤ count969 b) else decide (1 ≤ count983 b)))) else (if i < 987 then (if i < 985 then decide (2 ≤ count983 b) else (if i < 986 then decide (1 ≤ count985 b) else decide (2 ≤ count985 b))) else (if i < 988 then decide (3 ≤ count985 b) else (if i < 989 then decide (1 ≤ count988 b) else decide (2 ≤ count988 b)))))) else (if i < 1002 then (if i < 996 then (if i < 993 then (if i < 991 then decide (1 ≤ count990 b) else (if i < 992 then decide (2 ≤ count990 b) else decide (3 ≤ count990 b))) else (if i < 994 then decide (1 ≤ count993 b) else (if i < 995 then decide (2 ≤ count993 b) else decide (3 ≤ count993 b)))) else (if i < 999 then (if i < 997 then decide (4 ≤ count993 b) else (if i < 998 then decide (5 ≤ count993 b) else decide (6 ≤ count993 b))) else (if i < 1000 then decide (1 ≤ count999 b) else (if i < 1001 then decide (2 ≤ count999 b) else decide (1 ≤ count1001 b))))) else (if i < 1008 then (if i < 1005 then (if i < 1003 then decide (2 ≤ count1001 b) else (if i < 1004 then decide (3 ≤ count1001 b) else decide (1 ≤ count1004 b))) else (if i < 1006 then decide (2 ≤ count1004 b) else (if i < 1007 then decide (1 ≤ count1006 b) else decide (2 ≤ count1006 b)))) else (if i < 1011 then (if i < 1009 then decide (1 ≤ count1008 b) else (if i < 1010 then decide (2 ≤ count1008 b) else decide (3 ≤ count1008 b))) else (if i < 1012 then decide (4 ≤ count1008 b) else (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b))))))) else (if i < 1038 then (if i < 1026 then (if i < 1020 then (if i < 1017 then (if i < 1015 then decide (3 ≤ count1012 b) else (if i < 1016 then decide (4 ≤ count1012 b) else decide (5 ≤ count1012 b))) else (if i < 1018 then decide (6 ≤ count1012 b) else (if i < 1019 then decide (7 ≤ count1012 b) else decide (1 ≤ count1019 b)))) else (if i < 1023 then (if i < 1021 then decide (2 ≤ count1019 b) else (if i < 1022 then decide (3 ≤ count1019 b) else decide (4 ≤ count1019 b))) else (if i < 1024 then decide (5 ≤ count1019 b) else (if i < 1025 then decide (6 ≤ count1019 b) else decide (7 ≤ count1019 b))))) else (if i < 1032 then (if i < 1029 then (if i < 1027 then decide (8 ≤ count1019 b) else (if i < 1028 then decide (9 ≤ count1019 b) else decide (10 ≤ count1019 b))) else (if i < 1030 then decide (11 ≤ count1019 b) else (if i < 1031 then decide (12 ≤ count1019 b) else decide (13 ≤ count1019 b)))) else (if i < 1035 then (if i < 1033 then decide (1 ≤ count1032 b) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (1 ≤ count1034 b))) else (if i < 1036 then decide (2 ≤ count1034 b) else (if i < 1037 then decide (3 ≤ count1034 b) else decide (1 ≤ count1037 b)))))) else (if i < 1050 then (if i < 1044 then (if i < 1041 then (if i < 1039 then decide (2 ≤ count1037 b) else (if i < 1040 then decide (1 ≤ count1039 b) else decide (2 ≤ count1039 b))) else (if i < 1042 then decide (1 ≤ count1041 b) else (if i < 1043 then decide (2 ≤ count1041 b) else decide (3 ≤ count1041 b)))) else (if i < 1047 then (if i < 1045 then decide (4 ≤ count1041 b) else (if i < 1046 then decide (1 ≤ count1045 b) else decide (2 ≤ count1045 b))) else (if i < 1048 then decide (3 ≤ count1045 b) else (if i < 1049 then decide (4 ≤ count1045 b) else decide (5 ≤ count1045 b))))) else (if i < 1056 then (if i < 1053 then (if i < 1051 then decide (6 ≤ count1045 b) else (if i < 1052 then decide (7 ≤ count1045 b) else decide (1 ≤ count1052 b))) else (if i < 1054 then decide (2 ≤ count1052 b) else (if i < 1055 then decide (1 ≤ count1054 b) else decide (2 ≤ count1054 b)))) else (if i < 1059 then (if i < 1057 then decide (3 ≤ count1054 b) else (if i < 1058 then decide (1 ≤ count1057 b) else decide (2 ≤ count1057 b))) else (if i < 1061 then (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b)) else (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b)))))))) else (if i < 1111 then (if i < 1087 then (if i < 1075 then (if i < 1069 then (if i < 1066 then (if i < 1064 then decide (3 ≤ count1061 b) else (if i < 1065 then decide (4 ≤ count1061 b) else decide (1 ≤ count1065 b))) else (if i < 1067 then decide (2 ≤ count1065 b) else (if i < 1068 then decide (3 ≤ count1065 b) else decide (4 ≤ count1065 b)))) else (if i < 1072 then (if i < 1070 then decide (5 ≤ count1065 b) else (if i < 1071 then decide (6 ≤ count1065 b) else decide (7 ≤ count1065 b))) else (if i < 1073 then decide (1 ≤ count1072 b) else (if i < 1074 then decide (2 ≤ count1072 b) else decide (3 ≤ count1072 b))))) else (if i < 1081 then (if i < 1078 then (if i < 1076 then decide (4 ≤ count1072 b) else (if i < 1077 then decide (5 ≤ count1072 b) else decide (6 ≤ count1072 b))) else (if i < 1079 then decide (7 ≤ count1072 b) else (if i < 1080 then decide (8 ≤ count1072 b) else decide (9 ≤ count1072 b)))) else (if i < 1084 then (if i < 1082 then decide (10 ≤ count1072 b) else (if i < 1083 then decide (11 ≤ count1072 b) else decide (12 ≤ count1072 b))) else (if i < 1085 then decide (13 ≤ count1072 b) else (if i < 1086 then decide (14 ≤ count1072 b) else decide (1 ≤ count1086 b)))))) else (if i < 1099 then (if i < 1093 then (if i < 1090 then (if i < 1088 then decide (2 ≤ count1086 b) else (if i < 1089 then decide (3 ≤ count1086 b) else decide (4 ≤ count1086 b))) else (if i < 1091 then decide (5 ≤ count1086 b) else (if i < 1092 then decide (6 ≤ count1086 b) else decide (7 ≤ count1086 b)))) else (if i < 1096 then (if i < 1094 then decide (8 ≤ count1086 b) else (if i < 1095 then decide (9 ≤ count1086 b) else decide (10 ≤ count1086 b))) else (if i < 1097 then decide (11 ≤ count1086 b) else (if i < 1098 then decide (12 ≤ count1086 b) else decide (13 ≤ count1086 b))))) else (if i < 1105 then (if i < 1102 then (if i < 1100 then decide (14 ≤ count1086 b) else (if i < 1101 then decide (15 ≤ count1086 b) else decide (16 ≤ count1086 b))) else (if i < 1103 then decide (17 ≤ count1086 b) else (if i < 1104 then decide (18 ≤ count1086 b) else decide (19 ≤ count1086 b)))) else (if i < 1108 then (if i < 1106 then decide (20 ≤ count1086 b) else (if i < 1107 then decide (21 ≤ count1086 b) else decide (22 ≤ count1086 b))) else (if i < 1109 then decide (23 ≤ count1086 b) else (if i < 1110 then decide (24 ≤ count1086 b) else decide (25 ≤ count1086 b))))))) else (if i < 1135 then (if i < 1123 then (if i < 1117 then (if i < 1114 then (if i < 1112 then decide (26 ≤ count1086 b) else (if i < 1113 then decide (27 ≤ count1086 b) else decide (1 ≤ count1113 b))) else (if i < 1115 then decide (2 ≤ count1113 b) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b)))) else (if i < 1120 then (if i < 1118 then decide (3 ≤ count1115 b) else (if i < 1119 then decide (1 ≤ count1118 b) else decide (2 ≤ count1118 b))) else (if i < 1121 then decide (1 ≤ count1120 b) else (if i < 1122 then decide (2 ≤ count1120 b) else decide (1 ≤ count1122 b))))) else (if i < 1129 then (if i < 1126 then (if i < 1124 then decide (2 ≤ count1122 b) else (if i < 1125 then decide (3 ≤ count1122 b) else decide (4 ≤ count1122 b))) else (if i < 1127 then decide (1 ≤ count1126 b) else (if i < 1128 then decide (2 ≤ count1126 b) else decide (3 ≤ count1126 b)))) else (if i < 1132 then (if i < 1130 then decide (4 ≤ count1126 b) else (if i < 1131 then decide (5 ≤ count1126 b) else decide (6 ≤ count1126 b))) else (if i < 1133 then decide (7 ≤ count1126 b) else (if i < 1134 then decide (1 ≤ count1133 b) else decide (2 ≤ count1133 b)))))) else (if i < 1147 then (if i < 1141 then (if i < 1138 then (if i < 1136 then decide (1 ≤ count1135 b) else (if i < 1137 then decide (2 ≤ count1135 b) else decide (3 ≤ count1135 b))) else (if i < 1139 then decide (1 ≤ count1138 b) else (if i < 1140 then decide (2 ≤ count1138 b) else decide (1 ≤ count1140 b)))) else (if i < 1144 then (if i < 1142 then decide (2 ≤ count1140 b) else (if i < 1143 then decide (1 ≤ count1142 b) else decide (2 ≤ count1142 b))) else (if i < 1145 then decide (3 ≤ count1142 b) else (if i < 1146 then decide (4 ≤ count1142 b) else decide (1 ≤ count1146 b))))) else (if i < 1153 then (if i < 1150 then (if i < 1148 then decide (2 ≤ count1146 b) else (if i < 1149 then decide (3 ≤ count1146 b) else decide (4 ≤ count1146 b))) else (if i < 1151 then decide (5 ≤ count1146 b) else (if i < 1152 then decide (6 ≤ count1146 b) else decide (7 ≤ count1146 b)))) else (if i < 1156 then (if i < 1154 then decide (1 ≤ count1153 b) else (if i < 1155 then decide (2 ≤ count1153 b) else decide (3 ≤ count1153 b))) else (if i < 1158 then (if i < 1157 then decide (4 ≤ count1153 b) else decide (5 ≤ count1153 b)) else (if i < 1159 then decide (6 ≤ count1153 b) else decide (7 ≤ count1153 b)))))))))) else (if i < 1353 then (if i < 1256 then (if i < 1208 then (if i < 1184 then (if i < 1172 then (if i < 1166 then (if i < 1163 then (if i < 1161 then decide (8 ≤ count1153 b) else (if i < 1162 then decide (9 ≤ count1153 b) else decide (10 ≤ count1153 b))) else (if i < 1164 then decide (11 ≤ count1153 b) else (if i < 1165 then decide (12 ≤ count1153 b) else decide (13 ≤ count1153 b)))) else (if i < 1169 then (if i < 1167 then decide (14 ≤ count1153 b) else (if i < 1168 then decide (1 ≤ count1167 b) else decide (2 ≤ count1167 b))) else (if i < 1170 then decide (1 ≤ count1169 b) else (if i < 1171 then decide (2 ≤ count1169 b) else decide (3 ≤ count1169 b))))) else (if i < 1178 then (if i < 1175 then (if i < 1173 then decide (1 ≤ count1172 b) else (if i < 1174 then decide (2 ≤ count1172 b) else decide (1 ≤ count1174 b))) else (if i < 1176 then decide (2 ≤ count1174 b) else (if i < 1177 then decide (1 ≤ count1176 b) else decide (2 ≤ count1176 b)))) else (if i < 1181 then (if i < 1179 then decide (3 ≤ count1176 b) else (if i < 1180 then decide (4 ≤ count1176 b) else decide (1 ≤ count1180 b))) else (if i < 1182 then decide (2 ≤ count1180 b) else (if i < 1183 then decide (3 ≤ count1180 b) else decide (4 ≤ count1180 b)))))) else (if i < 1196 then (if i < 1190 then (if i < 1187 then (if i < 1185 then decide (5 ≤ count1180 b) else (if i < 1186 then decide (6 ≤ count1180 b) else decide (7 ≤ count1180 b))) else (if i < 1188 then decide (1 ≤ count1187 b) else (if i < 1189 then decide (2 ≤ count1187 b) else decide (1 ≤ count1189 b)))) else (if i < 1193 then (if i < 1191 then decide (2 ≤ count1189 b) else (if i < 1192 then decide (3 ≤ count1189 b) else decide (1 ≤ count1192 b))) else (if i < 1194 then decide (2 ≤ count1192 b) else (if i < 1195 then decide (1 ≤ count1194 b) else decide (2 ≤ count1194 b))))) else (if i < 1202 then (if i < 1199 then (if i < 1197 then decide (1 ≤ count1196 b) else (if i < 1198 then decide (2 ≤ count1196 b) else decide (3 ≤ count1196 b))) else (if i < 1200 then decide (4 ≤ count1196 b) else (if i < 1201 then decide (1 ≤ count1200 b) else decide (2 ≤ count1200 b)))) else (if i < 1205 then (if i < 1203 then decide (3 ≤ count1200 b) else (if i < 1204 then decide (4 ≤ count1200 b) else decide (5 ≤ count1200 b))) else (if i < 1206 then decide (6 ≤ count1200 b) else (if i < 1207 then decide (7 ≤ count1200 b) else decide (1 ≤ count1207 b))))))) else (if i < 1232 then (if i < 1220 then (if i < 1214 then (if i < 1211 then (if i < 1209 then decide (2 ≤ count1207 b) else (if i < 1210 then decide (3 ≤ count1207 b) else decide (4 ≤ count1207 b))) else (if i < 1212 then decide (5 ≤ count1207 b) else (if i < 1213 then decide (6 ≤ count1207 b) else decide (7 ≤ count1207 b)))) else (if i < 1217 then (if i < 1215 then decide (8 ≤ count1207 b) else (if i < 1216 then decide (9 ≤ count1207 b) else decide (10 ≤ count1207 b))) else (if i < 1218 then decide (11 ≤ count1207 b) else (if i < 1219 then decide (12 ≤ count1207 b) else decide (13 ≤ count1207 b))))) else (if i < 1226 then (if i < 1223 then (if i < 1221 then decide (14 ≤ count1207 b) else (if i < 1222 then decide (1 ≤ count1221 b) else decide (2 ≤ count1221 b))) else (if i < 1224 then decide (3 ≤ count1221 b) else (if i < 1225 then decide (4 ≤ count1221 b) else decide (5 ≤ count1221 b)))) else (if i < 1229 then (if i < 1227 then decide (6 ≤ count1221 b) else (if i < 1228 then decide (7 ≤ count1221 b) else decide (8 ≤ count1221 b))) else (if i < 1230 then decide (9 ≤ count1221 b) else (if i < 1231 then decide (10 ≤ count1221 b) else decide (11 ≤ count1221 b)))))) else (if i < 1244 then (if i < 1238 then (if i < 1235 then (if i < 1233 then decide (12 ≤ count1221 b) else (if i < 1234 then decide (13 ≤ count1221 b) else decide (14 ≤ count1221 b))) else (if i < 1236 then decide (15 ≤ count1221 b) else (if i < 1237 then decide (16 ≤ count1221 b) else decide (17 ≤ count1221 b)))) else (if i < 1241 then (if i < 1239 then decide (18 ≤ count1221 b) else (if i < 1240 then decide (19 ≤ count1221 b) else decide (20 ≤ count1221 b))) else (if i < 1242 then decide (21 ≤ count1221 b) else (if i < 1243 then decide (22 ≤ count1221 b) else decide (23 ≤ count1221 b))))) else (if i < 1250 then (if i < 1247 then (if i < 1245 then decide (24 ≤ count1221 b) else (if i < 1246 then decide (25 ≤ count1221 b) else decide (26 ≤ count1221 b))) else (if i < 1248 then decide (27 ≤ count1221 b) else (if i < 1249 then decide (28 ≤ count1221 b) else decide (1 ≤ count1249 b)))) else (if i < 1253 then (if i < 1251 then decide (2 ≤ count1249 b) else (if i < 1252 then decide (3 ≤ count1249 b) else decide (4 ≤ count1249 b))) else (if i < 1254 then decide (5 ≤ count1249 b) else (if i < 1255 then decide (6 ≤ count1249 b) else decide (7 ≤ count1249 b)))))))) else (if i < 1304 then (if i < 1280 then (if i < 1268 then (if i < 1262 then (if i < 1259 then (if i < 1257 then decide (8 ≤ count1249 b) else (if i < 1258 then decide (9 ≤ count1249 b) else decide (10 ≤ count1249 b))) else (if i < 1260 then decide (11 ≤ count1249 b) else (if i < 1261 then decide (12 ≤ count1249 b) else decide (13 ≤ count1249 b)))) else (if i < 1265 then (if i < 1263 then decide (14 ≤ count1249 b) else (if i < 1264 then decide (15 ≤ count1249 b) else decide (16 ≤ count1249 b))) else (if i < 1266 then decide (17 ≤ count1249 b) else (if i < 1267 then decide (18 ≤ count1249 b) else decide (19 ≤ count1249 b))))) else (if i < 1274 then (if i < 1271 then (if i < 1269 then decide (20 ≤ count1249 b) else (if i < 1270 then decide (21 ≤ count1249 b) else decide (22 ≤ count1249 b))) else (if i < 1272 then decide (23 ≤ count1249 b) else (if i < 1273 then decide (24 ≤ count1249 b) else decide (25 ≤ count1249 b)))) else (if i < 1277 then (if i < 1275 then decide (26 ≤ count1249 b) else (if i < 1276 then decide (27 ≤ count1249 b) else decide (28 ≤ count1249 b))) else (if i < 1278 then decide (29 ≤ count1249 b) else (if i < 1279 then decide (30 ≤ count1249 b) else decide (31 ≤ count1249 b)))))) else (if i < 1292 then (if i < 1286 then (if i < 1283 then (if i < 1281 then decide (32 ≤ count1249 b) else (if i < 1282 then decide (33 ≤ count1249 b) else decide (34 ≤ count1249 b))) else (if i < 1284 then decide (35 ≤ count1249 b) else (if i < 1285 then decide (36 ≤ count1249 b) else decide (37 ≤ count1249 b)))) else (if i < 1289 then (if i < 1287 then decide (38 ≤ count1249 b) else (if i < 1288 then decide (39 ≤ count1249 b) else decide (40 ≤ count1249 b))) else (if i < 1290 then decide (41 ≤ count1249 b) else (if i < 1291 then decide (42 ≤ count1249 b) else decide (1 ≤ count1291 b))))) else (if i < 1298 then (if i < 1295 then (if i < 1293 then decide (2 ≤ count1291 b) else (if i < 1294 then decide (1 ≤ count1293 b) else decide (2 ≤ count1293 b))) else (if i < 1296 then decide (3 ≤ count1293 b) else (if i < 1297 then decide (1 ≤ count1296 b) else decide (2 ≤ count1296 b)))) else (if i < 1301 then (if i < 1299 then decide (1 ≤ count1298 b) else (if i < 1300 then decide (2 ≤ count1298 b) else decide (3 ≤ count1298 b))) else (if i < 1302 then decide (1 ≤ count1301 b) else (if i < 1303 then decide (2 ≤ count1301 b) else decide (3 ≤ count1301 b))))))) else (if i < 1328 then (if i < 1316 then (if i < 1310 then (if i < 1307 then (if i < 1305 then decide (4 ≤ count1301 b) else (if i < 1306 then decide (5 ≤ count1301 b) else decide (6 ≤ count1301 b))) else (if i < 1308 then decide (1 ≤ count1307 b) else (if i < 1309 then decide (2 ≤ count1307 b) else decide (1 ≤ count1309 b)))) else (if i < 1313 then (if i < 1311 then decide (2 ≤ count1309 b) else (if i < 1312 then decide (3 ≤ count1309 b) else decide (1 ≤ count1312 b))) else (if i < 1314 then decide (2 ≤ count1312 b) else (if i < 1315 then decide (1 ≤ count1314 b) else decide (2 ≤ count1314 b))))) else (if i < 1322 then (if i < 1319 then (if i < 1317 then decide (1 ≤ count1316 b) else (if i < 1318 then decide (2 ≤ count1316 b) else decide (3 ≤ count1316 b))) else (if i < 1320 then decide (4 ≤ count1316 b) else (if i < 1321 then decide (1 ≤ count1320 b) else decide (2 ≤ count1320 b)))) else (if i < 1325 then (if i < 1323 then decide (3 ≤ count1320 b) else (if i < 1324 then decide (4 ≤ count1320 b) else decide (5 ≤ count1320 b))) else (if i < 1326 then decide (6 ≤ count1320 b) else (if i < 1327 then decide (7 ≤ count1320 b) else decide (1 ≤ count1327 b)))))) else (if i < 1340 then (if i < 1334 then (if i < 1331 then (if i < 1329 then decide (2 ≤ count1327 b) else (if i < 1330 then decide (3 ≤ count1327 b) else decide (4 ≤ count1327 b))) else (if i < 1332 then decide (5 ≤ count1327 b) else (if i < 1333 then decide (6 ≤ count1327 b) else decide (7 ≤ count1327 b)))) else (if i < 1337 then (if i < 1335 then decide (8 ≤ count1327 b) else (if i < 1336 then decide (9 ≤ count1327 b) else decide (10 ≤ count1327 b))) else (if i < 1338 then decide (11 ≤ count1327 b) else (if i < 1339 then decide (12 ≤ count1327 b) else decide (13 ≤ count1327 b))))) else (if i < 1346 then (if i < 1343 then (if i < 1341 then decide (1 ≤ count1340 b) else (if i < 1342 then decide (2 ≤ count1340 b) else decide (1 ≤ count1342 b))) else (if i < 1344 then decide (2 ≤ count1342 b) else (if i < 1345 then decide (3 ≤ count1342 b) else decide (1 ≤ count1345 b)))) else (if i < 1349 then (if i < 1347 then decide (2 ≤ count1345 b) else (if i < 1348 then decide (1 ≤ count1347 b) else decide (2 ≤ count1347 b))) else (if i < 1351 then (if i < 1350 then decide (1 ≤ count1349 b) else decide (2 ≤ count1349 b)) else (if i < 1352 then decide (3 ≤ count1349 b) else decide (4 ≤ count1349 b))))))))) else (if i < 1450 then (if i < 1401 then (if i < 1377 then (if i < 1365 then (if i < 1359 then (if i < 1356 then (if i < 1354 then decide (1 ≤ count1353 b) else (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b))) else (if i < 1357 then decide (4 ≤ count1353 b) else (if i < 1358 then decide (5 ≤ count1353 b) else decide (6 ≤ count1353 b)))) else (if i < 1362 then (if i < 1360 then decide (7 ≤ count1353 b) else (if i < 1361 then decide (1 ≤ count1360 b) else decide (2 ≤ count1360 b))) else (if i < 1363 then decide (1 ≤ count1362 b) else (if i < 1364 then decide (2 ≤ count1362 b) else decide (3 ≤ count1362 b))))) else (if i < 1371 then (if i < 1368 then (if i < 1366 then decide (1 ≤ count1365 b) else (if i < 1367 then decide (2 ≤ count1365 b) else decide (1 ≤ count1367 b))) else (if i < 1369 then decide (2 ≤ count1367 b) else (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)))) else (if i < 1374 then (if i < 1372 then decide (3 ≤ count1369 b) else (if i < 1373 then decide (4 ≤ count1369 b) else decide (1 ≤ count1373 b))) else (if i < 1375 then decide (2 ≤ count1373 b) else (if i < 1376 then decide (3 ≤ count1373 b) else decide (4 ≤ count1373 b)))))) else (if i < 1389 then (if i < 1383 then (if i < 1380 then (if i < 1378 then decide (5 ≤ count1373 b) else (if i < 1379 then decide (6 ≤ count1373 b) else decide (7 ≤ count1373 b))) else (if i < 1381 then decide (1 ≤ count1380 b) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (3 ≤ count1380 b)))) else (if i < 1386 then (if i < 1384 then decide (4 ≤ count1380 b) else (if i < 1385 then decide (5 ≤ count1380 b) else decide (6 ≤ count1380 b))) else (if i < 1387 then decide (7 ≤ count1380 b) else (if i < 1388 then decide (8 ≤ count1380 b) else decide (9 ≤ count1380 b))))) else (if i < 1395 then (if i < 1392 then (if i < 1390 then decide (10 ≤ count1380 b) else (if i < 1391 then decide (11 ≤ count1380 b) else decide (12 ≤ count1380 b))) else (if i < 1393 then decide (13 ≤ count1380 b) else (if i < 1394 then decide (14 ≤ count1380 b) else decide (1 ≤ count1394 b)))) else (if i < 1398 then (if i < 1396 then decide (2 ≤ count1394 b) else (if i < 1397 then decide (3 ≤ count1394 b) else decide (4 ≤ count1394 b))) else (if i < 1399 then decide (5 ≤ count1394 b) else (if i < 1400 then decide (6 ≤ count1394 b) else decide (7 ≤ count1394 b))))))) else (if i < 1425 then (if i < 1413 then (if i < 1407 then (if i < 1404 then (if i < 1402 then decide (8 ≤ count1394 b) else (if i < 1403 then decide (9 ≤ count1394 b) else decide (10 ≤ count1394 b))) else (if i < 1405 then decide (11 ≤ count1394 b) else (if i < 1406 then decide (12 ≤ count1394 b) else decide (13 ≤ count1394 b)))) else (if i < 1410 then (if i < 1408 then decide (14 ≤ count1394 b) else (if i < 1409 then decide (15 ≤ count1394 b) else decide (1 ≤ count1409 b))) else (if i < 1411 then decide (2 ≤ count1409 b) else (if i < 1412 then decide (1 ≤ count1411 b) else decide (2 ≤ count1411 b))))) else (if i < 1419 then (if i < 1416 then (if i < 1414 then decide (3 ≤ count1411 b) else (if i < 1415 then decide (1 ≤ count1414 b) else decide (2 ≤ count1414 b))) else (if i < 1417 then decide (1 ≤ count1416 b) else (if i < 1418 then decide (2 ≤ count1416 b) else decide (1 ≤ count1418 b)))) else (if i < 1422 then (if i < 1420 then decide (2 ≤ count1418 b) else (if i < 1421 then decide (3 ≤ count1418 b) else decide (4 ≤ count1418 b))) else (if i < 1423 then decide (1 ≤ count1422 b) else (if i < 1424 then decide (2 ≤ count1422 b) else decide (3 ≤ count1422 b)))))) else (if i < 1437 then (if i < 1431 then (if i < 1428 then (if i < 1426 then decide (4 ≤ count1422 b) else (if i < 1427 then decide (5 ≤ count1422 b) else decide (6 ≤ count1422 b))) else (if i < 1429 then decide (7 ≤ count1422 b) else (if i < 1430 then decide (1 ≤ count1429 b) else decide (2 ≤ count1429 b)))) else (if i < 1434 then (if i < 1432 then decide (1 ≤ count1431 b) else (if i < 1433 then decide (2 ≤ count1431 b) else decide (3 ≤ count1431 b))) else (if i < 1435 then decide (1 ≤ count1434 b) else (if i < 1436 then decide (2 ≤ count1434 b) else decide (1 ≤ count1436 b))))) else (if i < 1443 then (if i < 1440 then (if i < 1438 then decide (2 ≤ count1436 b) else (if i < 1439 then decide (1 ≤ count1438 b) else decide (2 ≤ count1438 b))) else (if i < 1441 then decide (3 ≤ count1438 b) else (if i < 1442 then decide (4 ≤ count1438 b) else decide (1 ≤ count1442 b)))) else (if i < 1446 then (if i < 1444 then decide (2 ≤ count1442 b) else (if i < 1445 then decide (3 ≤ count1442 b) else decide (4 ≤ count1442 b))) else (if i < 1448 then (if i < 1447 then decide (5 ≤ count1442 b) else decide (6 ≤ count1442 b)) else (if i < 1449 then decide (7 ≤ count1442 b) else decide (1 ≤ count1449 b)))))))) else (if i < 1498 then (if i < 1474 then (if i < 1462 then (if i < 1456 then (if i < 1453 then (if i < 1451 then decide (2 ≤ count1449 b) else (if i < 1452 then decide (3 ≤ count1449 b) else decide (4 ≤ count1449 b))) else (if i < 1454 then decide (5 ≤ count1449 b) else (if i < 1455 then decide (6 ≤ count1449 b) else decide (7 ≤ count1449 b)))) else (if i < 1459 then (if i < 1457 then decide (8 ≤ count1449 b) else (if i < 1458 then decide (9 ≤ count1449 b) else decide (10 ≤ count1449 b))) else (if i < 1460 then decide (11 ≤ count1449 b) else (if i < 1461 then decide (12 ≤ count1449 b) else decide (13 ≤ count1449 b))))) else (if i < 1468 then (if i < 1465 then (if i < 1463 then decide (14 ≤ count1449 b) else (if i < 1464 then decide (1 ≤ count1463 b) else decide (2 ≤ count1463 b))) else (if i < 1466 then decide (1 ≤ count1465 b) else (if i < 1467 then decide (2 ≤ count1465 b) else decide (3 ≤ count1465 b)))) else (if i < 1471 then (if i < 1469 then decide (1 ≤ count1468 b) else (if i < 1470 then decide (2 ≤ count1468 b) else decide (1 ≤ count1470 b))) else (if i < 1472 then decide (2 ≤ count1470 b) else (if i < 1473 then decide (1 ≤ count1472 b) else decide (2 ≤ count1472 b)))))) else (if i < 1486 then (if i < 1480 then (if i < 1477 then (if i < 1475 then decide (3 ≤ count1472 b) else (if i < 1476 then decide (4 ≤ count1472 b) else decide (1 ≤ count1476 b))) else (if i < 1478 then decide (2 ≤ count1476 b) else (if i < 1479 then decide (3 ≤ count1476 b) else decide (4 ≤ count1476 b)))) else (if i < 1483 then (if i < 1481 then decide (5 ≤ count1476 b) else (if i < 1482 then decide (6 ≤ count1476 b) else decide (7 ≤ count1476 b))) else (if i < 1484 then decide (1 ≤ count1483 b) else (if i < 1485 then decide (2 ≤ count1483 b) else decide (1 ≤ count1485 b))))) else (if i < 1492 then (if i < 1489 then (if i < 1487 then decide (2 ≤ count1485 b) else (if i < 1488 then decide (3 ≤ count1485 b) else decide (1 ≤ count1488 b))) else (if i < 1490 then decide (2 ≤ count1488 b) else (if i < 1491 then decide (1 ≤ count1490 b) else decide (2 ≤ count1490 b)))) else (if i < 1495 then (if i < 1493 then decide (1 ≤ count1492 b) else (if i < 1494 then decide (2 ≤ count1492 b) else decide (3 ≤ count1492 b))) else (if i < 1496 then decide (4 ≤ count1492 b) else (if i < 1497 then decide (1 ≤ count1496 b) else decide (2 ≤ count1496 b))))))) else (if i < 1522 then (if i < 1510 then (if i < 1504 then (if i < 1501 then (if i < 1499 then decide (3 ≤ count1496 b) else (if i < 1500 then decide (4 ≤ count1496 b) else decide (5 ≤ count1496 b))) else (if i < 1502 then decide (6 ≤ count1496 b) else (if i < 1503 then decide (7 ≤ count1496 b) else decide (1 ≤ count1503 b)))) else (if i < 1507 then (if i < 1505 then decide (2 ≤ count1503 b) else (if i < 1506 then decide (3 ≤ count1503 b) else decide (4 ≤ count1503 b))) else (if i < 1508 then decide (5 ≤ count1503 b) else (if i < 1509 then decide (6 ≤ count1503 b) else decide (7 ≤ count1503 b))))) else (if i < 1516 then (if i < 1513 then (if i < 1511 then decide (8 ≤ count1503 b) else (if i < 1512 then decide (9 ≤ count1503 b) else decide (10 ≤ count1503 b))) else (if i < 1514 then decide (11 ≤ count1503 b) else (if i < 1515 then decide (12 ≤ count1503 b) else decide (13 ≤ count1503 b)))) else (if i < 1519 then (if i < 1517 then decide (14 ≤ count1503 b) else (if i < 1518 then decide (1 ≤ count1517 b) else decide (2 ≤ count1517 b))) else (if i < 1520 then decide (3 ≤ count1517 b) else (if i < 1521 then decide (4 ≤ count1517 b) else decide (5 ≤ count1517 b)))))) else (if i < 1534 then (if i < 1528 then (if i < 1525 then (if i < 1523 then decide (6 ≤ count1517 b) else (if i < 1524 then decide (7 ≤ count1517 b) else decide (8 ≤ count1517 b))) else (if i < 1526 then decide (9 ≤ count1517 b) else (if i < 1527 then decide (10 ≤ count1517 b) else decide (11 ≤ count1517 b)))) else (if i < 1531 then (if i < 1529 then decide (12 ≤ count1517 b) else (if i < 1530 then decide (13 ≤ count1517 b) else decide (14 ≤ count1517 b))) else (if i < 1532 then decide (15 ≤ count1517 b) else (if i < 1533 then decide (1 ≤ count1532 b) else decide (2 ≤ count1532 b))))) else (if i < 1540 then (if i < 1537 then (if i < 1535 then decide (3 ≤ count1532 b) else (if i < 1536 then decide (4 ≤ count1532 b) else decide (5 ≤ count1532 b))) else (if i < 1538 then decide (6 ≤ count1532 b) else (if i < 1539 then decide (7 ≤ count1532 b) else decide (8 ≤ count1532 b)))) else (if i < 1543 then (if i < 1541 then decide (9 ≤ count1532 b) else (if i < 1542 then decide (10 ≤ count1532 b) else decide (11 ≤ count1532 b))) else (if i < 1545 then (if i < 1544 then decide (12 ≤ count1532 b) else decide (13 ≤ count1532 b)) else (if i < 1546 then decide (14 ≤ count1532 b) else decide (15 ≤ count1532 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (99 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (106 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (107 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (117 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (118 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (119 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (120 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (121 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (122 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (125 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (129 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (130 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (131 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (133 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (135 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (137 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (139 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (140 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (141 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (143 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (144 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (145 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (146 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (148 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (150 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (156 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (158 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (159 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (194 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (195 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (196 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (205 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (209 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (213 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (214 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (215 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (221 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (227 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (229 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (231 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (233 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (237 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (257 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (259 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (261 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (263 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (265 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (267 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (268 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (269 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (271 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (272 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (273 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (274 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (276 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (284 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (286 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (287 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (320 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (322 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (323 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (324 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (326 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (330 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (331 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (332 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (333 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (337 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (341 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (342 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (343 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (344 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (345 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (346 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (349 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (384 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (386 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (387 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (388 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (390 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (394 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (395 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (396 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (397 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (401 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (405 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (406 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (407 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (408 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (409 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (410 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (413 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (482 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (483 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (484 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (486 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (490 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (491 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (492 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (493 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (501 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (502 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (505 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (506 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (509 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (BallClauseLogic.Endpoint q (99 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (BallClauseLogic.Endpoint q (106 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (107 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (117 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (119 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (120 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (121 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (122 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (143 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (146 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (194 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (196 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (209 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (213 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (215 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (231 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (233 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (237 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (263 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (271 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (273 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (284 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (286 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (323 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (324 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (326 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (330 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (343 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (344 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (388 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (390 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (394 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (395 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (396 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (405 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (408 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (483 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (484 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (491 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (1 ≤ count219 (baseVal q)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (1 ≤ count221 (baseVal q)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (1 ≤ count227 (baseVal q)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (1 ≤ count229 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value268 (q : Snake 81) : valuation q 268 = decide (2 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value320 (q : Snake 81) : valuation q 320 = decide (2 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value322 (q : Snake 81) : valuation q 322 = decide (2 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value338 (q : Snake 81) : valuation q 338 = decide (2 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value398 (q : Snake 81) : valuation q 398 = decide (2 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value430 (q : Snake 81) : valuation q 430 = decide (2 ≤ count429 (baseVal q)) := rfl
theorem value432 (q : Snake 81) : valuation q 432 = decide (2 ≤ count431 (baseVal q)) := rfl
theorem value1293 (q : Snake 81) : valuation q 1293 = decide (1 ≤ count1293 (baseVal q)) := rfl
theorem value1296 (q : Snake 81) : valuation q 1296 = decide (1 ≤ count1296 (baseVal q)) := rfl
theorem value1298 (q : Snake 81) : valuation q 1298 = decide (1 ≤ count1298 (baseVal q)) := rfl
theorem value1301 (q : Snake 81) : valuation q 1301 = decide (1 ≤ count1301 (baseVal q)) := rfl
theorem value1302 (q : Snake 81) : valuation q 1302 = decide (2 ≤ count1301 (baseVal q)) := rfl
theorem value1307 (q : Snake 81) : valuation q 1307 = decide (1 ≤ count1307 (baseVal q)) := rfl
theorem value1308 (q : Snake 81) : valuation q 1308 = decide (2 ≤ count1307 (baseVal q)) := rfl
theorem value1309 (q : Snake 81) : valuation q 1309 = decide (1 ≤ count1309 (baseVal q)) := rfl
theorem value1310 (q : Snake 81) : valuation q 1310 = decide (2 ≤ count1309 (baseVal q)) := rfl
theorem value1311 (q : Snake 81) : valuation q 1311 = decide (3 ≤ count1309 (baseVal q)) := rfl
theorem value1312 (q : Snake 81) : valuation q 1312 = decide (1 ≤ count1312 (baseVal q)) := rfl
theorem value1313 (q : Snake 81) : valuation q 1313 = decide (2 ≤ count1312 (baseVal q)) := rfl
theorem value1314 (q : Snake 81) : valuation q 1314 = decide (1 ≤ count1314 (baseVal q)) := rfl
theorem value1315 (q : Snake 81) : valuation q 1315 = decide (2 ≤ count1314 (baseVal q)) := rfl
theorem value1316 (q : Snake 81) : valuation q 1316 = decide (1 ≤ count1316 (baseVal q)) := rfl
theorem value1317 (q : Snake 81) : valuation q 1317 = decide (2 ≤ count1316 (baseVal q)) := rfl
theorem value1318 (q : Snake 81) : valuation q 1318 = decide (3 ≤ count1316 (baseVal q)) := rfl
theorem value1320 (q : Snake 81) : valuation q 1320 = decide (1 ≤ count1320 (baseVal q)) := rfl
theorem value1321 (q : Snake 81) : valuation q 1321 = decide (2 ≤ count1320 (baseVal q)) := rfl
theorem value1322 (q : Snake 81) : valuation q 1322 = decide (3 ≤ count1320 (baseVal q)) := rfl
theorem value1323 (q : Snake 81) : valuation q 1323 = decide (4 ≤ count1320 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (1 ≤ count1327 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (2 ≤ count1327 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (3 ≤ count1327 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (4 ≤ count1327 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (1 ≤ count1340 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (2 ≤ count1340 (baseVal q)) := rfl
theorem value1342 (q : Snake 81) : valuation q 1342 = decide (1 ≤ count1342 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (2 ≤ count1342 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (3 ≤ count1342 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (1 ≤ count1345 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (2 ≤ count1345 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (1 ≤ count1347 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (1 ≤ count1349 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (2 ≤ count1349 (baseVal q)) := rfl
theorem value1351 (q : Snake 81) : valuation q 1351 = decide (3 ≤ count1349 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (1 ≤ count1353 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (2 ≤ count1353 (baseVal q)) := rfl
theorem value1355 (q : Snake 81) : valuation q 1355 = decide (3 ≤ count1353 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (4 ≤ count1353 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (5 ≤ count1353 (baseVal q)) := rfl
theorem value1360 (q : Snake 81) : valuation q 1360 = decide (1 ≤ count1360 (baseVal q)) := rfl
theorem value1361 (q : Snake 81) : valuation q 1361 = decide (2 ≤ count1360 (baseVal q)) := rfl
theorem value1362 (q : Snake 81) : valuation q 1362 = decide (1 ≤ count1362 (baseVal q)) := rfl
theorem value1363 (q : Snake 81) : valuation q 1363 = decide (2 ≤ count1362 (baseVal q)) := rfl
theorem value1364 (q : Snake 81) : valuation q 1364 = decide (3 ≤ count1362 (baseVal q)) := rfl
theorem value1365 (q : Snake 81) : valuation q 1365 = decide (1 ≤ count1365 (baseVal q)) := rfl
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (2 ≤ count1365 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (1 ≤ count1367 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (2 ≤ count1367 (baseVal q)) := rfl
theorem value1369 (q : Snake 81) : valuation q 1369 = decide (1 ≤ count1369 (baseVal q)) := rfl
theorem value1370 (q : Snake 81) : valuation q 1370 = decide (2 ≤ count1369 (baseVal q)) := rfl
theorem value1371 (q : Snake 81) : valuation q 1371 = decide (3 ≤ count1369 (baseVal q)) := rfl
theorem value1372 (q : Snake 81) : valuation q 1372 = decide (4 ≤ count1369 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (2 ≤ count1373 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (3 ≤ count1373 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (4 ≤ count1373 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (5 ≤ count1373 (baseVal q)) := rfl
theorem value1378 (q : Snake 81) : valuation q 1378 = decide (6 ≤ count1373 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (3 ≤ count1380 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (4 ≤ count1380 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (5 ≤ count1380 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (6 ≤ count1380 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (7 ≤ count1380 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (8 ≤ count1380 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (5 ≤ count1394 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (6 ≤ count1394 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (7 ≤ count1394 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (8 ≤ count1394 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (9 ≤ count1394 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (10 ≤ count1394 (baseVal q)) := rfl
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
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (1 ≤ count1434 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (2 ≤ count1434 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (1 ≤ count1436 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (2 ≤ count1436 (baseVal q)) := rfl
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
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (4 ≤ count1472 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (1 ≤ count1476 (baseVal q)) := rfl
theorem value1477 (q : Snake 81) : valuation q 1477 = decide (2 ≤ count1476 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (3 ≤ count1476 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (4 ≤ count1476 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (5 ≤ count1476 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (6 ≤ count1476 (baseVal q)) := rfl
theorem value1483 (q : Snake 81) : valuation q 1483 = decide (1 ≤ count1483 (baseVal q)) := rfl
theorem value1484 (q : Snake 81) : valuation q 1484 = decide (2 ≤ count1483 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (1 ≤ count1485 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (3 ≤ count1485 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (1 ≤ count1488 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (1 ≤ count1490 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (1 ≤ count1492 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (1 ≤ count1496 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (2 ≤ count1496 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (3 ≤ count1496 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (1 ≤ count1503 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (2 ≤ count1503 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (3 ≤ count1503 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (4 ≤ count1503 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (5 ≤ count1503 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (6 ≤ count1503 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (5 ≤ count1517 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (6 ≤ count1517 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (7 ≤ count1517 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (8 ≤ count1517 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (9 ≤ count1517 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (10 ≤ count1517 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (15 ≤ count1532 (baseVal q)) := rfl
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
theorem meaningNeg99 (b : Nat → Bool) : literal (valuationOf b) (-99) = decide (1 ≤ countLit b [-99]) := by
  change literal b (-99) = decide (1 ≤ countLit b [-99])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-99) <;> decide
theorem meaningNeg96 (b : Nat → Bool) : literal (valuationOf b) (-96) = decide (1 ≤ countLit b [-96]) := by
  change literal b (-96) = decide (1 ≤ countLit b [-96])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-96) <;> decide
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
theorem meaningNeg91 (b : Nat → Bool) : literal (valuationOf b) (-91) = decide (1 ≤ countLit b [-91]) := by
  change literal b (-91) = decide (1 ≤ countLit b [-91])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-91) <;> decide
theorem meaningNeg88 (b : Nat → Bool) : literal (valuationOf b) (-88) = decide (1 ≤ countLit b [-88]) := by
  change literal b (-88) = decide (1 ≤ countLit b [-88])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-88) <;> decide
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
theorem meaningNeg83 (b : Nat → Bool) : literal (valuationOf b) (-83) = decide (1 ≤ countLit b [-83]) := by
  change literal b (-83) = decide (1 ≤ countLit b [-83])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-83) <;> decide
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
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
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
theorem meaningNeg9 (b : Nat → Bool) : literal (valuationOf b) (-9) = decide (1 ≤ countLit b [-9]) := by
  change literal b (-9) = decide (1 ≤ countLit b [-9])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-9) <;> decide
theorem meaningNeg3 (b : Nat → Bool) : literal (valuationOf b) (-3) = decide (1 ≤ countLit b [-3]) := by
  change literal b (-3) = decide (1 ≤ countLit b [-3])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-3) <;> decide
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
theorem meaning115 (b : Nat → Bool) : literal (valuationOf b) (115) = decide (1 ≤ countLit b [115]) := by
  change literal b (115) = decide (1 ≤ countLit b [115])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (115) <;> decide
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
theorem meaning124 (b : Nat → Bool) : literal (valuationOf b) (124) = decide (1 ≤ countLit b [124]) := by
  change literal b (124) = decide (1 ≤ countLit b [124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (124) <;> decide
theorem meaning130 (b : Nat → Bool) : literal (valuationOf b) (130) = decide (1 ≤ countLit b [130]) := by
  change literal b (130) = decide (1 ≤ countLit b [130])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (130) <;> decide
theorem meaning137 (b : Nat → Bool) : literal (valuationOf b) (137) = decide (1 ≤ countLit b [137]) := by
  change literal b (137) = decide (1 ≤ countLit b [137])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (137) <;> decide
theorem meaning143 (b : Nat → Bool) : literal (valuationOf b) (143) = decide (1 ≤ countLit b [143]) := by
  change literal b (143) = decide (1 ≤ countLit b [143])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (143) <;> decide
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
theorem meaning153 (b : Nat → Bool) : literal (valuationOf b) (153) = decide (1 ≤ countLit b [153]) := by
  change literal b (153) = decide (1 ≤ countLit b [153])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (153) <;> decide
theorem meaning156 (b : Nat → Bool) : literal (valuationOf b) (156) = decide (1 ≤ countLit b [156]) := by
  change literal b (156) = decide (1 ≤ countLit b [156])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (156) <;> decide
theorem meaning162 (b : Nat → Bool) : literal (valuationOf b) (162) = decide (1 ≤ countLit b [162]) := by
  change literal b (162) = decide (1 ≤ countLit b [162])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (162) <;> decide
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
theorem meaning174 (b : Nat → Bool) : literal (valuationOf b) (174) = decide (1 ≤ countLit b [174]) := by
  change literal b (174) = decide (1 ≤ countLit b [174])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (174) <;> decide
theorem meaning176 (b : Nat → Bool) : literal (valuationOf b) (176) = decide (1 ≤ countLit b [176]) := by
  change literal b (176) = decide (1 ≤ countLit b [176])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (176) <;> decide
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
theorem meaning182 (b : Nat → Bool) : literal (valuationOf b) (182) = decide (1 ≤ countLit b [182]) := by
  change literal b (182) = decide (1 ≤ countLit b [182])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (182) <;> decide
theorem meaning186 (b : Nat → Bool) : literal (valuationOf b) (186) = decide (1 ≤ countLit b [186]) := by
  change literal b (186) = decide (1 ≤ countLit b [186])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (186) <;> decide
theorem meaning190 (b : Nat → Bool) : literal (valuationOf b) (190) = decide (1 ≤ countLit b [190]) := by
  change literal b (190) = decide (1 ≤ countLit b [190])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (190) <;> decide
theorem meaning191 (b : Nat → Bool) : literal (valuationOf b) (191) = decide (1 ≤ countLit b [191]) := by
  change literal b (191) = decide (1 ≤ countLit b [191])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (191) <;> decide
theorem meaning193 (b : Nat → Bool) : literal (valuationOf b) (193) = decide (1 ≤ countLit b [193]) := by
  change literal b (193) = decide (1 ≤ countLit b [193])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (193) <;> decide
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
theorem meaning199 (b : Nat → Bool) : literal (valuationOf b) (199) = decide (1 ≤ countLit b [199]) := by
  change literal b (199) = decide (1 ≤ countLit b [199])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (199) <;> decide
theorem meaning202 (b : Nat → Bool) : literal (valuationOf b) (202) = decide (1 ≤ countLit b [202]) := by
  change literal b (202) = decide (1 ≤ countLit b [202])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (202) <;> decide
theorem meaning204 (b : Nat → Bool) : literal (valuationOf b) (204) = decide (1 ≤ countLit b [204]) := by
  change literal b (204) = decide (1 ≤ countLit b [204])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (204) <;> decide
theorem meaning209 (b : Nat → Bool) : literal (valuationOf b) (209) = decide (1 ≤ countLit b [209]) := by
  change literal b (209) = decide (1 ≤ countLit b [209])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (209) <;> decide
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) 219 = decide (1 ≤ count219 b) := rfl
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) 221 = decide (1 ≤ count221 b) := rfl
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) 227 = decide (1 ≤ count227 b) := rfl
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) 229 = decide (1 ≤ count229 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning268 (b : Nat → Bool) : literal (valuationOf b) 268 = decide (2 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning320 (b : Nat → Bool) : literal (valuationOf b) 320 = decide (2 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning322 (b : Nat → Bool) : literal (valuationOf b) 322 = decide (2 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning338 (b : Nat → Bool) : literal (valuationOf b) 338 = decide (2 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning398 (b : Nat → Bool) : literal (valuationOf b) 398 = decide (2 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning430 (b : Nat → Bool) : literal (valuationOf b) 430 = decide (2 ≤ count429 b) := rfl
theorem meaning432 (b : Nat → Bool) : literal (valuationOf b) 432 = decide (2 ≤ count431 b) := rfl
theorem meaning1293 (b : Nat → Bool) : literal (valuationOf b) 1293 = decide (1 ≤ count1293 b) := rfl
theorem meaning1296 (b : Nat → Bool) : literal (valuationOf b) 1296 = decide (1 ≤ count1296 b) := rfl
theorem meaning1298 (b : Nat → Bool) : literal (valuationOf b) 1298 = decide (1 ≤ count1298 b) := rfl
theorem meaning1301 (b : Nat → Bool) : literal (valuationOf b) 1301 = decide (1 ≤ count1301 b) := rfl
theorem meaning1302 (b : Nat → Bool) : literal (valuationOf b) 1302 = decide (2 ≤ count1301 b) := rfl
theorem meaning1307 (b : Nat → Bool) : literal (valuationOf b) 1307 = decide (1 ≤ count1307 b) := rfl
theorem meaning1308 (b : Nat → Bool) : literal (valuationOf b) 1308 = decide (2 ≤ count1307 b) := rfl
theorem meaning1309 (b : Nat → Bool) : literal (valuationOf b) 1309 = decide (1 ≤ count1309 b) := rfl
theorem meaning1310 (b : Nat → Bool) : literal (valuationOf b) 1310 = decide (2 ≤ count1309 b) := rfl
theorem meaning1311 (b : Nat → Bool) : literal (valuationOf b) 1311 = decide (3 ≤ count1309 b) := rfl
theorem meaning1312 (b : Nat → Bool) : literal (valuationOf b) 1312 = decide (1 ≤ count1312 b) := rfl
theorem meaning1313 (b : Nat → Bool) : literal (valuationOf b) 1313 = decide (2 ≤ count1312 b) := rfl
theorem meaning1314 (b : Nat → Bool) : literal (valuationOf b) 1314 = decide (1 ≤ count1314 b) := rfl
theorem meaning1315 (b : Nat → Bool) : literal (valuationOf b) 1315 = decide (2 ≤ count1314 b) := rfl
theorem meaning1316 (b : Nat → Bool) : literal (valuationOf b) 1316 = decide (1 ≤ count1316 b) := rfl
theorem meaning1317 (b : Nat → Bool) : literal (valuationOf b) 1317 = decide (2 ≤ count1316 b) := rfl
theorem meaning1318 (b : Nat → Bool) : literal (valuationOf b) 1318 = decide (3 ≤ count1316 b) := rfl
theorem meaning1320 (b : Nat → Bool) : literal (valuationOf b) 1320 = decide (1 ≤ count1320 b) := rfl
theorem meaning1321 (b : Nat → Bool) : literal (valuationOf b) 1321 = decide (2 ≤ count1320 b) := rfl
theorem meaning1322 (b : Nat → Bool) : literal (valuationOf b) 1322 = decide (3 ≤ count1320 b) := rfl
theorem meaning1323 (b : Nat → Bool) : literal (valuationOf b) 1323 = decide (4 ≤ count1320 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (1 ≤ count1327 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (2 ≤ count1327 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (3 ≤ count1327 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (4 ≤ count1327 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (1 ≤ count1340 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (2 ≤ count1340 b) := rfl
theorem meaning1342 (b : Nat → Bool) : literal (valuationOf b) 1342 = decide (1 ≤ count1342 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (2 ≤ count1342 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (3 ≤ count1342 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (1 ≤ count1345 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (2 ≤ count1345 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (1 ≤ count1347 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (1 ≤ count1349 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (2 ≤ count1349 b) := rfl
theorem meaning1351 (b : Nat → Bool) : literal (valuationOf b) 1351 = decide (3 ≤ count1349 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (1 ≤ count1353 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (2 ≤ count1353 b) := rfl
theorem meaning1355 (b : Nat → Bool) : literal (valuationOf b) 1355 = decide (3 ≤ count1353 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (4 ≤ count1353 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (5 ≤ count1353 b) := rfl
theorem meaning1360 (b : Nat → Bool) : literal (valuationOf b) 1360 = decide (1 ≤ count1360 b) := rfl
theorem meaning1361 (b : Nat → Bool) : literal (valuationOf b) 1361 = decide (2 ≤ count1360 b) := rfl
theorem meaning1362 (b : Nat → Bool) : literal (valuationOf b) 1362 = decide (1 ≤ count1362 b) := rfl
theorem meaning1363 (b : Nat → Bool) : literal (valuationOf b) 1363 = decide (2 ≤ count1362 b) := rfl
theorem meaning1364 (b : Nat → Bool) : literal (valuationOf b) 1364 = decide (3 ≤ count1362 b) := rfl
theorem meaning1365 (b : Nat → Bool) : literal (valuationOf b) 1365 = decide (1 ≤ count1365 b) := rfl
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (2 ≤ count1365 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (1 ≤ count1367 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (2 ≤ count1367 b) := rfl
theorem meaning1369 (b : Nat → Bool) : literal (valuationOf b) 1369 = decide (1 ≤ count1369 b) := rfl
theorem meaning1370 (b : Nat → Bool) : literal (valuationOf b) 1370 = decide (2 ≤ count1369 b) := rfl
theorem meaning1371 (b : Nat → Bool) : literal (valuationOf b) 1371 = decide (3 ≤ count1369 b) := rfl
theorem meaning1372 (b : Nat → Bool) : literal (valuationOf b) 1372 = decide (4 ≤ count1369 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (2 ≤ count1373 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (3 ≤ count1373 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (4 ≤ count1373 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (5 ≤ count1373 b) := rfl
theorem meaning1378 (b : Nat → Bool) : literal (valuationOf b) 1378 = decide (6 ≤ count1373 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (3 ≤ count1380 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (4 ≤ count1380 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (5 ≤ count1380 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (6 ≤ count1380 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (7 ≤ count1380 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (8 ≤ count1380 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (5 ≤ count1394 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (6 ≤ count1394 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (7 ≤ count1394 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (8 ≤ count1394 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (9 ≤ count1394 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (10 ≤ count1394 b) := rfl
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
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (1 ≤ count1434 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (2 ≤ count1434 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (1 ≤ count1436 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (2 ≤ count1436 b) := rfl
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
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (4 ≤ count1472 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (1 ≤ count1476 b) := rfl
theorem meaning1477 (b : Nat → Bool) : literal (valuationOf b) 1477 = decide (2 ≤ count1476 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (3 ≤ count1476 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (4 ≤ count1476 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (5 ≤ count1476 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (6 ≤ count1476 b) := rfl
theorem meaning1483 (b : Nat → Bool) : literal (valuationOf b) 1483 = decide (1 ≤ count1483 b) := rfl
theorem meaning1484 (b : Nat → Bool) : literal (valuationOf b) 1484 = decide (2 ≤ count1483 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (1 ≤ count1485 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (2 ≤ count1485 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (3 ≤ count1485 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (1 ≤ count1488 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (1 ≤ count1490 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (1 ≤ count1492 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (1 ≤ count1496 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (2 ≤ count1496 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (3 ≤ count1496 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (1 ≤ count1503 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (2 ≤ count1503 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (3 ≤ count1503 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (4 ≤ count1503 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (5 ≤ count1503 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (6 ≤ count1503 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (5 ≤ count1517 b) := rfl
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
end Snake9.Regrowth.E112090
