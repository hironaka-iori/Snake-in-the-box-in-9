import E112148Data
namespace Snake9.Regrowth.E112148
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 111 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (11 : Vertex)) else decide (InPath q (25 : Vertex)))) else (if i < 4 then decide (InPath q (27 : Vertex)) else (if i < 5 then decide (InPath q (65 : Vertex)) else decide (InPath q (66 : Vertex))))) else (if i < 9 then (if i < 7 then decide (InPath q (67 : Vertex)) else (if i < 8 then decide (InPath q (71 : Vertex)) else decide (InPath q (75 : Vertex)))) else (if i < 11 then (if i < 10 then decide (InPath q (77 : Vertex)) else decide (InPath q (79 : Vertex))) else (if i < 12 then decide (InPath q (80 : Vertex)) else decide (InPath q (81 : Vertex)))))) else (if i < 20 then (if i < 16 then (if i < 14 then decide (InPath q (82 : Vertex)) else (if i < 15 then decide (InPath q (83 : Vertex)) else decide (InPath q (84 : Vertex)))) else (if i < 18 then (if i < 17 then decide (InPath q (88 : Vertex)) else decide (InPath q (90 : Vertex))) else (if i < 19 then decide (InPath q (91 : Vertex)) else decide (InPath q (92 : Vertex))))) else (if i < 23 then (if i < 21 then decide (InPath q (94 : Vertex)) else (if i < 22 then decide (InPath q (95 : Vertex)) else decide (InPath q (129 : Vertex)))) else (if i < 25 then (if i < 24 then decide (InPath q (130 : Vertex)) else decide (InPath q (131 : Vertex))) else (if i < 26 then decide (InPath q (135 : Vertex)) else decide (InPath q (137 : Vertex))))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then decide (InPath q (141 : Vertex)) else (if i < 29 then decide (InPath q (143 : Vertex)) else decide (InPath q (144 : Vertex)))) else (if i < 32 then (if i < 31 then decide (InPath q (145 : Vertex)) else decide (InPath q (146 : Vertex))) else (if i < 33 then decide (InPath q (147 : Vertex)) else decide (InPath q (148 : Vertex))))) else (if i < 37 then (if i < 35 then decide (InPath q (154 : Vertex)) else (if i < 36 then decide (InPath q (156 : Vertex)) else decide (InPath q (157 : Vertex)))) else (if i < 39 then (if i < 38 then decide (InPath q (158 : Vertex)) else decide (InPath q (159 : Vertex))) else (if i < 40 then decide (InPath q (192 : Vertex)) else decide (InPath q (193 : Vertex)))))) else (if i < 48 then (if i < 44 then (if i < 42 then decide (InPath q (198 : Vertex)) else (if i < 43 then decide (InPath q (199 : Vertex)) else decide (InPath q (200 : Vertex)))) else (if i < 46 then (if i < 45 then decide (InPath q (201 : Vertex)) else decide (InPath q (203 : Vertex))) else (if i < 47 then decide (InPath q (204 : Vertex)) else decide (InPath q (206 : Vertex))))) else (if i < 51 then (if i < 49 then decide (InPath q (210 : Vertex)) else (if i < 50 then decide (InPath q (213 : Vertex)) else decide (InPath q (214 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (215 : Vertex)) else decide (InPath q (217 : Vertex))) else (if i < 54 then decide (InPath q (218 : Vertex)) else decide (InPath q (219 : Vertex)))))))) else (if i < 83 then (if i < 69 then (if i < 62 then (if i < 58 then (if i < 56 then decide (InPath q (221 : Vertex)) else (if i < 57 then decide (InPath q (288 : Vertex)) else decide (InPath q (289 : Vertex)))) else (if i < 60 then (if i < 59 then decide (InPath q (294 : Vertex)) else decide (InPath q (296 : Vertex))) else (if i < 61 then decide (InPath q (300 : Vertex)) else decide (InPath q (302 : Vertex))))) else (if i < 65 then (if i < 63 then decide (InPath q (310 : Vertex)) else (if i < 64 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex)))) else (if i < 67 then (if i < 66 then decide (InPath q (326 : Vertex)) else decide (InPath q (327 : Vertex))) else (if i < 68 then decide (InPath q (328 : Vertex)) else decide (InPath q (329 : Vertex)))))) else (if i < 76 then (if i < 72 then (if i < 70 then decide (InPath q (331 : Vertex)) else (if i < 71 then decide (InPath q (332 : Vertex)) else decide (InPath q (334 : Vertex)))) else (if i < 74 then (if i < 73 then decide (InPath q (338 : Vertex)) else decide (InPath q (340 : Vertex))) else (if i < 75 then decide (InPath q (341 : Vertex)) else decide (InPath q (342 : Vertex))))) else (if i < 79 then (if i < 77 then decide (InPath q (343 : Vertex)) else (if i < 78 then decide (InPath q (345 : Vertex)) else decide (InPath q (346 : Vertex)))) else (if i < 81 then (if i < 80 then decide (InPath q (347 : Vertex)) else decide (InPath q (349 : Vertex))) else (if i < 82 then decide (InPath q (385 : Vertex)) else decide (InPath q (391 : Vertex))))))) else (if i < 97 then (if i < 90 then (if i < 86 then (if i < 84 then decide (InPath q (393 : Vertex)) else (if i < 85 then decide (InPath q (402 : Vertex)) else decide (InPath q (405 : Vertex)))) else (if i < 88 then (if i < 87 then decide (InPath q (406 : Vertex)) else decide (InPath q (407 : Vertex))) else (if i < 89 then decide (InPath q (409 : Vertex)) else decide (InPath q (411 : Vertex))))) else (if i < 93 then (if i < 91 then decide (InPath q (413 : Vertex)) else (if i < 92 then decide (InPath q (417 : Vertex)) else decide (InPath q (418 : Vertex)))) else (if i < 95 then (if i < 94 then decide (InPath q (433 : Vertex)) else decide (InPath q (434 : Vertex))) else (if i < 96 then decide (InPath q (435 : Vertex)) else decide (InPath q (480 : Vertex)))))) else (if i < 104 then (if i < 100 then (if i < 98 then decide (InPath q (481 : Vertex)) else (if i < 99 then decide (InPath q (486 : Vertex)) else decide (InPath q (487 : Vertex)))) else (if i < 102 then (if i < 101 then decide (InPath q (488 : Vertex)) else decide (InPath q (489 : Vertex))) else (if i < 103 then decide (InPath q (492 : Vertex)) else decide (InPath q (494 : Vertex))))) else (if i < 107 then (if i < 105 then decide (InPath q (498 : Vertex)) else (if i < 106 then decide (InPath q (501 : Vertex)) else decide (InPath q (502 : Vertex)))) else (if i < 109 then (if i < 108 then decide (InPath q (503 : Vertex)) else decide (InPath q (505 : Vertex))) else (if i < 110 then decide (InPath q (506 : Vertex)) else decide (InPath q (507 : Vertex))))))))) else (if i < 167 then (if i < 139 then (if i < 125 then (if i < 118 then (if i < 114 then (if i < 112 then decide (InPath q (509 : Vertex)) else (if i < 113 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else decide (BallClauseLogic.Endpoint q (25 : Vertex)))) else (if i < 116 then (if i < 115 then decide (BallClauseLogic.Endpoint q (27 : Vertex)) else decide (BallClauseLogic.Endpoint q (65 : Vertex))) else (if i < 117 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else decide (BallClauseLogic.Endpoint q (67 : Vertex))))) else (if i < 121 then (if i < 119 then decide (BallClauseLogic.Endpoint q (71 : Vertex)) else (if i < 120 then decide (BallClauseLogic.Endpoint q (75 : Vertex)) else decide (BallClauseLogic.Endpoint q (77 : Vertex)))) else (if i < 123 then (if i < 122 then decide (BallClauseLogic.Endpoint q (79 : Vertex)) else decide (BallClauseLogic.Endpoint q (80 : Vertex))) else (if i < 124 then decide (BallClauseLogic.Endpoint q (81 : Vertex)) else decide (BallClauseLogic.Endpoint q (82 : Vertex)))))) else (if i < 132 then (if i < 128 then (if i < 126 then decide (BallClauseLogic.Endpoint q (83 : Vertex)) else (if i < 127 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (88 : Vertex)))) else (if i < 130 then (if i < 129 then decide (BallClauseLogic.Endpoint q (90 : Vertex)) else decide (BallClauseLogic.Endpoint q (91 : Vertex))) else (if i < 131 then decide (BallClauseLogic.Endpoint q (92 : Vertex)) else decide (BallClauseLogic.Endpoint q (94 : Vertex))))) else (if i < 135 then (if i < 133 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else (if i < 134 then decide (BallClauseLogic.Endpoint q (129 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex)))) else (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (135 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (141 : Vertex))))))) else (if i < 153 then (if i < 146 then (if i < 142 then (if i < 140 then decide (BallClauseLogic.Endpoint q (143 : Vertex)) else (if i < 141 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (145 : Vertex)))) else (if i < 144 then (if i < 143 then decide (BallClauseLogic.Endpoint q (146 : Vertex)) else decide (BallClauseLogic.Endpoint q (147 : Vertex))) else (if i < 145 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (154 : Vertex))))) else (if i < 149 then (if i < 147 then decide (BallClauseLogic.Endpoint q (156 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (157 : Vertex)) else decide (BallClauseLogic.Endpoint q (158 : Vertex)))) else (if i < 151 then (if i < 150 then decide (BallClauseLogic.Endpoint q (159 : Vertex)) else decide (BallClauseLogic.Endpoint q (192 : Vertex))) else (if i < 152 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else decide (BallClauseLogic.Endpoint q (198 : Vertex)))))) else (if i < 160 then (if i < 156 then (if i < 154 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else (if i < 155 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else decide (BallClauseLogic.Endpoint q (201 : Vertex)))) else (if i < 158 then (if i < 157 then decide (BallClauseLogic.Endpoint q (203 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex))) else (if i < 159 then decide (BallClauseLogic.Endpoint q (206 : Vertex)) else decide (BallClauseLogic.Endpoint q (210 : Vertex))))) else (if i < 163 then (if i < 161 then decide (BallClauseLogic.Endpoint q (213 : Vertex)) else (if i < 162 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (215 : Vertex)))) else (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (217 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (219 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex)))))))) else (if i < 195 then (if i < 181 then (if i < 174 then (if i < 170 then (if i < 168 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else (if i < 169 then decide (BallClauseLogic.Endpoint q (289 : Vertex)) else decide (BallClauseLogic.Endpoint q (294 : Vertex)))) else (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (296 : Vertex)) else decide (BallClauseLogic.Endpoint q (300 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (302 : Vertex)) else decide (BallClauseLogic.Endpoint q (310 : Vertex))))) else (if i < 177 then (if i < 175 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else (if i < 176 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex)))) else (if i < 179 then (if i < 178 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (328 : Vertex))) else (if i < 180 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else decide (BallClauseLogic.Endpoint q (331 : Vertex)))))) else (if i < 188 then (if i < 184 then (if i < 182 then decide (BallClauseLogic.Endpoint q (332 : Vertex)) else (if i < 183 then decide (BallClauseLogic.Endpoint q (334 : Vertex)) else decide (BallClauseLogic.Endpoint q (338 : Vertex)))) else (if i < 186 then (if i < 185 then decide (BallClauseLogic.Endpoint q (340 : Vertex)) else decide (BallClauseLogic.Endpoint q (341 : Vertex))) else (if i < 187 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (343 : Vertex))))) else (if i < 191 then (if i < 189 then decide (BallClauseLogic.Endpoint q (345 : Vertex)) else (if i < 190 then decide (BallClauseLogic.Endpoint q (346 : Vertex)) else decide (BallClauseLogic.Endpoint q (347 : Vertex)))) else (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (349 : Vertex)) else decide (BallClauseLogic.Endpoint q (385 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (393 : Vertex))))))) else (if i < 209 then (if i < 202 then (if i < 198 then (if i < 196 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else (if i < 197 then decide (BallClauseLogic.Endpoint q (405 : Vertex)) else decide (BallClauseLogic.Endpoint q (406 : Vertex)))) else (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (407 : Vertex)) else decide (BallClauseLogic.Endpoint q (409 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (411 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex))))) else (if i < 205 then (if i < 203 then decide (BallClauseLogic.Endpoint q (417 : Vertex)) else (if i < 204 then decide (BallClauseLogic.Endpoint q (418 : Vertex)) else decide (BallClauseLogic.Endpoint q (433 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (434 : Vertex)) else decide (BallClauseLogic.Endpoint q (435 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))))) else (if i < 216 then (if i < 212 then (if i < 210 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else (if i < 211 then decide (BallClauseLogic.Endpoint q (487 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex)))) else (if i < 214 then (if i < 213 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (492 : Vertex))) else (if i < 215 then decide (BallClauseLogic.Endpoint q (494 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))))) else (if i < 219 then (if i < 217 then decide (BallClauseLogic.Endpoint q (501 : Vertex)) else (if i < 218 then decide (BallClauseLogic.Endpoint q (502 : Vertex)) else decide (BallClauseLogic.Endpoint q (503 : Vertex)))) else (if i < 221 then (if i < 220 then decide (BallClauseLogic.Endpoint q (505 : Vertex)) else decide (BallClauseLogic.Endpoint q (506 : Vertex))) else (if i < 222 then decide (BallClauseLogic.Endpoint q (507 : Vertex)) else decide (BallClauseLogic.Endpoint q (509 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count223 (b : Nat → Bool) : Nat := countLit b [113, 114]
def count225 (b : Nat → Bool) : Nat := countLit b [112, 113, 114]
def count227 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count229 (b : Nat → Bool) : Nat := countLit b [115, 116, 117]
def count231 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117]
def count233 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count235 (b : Nat → Bool) : Nat := countLit b [118, 119, 120]
def count237 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count239 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count241 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124]
def count247 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count255 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count261 (b : Nat → Bool) : Nat := countLit b [132, 133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count267 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138]
def count275 (b : Nat → Bool) : Nat := countLit b [140, 141]
def count277 (b : Nat → Bool) : Nat := countLit b [139, 140, 141]
def count279 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [142, 143, 144, 145]
def count285 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [146, 147, 148, 149, 150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count307 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count309 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count319 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]
def count329 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166]
def count331 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count333 (b : Nat → Bool) : Nat := countLit b [167, 168, 169]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [170, 171, 172]
def count339 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [174, 175, 176]
def count345 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count349 (b : Nat → Bool) : Nat := countLit b [177, 178, 179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [174, 175, 176, 177, 178, 179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180]
def count355 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [181, 182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count363 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187]
def count365 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184, 185, 186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count373 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194]
def count377 (b : Nat → Bool) : Nat := countLit b [188, 189, 190, 191, 192, 193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194]
def count383 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [195, 196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198, 199, 200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [205, 206]
def count401 (b : Nat → Bool) : Nat := countLit b [207, 208]
def count403 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208]
def count405 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208]
def count407 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208]
def count409 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count411 (b : Nat → Bool) : Nat := countLit b [209, 210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count417 (b : Nat → Bool) : Nat := countLit b [212, 213, 214, 215]
def count419 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212, 213, 214, 215]
def count421 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count423 (b : Nat → Bool) : Nat := countLit b [216, 217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count427 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count429 (b : Nat → Bool) : Nat := countLit b [219, 220, 221, 222]
def count431 (b : Nat → Bool) : Nat := countLit b [216, 217, 218, 219, 220, 221, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count437 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count439 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222]
def count441 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count443 (b : Nat → Bool) : Nat := countLit b [3, 4, 5]
def count446 (b : Nat → Bool) : Nat := countLit b [7, 8]
def count448 (b : Nat → Bool) : Nat := countLit b [9, 11]
def count450 (b : Nat → Bool) : Nat := countLit b [7, 8, 9, 11]
def count454 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 7, 8, 9, 11]
def count461 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count463 (b : Nat → Bool) : Nat := countLit b [14, 17, 19]
def count466 (b : Nat → Bool) : Nat := countLit b [21, 22]
def count468 (b : Nat → Bool) : Nat := countLit b [23, 25]
def count470 (b : Nat → Bool) : Nat := countLit b [21, 22, 23, 25]
def count474 (b : Nat → Bool) : Nat := countLit b [14, 17, 19, 21, 22, 23, 25]
def count481 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 7, 8, 9, 11, 14, 17, 19, 21, 22, 23, 25]
def count495 (b : Nat → Bool) : Nat := countLit b [29, 32]
def count497 (b : Nat → Bool) : Nat := countLit b [27, 29, 32]
def count500 (b : Nat → Bool) : Nat := countLit b [34, 35]
def count502 (b : Nat → Bool) : Nat := countLit b [38, 39]
def count504 (b : Nat → Bool) : Nat := countLit b [34, 35, 38, 39]
def count508 (b : Nat → Bool) : Nat := countLit b [27, 29, 32, 34, 35, 38, 39]
def count515 (b : Nat → Bool) : Nat := countLit b [44, 46]
def count517 (b : Nat → Bool) : Nat := countLit b [41, 44, 46]
def count520 (b : Nat → Bool) : Nat := countLit b [48, 51]
def count522 (b : Nat → Bool) : Nat := countLit b [54, 55]
def count524 (b : Nat → Bool) : Nat := countLit b [48, 51, 54, 55]
def count528 (b : Nat → Bool) : Nat := countLit b [41, 44, 46, 48, 51, 54, 55]
def count535 (b : Nat → Bool) : Nat := countLit b [27, 29, 32, 34, 35, 38, 39, 41, 44, 46, 48, 51, 54, 55]
def count549 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 7, 8, 9, 11, 14, 17, 19, 21, 22, 23, 25, 27, 29, 32, 34, 35, 38, 39, 41, 44, 46, 48, 51, 54, 55]
def count577 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count579 (b : Nat → Bool) : Nat := countLit b [56, 58, 60]
def count582 (b : Nat → Bool) : Nat := countLit b [63, 65]
def count584 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count586 (b : Nat → Bool) : Nat := countLit b [63, 65, 68, 70]
def count590 (b : Nat → Bool) : Nat := countLit b [56, 58, 60, 63, 65, 68, 70]
def count597 (b : Nat → Bool) : Nat := countLit b [73, 76]
def count599 (b : Nat → Bool) : Nat := countLit b [72, 73, 76]
def count602 (b : Nat → Bool) : Nat := countLit b [79, 80]
def count604 (b : Nat → Bool) : Nat := countLit b [83, 84]
def count606 (b : Nat → Bool) : Nat := countLit b [79, 80, 83, 84]
def count610 (b : Nat → Bool) : Nat := countLit b [72, 73, 76, 79, 80, 83, 84]
def count617 (b : Nat → Bool) : Nat := countLit b [56, 58, 60, 63, 65, 68, 70, 72, 73, 76, 79, 80, 83, 84]
def count631 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count633 (b : Nat → Bool) : Nat := countLit b [87, 89, 90]
def count636 (b : Nat → Bool) : Nat := countLit b [91, 92]
def count638 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count640 (b : Nat → Bool) : Nat := countLit b [91, 92, 95, 96]
def count644 (b : Nat → Bool) : Nat := countLit b [87, 89, 90, 91, 92, 95, 96]
def count651 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count653 (b : Nat → Bool) : Nat := countLit b [98, 101, 102]
def count656 (b : Nat → Bool) : Nat := countLit b [104, 107]
def count658 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count660 (b : Nat → Bool) : Nat := countLit b [104, 107, 110, 111]
def count664 (b : Nat → Bool) : Nat := countLit b [98, 101, 102, 104, 107, 110, 111]
def count671 (b : Nat → Bool) : Nat := countLit b [87, 89, 90, 91, 92, 95, 96, 98, 101, 102, 104, 107, 110, 111]
def count685 (b : Nat → Bool) : Nat := countLit b [56, 58, 60, 63, 65, 68, 70, 72, 73, 76, 79, 80, 83, 84, 87, 89, 90, 91, 92, 95, 96, 98, 101, 102, 104, 107, 110, 111]
def count713 (b : Nat → Bool) : Nat := countLit b [3, 4, 5, 7, 8, 9, 11, 14, 17, 19, 21, 22, 23, 25, 27, 29, 32, 34, 35, 38, 39, 41, 44, 46, 48, 51, 54, 55, 56, 58, 60, 63, 65, 68, 70, 72, 73, 76, 79, 80, 83, 84, 87, 89, 90, 91, 92, 95, 96, 98, 101, 102, 104, 107, 110, 111]
def count755 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count757 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5]
def count760 (b : Nat → Bool) : Nat := countLit b [-7, -8]
def count762 (b : Nat → Bool) : Nat := countLit b [-9, -11]
def count764 (b : Nat → Bool) : Nat := countLit b [-7, -8, -9, -11]
def count768 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -7, -8, -9, -11]
def count775 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count777 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19]
def count780 (b : Nat → Bool) : Nat := countLit b [-21, -22]
def count782 (b : Nat → Bool) : Nat := countLit b [-23, -25]
def count784 (b : Nat → Bool) : Nat := countLit b [-21, -22, -23, -25]
def count788 (b : Nat → Bool) : Nat := countLit b [-14, -17, -19, -21, -22, -23, -25]
def count795 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -7, -8, -9, -11, -14, -17, -19, -21, -22, -23, -25]
def count809 (b : Nat → Bool) : Nat := countLit b [-29, -32]
def count811 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32]
def count814 (b : Nat → Bool) : Nat := countLit b [-34, -35]
def count816 (b : Nat → Bool) : Nat := countLit b [-38, -39]
def count818 (b : Nat → Bool) : Nat := countLit b [-34, -35, -38, -39]
def count822 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32, -34, -35, -38, -39]
def count829 (b : Nat → Bool) : Nat := countLit b [-44, -46]
def count831 (b : Nat → Bool) : Nat := countLit b [-41, -44, -46]
def count834 (b : Nat → Bool) : Nat := countLit b [-48, -51]
def count836 (b : Nat → Bool) : Nat := countLit b [-54, -55]
def count838 (b : Nat → Bool) : Nat := countLit b [-48, -51, -54, -55]
def count842 (b : Nat → Bool) : Nat := countLit b [-41, -44, -46, -48, -51, -54, -55]
def count849 (b : Nat → Bool) : Nat := countLit b [-27, -29, -32, -34, -35, -38, -39, -41, -44, -46, -48, -51, -54, -55]
def count863 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -7, -8, -9, -11, -14, -17, -19, -21, -22, -23, -25, -27, -29, -32, -34, -35, -38, -39, -41, -44, -46, -48, -51, -54, -55]
def count879 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count881 (b : Nat → Bool) : Nat := countLit b [-56, -58, -60]
def count884 (b : Nat → Bool) : Nat := countLit b [-63, -65]
def count886 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count888 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68, -70]
def count892 (b : Nat → Bool) : Nat := countLit b [-56, -58, -60, -63, -65, -68, -70]
def count899 (b : Nat → Bool) : Nat := countLit b [-73, -76]
def count901 (b : Nat → Bool) : Nat := countLit b [-72, -73, -76]
def count904 (b : Nat → Bool) : Nat := countLit b [-79, -80]
def count906 (b : Nat → Bool) : Nat := countLit b [-83, -84]
def count908 (b : Nat → Bool) : Nat := countLit b [-79, -80, -83, -84]
def count912 (b : Nat → Bool) : Nat := countLit b [-72, -73, -76, -79, -80, -83, -84]
def count919 (b : Nat → Bool) : Nat := countLit b [-56, -58, -60, -63, -65, -68, -70, -72, -73, -76, -79, -80, -83, -84]
def count933 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count935 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90]
def count938 (b : Nat → Bool) : Nat := countLit b [-91, -92]
def count940 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count942 (b : Nat → Bool) : Nat := countLit b [-91, -92, -95, -96]
def count946 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90, -91, -92, -95, -96]
def count953 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count955 (b : Nat → Bool) : Nat := countLit b [-98, -101, -102]
def count958 (b : Nat → Bool) : Nat := countLit b [-104, -107]
def count960 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count962 (b : Nat → Bool) : Nat := countLit b [-104, -107, -110, -111]
def count966 (b : Nat → Bool) : Nat := countLit b [-98, -101, -102, -104, -107, -110, -111]
def count973 (b : Nat → Bool) : Nat := countLit b [-87, -89, -90, -91, -92, -95, -96, -98, -101, -102, -104, -107, -110, -111]
def count987 (b : Nat → Bool) : Nat := countLit b [-56, -58, -60, -63, -65, -68, -70, -72, -73, -76, -79, -80, -83, -84, -87, -89, -90, -91, -92, -95, -96, -98, -101, -102, -104, -107, -110, -111]
def count1003 (b : Nat → Bool) : Nat := countLit b [-3, -4, -5, -7, -8, -9, -11, -14, -17, -19, -21, -22, -23, -25, -27, -29, -32, -34, -35, -38, -39, -41, -44, -46, -48, -51, -54, -55, -56, -58, -60, -63, -65, -68, -70, -72, -73, -76, -79, -80, -83, -84, -87, -89, -90, -91, -92, -95, -96, -98, -101, -102, -104, -107, -110, -111]
def count1019 (b : Nat → Bool) : Nat := countLit b [2, 6]
def count1021 (b : Nat → Bool) : Nat := countLit b [1, 2, 6]
def count1024 (b : Nat → Bool) : Nat := countLit b [12, 13]
def count1026 (b : Nat → Bool) : Nat := countLit b [10, 12, 13]
def count1029 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 10, 12, 13]
def count1035 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count1037 (b : Nat → Bool) : Nat := countLit b [15, 16, 18]
def count1040 (b : Nat → Bool) : Nat := countLit b [20, 24]
def count1042 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count1044 (b : Nat → Bool) : Nat := countLit b [20, 24, 26, 28]
def count1048 (b : Nat → Bool) : Nat := countLit b [15, 16, 18, 20, 24, 26, 28]
def count1055 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 10, 12, 13, 15, 16, 18, 20, 24, 26, 28]
def count1068 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count1070 (b : Nat → Bool) : Nat := countLit b [30, 31, 33]
def count1073 (b : Nat → Bool) : Nat := countLit b [36, 37]
def count1075 (b : Nat → Bool) : Nat := countLit b [40, 42]
def count1077 (b : Nat → Bool) : Nat := countLit b [36, 37, 40, 42]
def count1081 (b : Nat → Bool) : Nat := countLit b [30, 31, 33, 36, 37, 40, 42]
def count1088 (b : Nat → Bool) : Nat := countLit b [45, 47]
def count1090 (b : Nat → Bool) : Nat := countLit b [43, 45, 47]
def count1093 (b : Nat → Bool) : Nat := countLit b [49, 50]
def count1095 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count1097 (b : Nat → Bool) : Nat := countLit b [49, 50, 52, 53]
def count1101 (b : Nat → Bool) : Nat := countLit b [43, 45, 47, 49, 50, 52, 53]
def count1108 (b : Nat → Bool) : Nat := countLit b [30, 31, 33, 36, 37, 40, 42, 43, 45, 47, 49, 50, 52, 53]
def count1122 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 10, 12, 13, 15, 16, 18, 20, 24, 26, 28, 30, 31, 33, 36, 37, 40, 42, 43, 45, 47, 49, 50, 52, 53]
def count1149 (b : Nat → Bool) : Nat := countLit b [59, 61]
def count1151 (b : Nat → Bool) : Nat := countLit b [57, 59, 61]
def count1154 (b : Nat → Bool) : Nat := countLit b [62, 64]
def count1156 (b : Nat → Bool) : Nat := countLit b [66, 67]
def count1158 (b : Nat → Bool) : Nat := countLit b [62, 64, 66, 67]
def count1162 (b : Nat → Bool) : Nat := countLit b [57, 59, 61, 62, 64, 66, 67]
def count1169 (b : Nat → Bool) : Nat := countLit b [71, 74]
def count1171 (b : Nat → Bool) : Nat := countLit b [69, 71, 74]
def count1174 (b : Nat → Bool) : Nat := countLit b [75, 77]
def count1176 (b : Nat → Bool) : Nat := countLit b [78, 81]
def count1178 (b : Nat → Bool) : Nat := countLit b [75, 77, 78, 81]
def count1182 (b : Nat → Bool) : Nat := countLit b [69, 71, 74, 75, 77, 78, 81]
def count1189 (b : Nat → Bool) : Nat := countLit b [57, 59, 61, 62, 64, 66, 67, 69, 71, 74, 75, 77, 78, 81]
def count1203 (b : Nat → Bool) : Nat := countLit b [85, 86]
def count1205 (b : Nat → Bool) : Nat := countLit b [82, 85, 86]
def count1208 (b : Nat → Bool) : Nat := countLit b [88, 93]
def count1210 (b : Nat → Bool) : Nat := countLit b [94, 97]
def count1212 (b : Nat → Bool) : Nat := countLit b [88, 93, 94, 97]
def count1216 (b : Nat → Bool) : Nat := countLit b [82, 85, 86, 88, 93, 94, 97]
def count1223 (b : Nat → Bool) : Nat := countLit b [100, 103]
def count1225 (b : Nat → Bool) : Nat := countLit b [99, 100, 103]
def count1228 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count1230 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count1232 (b : Nat → Bool) : Nat := countLit b [105, 106, 108, 109]
def count1236 (b : Nat → Bool) : Nat := countLit b [99, 100, 103, 105, 106, 108, 109]
def count1243 (b : Nat → Bool) : Nat := countLit b [82, 85, 86, 88, 93, 94, 97, 99, 100, 103, 105, 106, 108, 109]
def count1257 (b : Nat → Bool) : Nat := countLit b [57, 59, 61, 62, 64, 66, 67, 69, 71, 74, 75, 77, 78, 81, 82, 85, 86, 88, 93, 94, 97, 99, 100, 103, 105, 106, 108, 109]
def count1285 (b : Nat → Bool) : Nat := countLit b [1, 2, 6, 10, 12, 13, 15, 16, 18, 20, 24, 26, 28, 30, 31, 33, 36, 37, 40, 42, 43, 45, 47, 49, 50, 52, 53, 57, 59, 61, 62, 64, 66, 67, 69, 71, 74, 75, 77, 78, 81, 82, 85, 86, 88, 93, 94, 97, 99, 100, 103, 105, 106, 108, 109]
def count1327 (b : Nat → Bool) : Nat := countLit b [-2, -6]
def count1329 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6]
def count1332 (b : Nat → Bool) : Nat := countLit b [-12, -13]
def count1334 (b : Nat → Bool) : Nat := countLit b [-10, -12, -13]
def count1337 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -10, -12, -13]
def count1343 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1345 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18]
def count1348 (b : Nat → Bool) : Nat := countLit b [-20, -24]
def count1350 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count1352 (b : Nat → Bool) : Nat := countLit b [-20, -24, -26, -28]
def count1356 (b : Nat → Bool) : Nat := countLit b [-15, -16, -18, -20, -24, -26, -28]
def count1363 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28]
def count1376 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count1378 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33]
def count1381 (b : Nat → Bool) : Nat := countLit b [-36, -37]
def count1383 (b : Nat → Bool) : Nat := countLit b [-40, -42]
def count1385 (b : Nat → Bool) : Nat := countLit b [-36, -37, -40, -42]
def count1389 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33, -36, -37, -40, -42]
def count1396 (b : Nat → Bool) : Nat := countLit b [-45, -47]
def count1398 (b : Nat → Bool) : Nat := countLit b [-43, -45, -47]
def count1401 (b : Nat → Bool) : Nat := countLit b [-49, -50]
def count1403 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count1405 (b : Nat → Bool) : Nat := countLit b [-49, -50, -52, -53]
def count1409 (b : Nat → Bool) : Nat := countLit b [-43, -45, -47, -49, -50, -52, -53]
def count1416 (b : Nat → Bool) : Nat := countLit b [-30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]
def count1430 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53]
def count1445 (b : Nat → Bool) : Nat := countLit b [-59, -61]
def count1447 (b : Nat → Bool) : Nat := countLit b [-57, -59, -61]
def count1450 (b : Nat → Bool) : Nat := countLit b [-62, -64]
def count1452 (b : Nat → Bool) : Nat := countLit b [-66, -67]
def count1454 (b : Nat → Bool) : Nat := countLit b [-62, -64, -66, -67]
def count1458 (b : Nat → Bool) : Nat := countLit b [-57, -59, -61, -62, -64, -66, -67]
def count1465 (b : Nat → Bool) : Nat := countLit b [-71, -74]
def count1467 (b : Nat → Bool) : Nat := countLit b [-69, -71, -74]
def count1470 (b : Nat → Bool) : Nat := countLit b [-75, -77]
def count1472 (b : Nat → Bool) : Nat := countLit b [-78, -81]
def count1474 (b : Nat → Bool) : Nat := countLit b [-75, -77, -78, -81]
def count1478 (b : Nat → Bool) : Nat := countLit b [-69, -71, -74, -75, -77, -78, -81]
def count1485 (b : Nat → Bool) : Nat := countLit b [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81]
def count1499 (b : Nat → Bool) : Nat := countLit b [-85, -86]
def count1501 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86]
def count1504 (b : Nat → Bool) : Nat := countLit b [-88, -93]
def count1506 (b : Nat → Bool) : Nat := countLit b [-94, -97]
def count1508 (b : Nat → Bool) : Nat := countLit b [-88, -93, -94, -97]
def count1512 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86, -88, -93, -94, -97]
def count1519 (b : Nat → Bool) : Nat := countLit b [-100, -103]
def count1521 (b : Nat → Bool) : Nat := countLit b [-99, -100, -103]
def count1524 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count1526 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count1528 (b : Nat → Bool) : Nat := countLit b [-105, -106, -108, -109]
def count1532 (b : Nat → Bool) : Nat := countLit b [-99, -100, -103, -105, -106, -108, -109]
def count1539 (b : Nat → Bool) : Nat := countLit b [-82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]
def count1553 (b : Nat → Bool) : Nat := countLit b [-57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]
def count1568 (b : Nat → Bool) : Nat := countLit b [-1, -2, -6, -10, -12, -13, -15, -16, -18, -20, -24, -26, -28, -30, -31, -33, -36, -37, -40, -42, -43, -45, -47, -49, -50, -52, -53, -57, -59, -61, -62, -64, -66, -67, -69, -71, -74, -75, -77, -78, -81, -82, -85, -86, -88, -93, -94, -97, -99, -100, -103, -105, -106, -108, -109]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 791 then (if i < 395 then (if i < 197 then (if i < 98 then (if i < 49 then (if i < 24 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 22 then b 21 else (if i < 23 then b 22 else b 23))))) else (if i < 36 then (if i < 30 then (if i < 27 then (if i < 25 then b 24 else (if i < 26 then b 25 else b 26)) else (if i < 28 then b 27 else (if i < 29 then b 28 else b 29))) else (if i < 33 then (if i < 31 then b 30 else (if i < 32 then b 31 else b 32)) else (if i < 34 then b 33 else (if i < 35 then b 34 else b 35)))) else (if i < 42 then (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 40 then b 39 else (if i < 41 then b 40 else b 41))) else (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else b 48)))))) else (if i < 73 then (if i < 61 then (if i < 55 then (if i < 52 then (if i < 50 then b 49 else (if i < 51 then b 50 else b 51)) else (if i < 53 then b 52 else (if i < 54 then b 53 else b 54))) else (if i < 58 then (if i < 56 then b 55 else (if i < 57 then b 56 else b 57)) else (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)))) else (if i < 67 then (if i < 64 then (if i < 62 then b 61 else (if i < 63 then b 62 else b 63)) else (if i < 65 then b 64 else (if i < 66 then b 65 else b 66))) else (if i < 70 then (if i < 68 then b 67 else (if i < 69 then b 68 else b 69)) else (if i < 71 then b 70 else (if i < 72 then b 71 else b 72))))) else (if i < 85 then (if i < 79 then (if i < 76 then (if i < 74 then b 73 else (if i < 75 then b 74 else b 75)) else (if i < 77 then b 76 else (if i < 78 then b 77 else b 78))) else (if i < 82 then (if i < 80 then b 79 else (if i < 81 then b 80 else b 81)) else (if i < 83 then b 82 else (if i < 84 then b 83 else b 84)))) else (if i < 91 then (if i < 88 then (if i < 86 then b 85 else (if i < 87 then b 86 else b 87)) else (if i < 89 then b 88 else (if i < 90 then b 89 else b 90))) else (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else b 97))))))) else (if i < 147 then (if i < 122 then (if i < 110 then (if i < 104 then (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 102 then b 101 else (if i < 103 then b 102 else b 103))) else (if i < 107 then (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)) else (if i < 108 then b 107 else (if i < 109 then b 108 else b 109)))) else (if i < 116 then (if i < 113 then (if i < 111 then b 110 else (if i < 112 then b 111 else b 112)) else (if i < 114 then b 113 else (if i < 115 then b 114 else b 115))) else (if i < 119 then (if i < 117 then b 116 else (if i < 118 then b 117 else b 118)) else (if i < 120 then b 119 else (if i < 121 then b 120 else b 121))))) else (if i < 134 then (if i < 128 then (if i < 125 then (if i < 123 then b 122 else (if i < 124 then b 123 else b 124)) else (if i < 126 then b 125 else (if i < 127 then b 126 else b 127))) else (if i < 131 then (if i < 129 then b 128 else (if i < 130 then b 129 else b 130)) else (if i < 132 then b 131 else (if i < 133 then b 132 else b 133)))) else (if i < 140 then (if i < 137 then (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)) else (if i < 138 then b 137 else (if i < 139 then b 138 else b 139))) else (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 145 then (if i < 144 then b 143 else b 144) else (if i < 146 then b 145 else b 146)))))) else (if i < 172 then (if i < 159 then (if i < 153 then (if i < 150 then (if i < 148 then b 147 else (if i < 149 then b 148 else b 149)) else (if i < 151 then b 150 else (if i < 152 then b 151 else b 152))) else (if i < 156 then (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)) else (if i < 157 then b 156 else (if i < 158 then b 157 else b 158)))) else (if i < 165 then (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 163 then b 162 else (if i < 164 then b 163 else b 164))) else (if i < 168 then (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)) else (if i < 170 then (if i < 169 then b 168 else b 169) else (if i < 171 then b 170 else b 171))))) else (if i < 184 then (if i < 178 then (if i < 175 then (if i < 173 then b 172 else (if i < 174 then b 173 else b 174)) else (if i < 176 then b 175 else (if i < 177 then b 176 else b 177))) else (if i < 181 then (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)) else (if i < 182 then b 181 else (if i < 183 then b 182 else b 183)))) else (if i < 190 then (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 188 then b 187 else (if i < 189 then b 188 else b 189))) else (if i < 193 then (if i < 191 then b 190 else (if i < 192 then b 191 else b 192)) else (if i < 195 then (if i < 194 then b 193 else b 194) else (if i < 196 then b 195 else b 196)))))))) else (if i < 296 then (if i < 246 then (if i < 221 then (if i < 209 then (if i < 203 then (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 201 then b 200 else (if i < 202 then b 201 else b 202))) else (if i < 206 then (if i < 204 then b 203 else (if i < 205 then b 204 else b 205)) else (if i < 207 then b 206 else (if i < 208 then b 207 else b 208)))) else (if i < 215 then (if i < 212 then (if i < 210 then b 209 else (if i < 211 then b 210 else b 211)) else (if i < 213 then b 212 else (if i < 214 then b 213 else b 214))) else (if i < 218 then (if i < 216 then b 215 else (if i < 217 then b 216 else b 217)) else (if i < 219 then b 218 else (if i < 220 then b 219 else b 220))))) else (if i < 233 then (if i < 227 then (if i < 224 then (if i < 222 then b 221 else (if i < 223 then b 222 else decide (1 ≤ count223 b))) else (if i < 225 then decide (2 ≤ count223 b) else (if i < 226 then decide (1 ≤ count225 b) else decide (2 ≤ count225 b)))) else (if i < 230 then (if i < 228 then decide (1 ≤ count227 b) else (if i < 229 then decide (2 ≤ count227 b) else decide (1 ≤ count229 b))) else (if i < 231 then decide (2 ≤ count229 b) else (if i < 232 then decide (1 ≤ count231 b) else decide (2 ≤ count231 b))))) else (if i < 239 then (if i < 236 then (if i < 234 then decide (1 ≤ count233 b) else (if i < 235 then decide (2 ≤ count233 b) else decide (1 ≤ count235 b))) else (if i < 237 then decide (2 ≤ count235 b) else (if i < 238 then decide (1 ≤ count237 b) else decide (2 ≤ count237 b)))) else (if i < 242 then (if i < 240 then decide (1 ≤ count239 b) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b))) else (if i < 244 then (if i < 243 then decide (2 ≤ count241 b) else decide (1 ≤ count243 b)) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b))))))) else (if i < 271 then (if i < 258 then (if i < 252 then (if i < 249 then (if i < 247 then decide (2 ≤ count245 b) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b))) else (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b)))) else (if i < 255 then (if i < 253 then decide (2 ≤ count251 b) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))) else (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))))) else (if i < 264 then (if i < 261 then (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b))) else (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b)))) else (if i < 267 then (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))) else (if i < 269 then (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b)) else (if i < 270 then decide (1 ≤ count269 b) else decide (2 ≤ count269 b)))))) else (if i < 283 then (if i < 277 then (if i < 274 then (if i < 272 then decide (1 ≤ count271 b) else (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b))) else (if i < 275 then decide (2 ≤ count273 b) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b)))) else (if i < 280 then (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))) else (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))))) else (if i < 289 then (if i < 286 then (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b))) else (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)))) else (if i < 292 then (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b))) else (if i < 294 then (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b)) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)))))))) else (if i < 345 then (if i < 320 then (if i < 308 then (if i < 302 then (if i < 299 then (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b))) else (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)))) else (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))))) else (if i < 314 then (if i < 311 then (if i < 309 then decide (2 ≤ count307 b) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b))) else (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)))) else (if i < 317 then (if i < 315 then decide (2 ≤ count313 b) else (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b))) else (if i < 318 then decide (1 ≤ count317 b) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))))) else (if i < 332 then (if i < 326 then (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 324 then decide (1 ≤ count323 b) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b)))) else (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))))) else (if i < 338 then (if i < 335 then (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))) else (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)))) else (if i < 341 then (if i < 339 then decide (2 ≤ count337 b) else (if i < 340 then decide (1 ≤ count339 b) else decide (2 ≤ count339 b))) else (if i < 343 then (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b)) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b))))))) else (if i < 370 then (if i < 357 then (if i < 351 then (if i < 348 then (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b))) else (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b)))) else (if i < 354 then (if i < 352 then decide (1 ≤ count351 b) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))) else (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))))) else (if i < 363 then (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)))) else (if i < 366 then (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b))) else (if i < 368 then (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b)))))) else (if i < 382 then (if i < 376 then (if i < 373 then (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))) else (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)))) else (if i < 379 then (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b))) else (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))))) else (if i < 388 then (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)))) else (if i < 391 then (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b))) else (if i < 393 then (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b)) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)))))))))) else (if i < 593 then (if i < 494 then (if i < 444 then (if i < 419 then (if i < 407 then (if i < 401 then (if i < 398 then (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))) else (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)))) else (if i < 404 then (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))))) else (if i < 413 then (if i < 410 then (if i < 408 then decide (1 ≤ count407 b) else (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b))) else (if i < 411 then decide (2 ≤ count409 b) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)))) else (if i < 416 then (if i < 414 then decide (1 ≤ count413 b) else (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b))) else (if i < 417 then decide (2 ≤ count415 b) else (if i < 418 then decide (1 ≤ count417 b) else decide (2 ≤ count417 b)))))) else (if i < 431 then (if i < 425 then (if i < 422 then (if i < 420 then decide (1 ≤ count419 b) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))) else (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b)))) else (if i < 428 then (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b))) else (if i < 429 then decide (2 ≤ count427 b) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))))) else (if i < 437 then (if i < 434 then (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))) else (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))) else (if i < 440 then (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))) else (if i < 442 then (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b))))))) else (if i < 469 then (if i < 456 then (if i < 450 then (if i < 447 then (if i < 445 then decide (2 ≤ count443 b) else (if i < 446 then decide (3 ≤ count443 b) else decide (1 ≤ count446 b))) else (if i < 448 then decide (2 ≤ count446 b) else (if i < 449 then decide (1 ≤ count448 b) else decide (2 ≤ count448 b)))) else (if i < 453 then (if i < 451 then decide (1 ≤ count450 b) else (if i < 452 then decide (2 ≤ count450 b) else decide (3 ≤ count450 b))) else (if i < 454 then decide (4 ≤ count450 b) else (if i < 455 then decide (1 ≤ count454 b) else decide (2 ≤ count454 b))))) else (if i < 462 then (if i < 459 then (if i < 457 then decide (3 ≤ count454 b) else (if i < 458 then decide (4 ≤ count454 b) else decide (5 ≤ count454 b))) else (if i < 460 then decide (6 ≤ count454 b) else (if i < 461 then decide (7 ≤ count454 b) else decide (1 ≤ count461 b)))) else (if i < 465 then (if i < 463 then decide (2 ≤ count461 b) else (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b))) else (if i < 467 then (if i < 466 then decide (3 ≤ count463 b) else decide (1 ≤ count466 b)) else (if i < 468 then decide (2 ≤ count466 b) else decide (1 ≤ count468 b)))))) else (if i < 481 then (if i < 475 then (if i < 472 then (if i < 470 then decide (2 ≤ count468 b) else (if i < 471 then decide (1 ≤ count470 b) else decide (2 ≤ count470 b))) else (if i < 473 then decide (3 ≤ count470 b) else (if i < 474 then decide (4 ≤ count470 b) else decide (1 ≤ count474 b)))) else (if i < 478 then (if i < 476 then decide (2 ≤ count474 b) else (if i < 477 then decide (3 ≤ count474 b) else decide (4 ≤ count474 b))) else (if i < 479 then decide (5 ≤ count474 b) else (if i < 480 then decide (6 ≤ count474 b) else decide (7 ≤ count474 b))))) else (if i < 487 then (if i < 484 then (if i < 482 then decide (1 ≤ count481 b) else (if i < 483 then decide (2 ≤ count481 b) else decide (3 ≤ count481 b))) else (if i < 485 then decide (4 ≤ count481 b) else (if i < 486 then decide (5 ≤ count481 b) else decide (6 ≤ count481 b)))) else (if i < 490 then (if i < 488 then decide (7 ≤ count481 b) else (if i < 489 then decide (8 ≤ count481 b) else decide (9 ≤ count481 b))) else (if i < 492 then (if i < 491 then decide (10 ≤ count481 b) else decide (11 ≤ count481 b)) else (if i < 493 then decide (12 ≤ count481 b) else decide (13 ≤ count481 b)))))))) else (if i < 543 then (if i < 518 then (if i < 506 then (if i < 500 then (if i < 497 then (if i < 495 then decide (14 ≤ count481 b) else (if i < 496 then decide (1 ≤ count495 b) else decide (2 ≤ count495 b))) else (if i < 498 then decide (1 ≤ count497 b) else (if i < 499 then decide (2 ≤ count497 b) else decide (3 ≤ count497 b)))) else (if i < 503 then (if i < 501 then decide (1 ≤ count500 b) else (if i < 502 then decide (2 ≤ count500 b) else decide (1 ≤ count502 b))) else (if i < 504 then decide (2 ≤ count502 b) else (if i < 505 then decide (1 ≤ count504 b) else decide (2 ≤ count504 b))))) else (if i < 512 then (if i < 509 then (if i < 507 then decide (3 ≤ count504 b) else (if i < 508 then decide (4 ≤ count504 b) else decide (1 ≤ count508 b))) else (if i < 510 then decide (2 ≤ count508 b) else (if i < 511 then decide (3 ≤ count508 b) else decide (4 ≤ count508 b)))) else (if i < 515 then (if i < 513 then decide (5 ≤ count508 b) else (if i < 514 then decide (6 ≤ count508 b) else decide (7 ≤ count508 b))) else (if i < 516 then decide (1 ≤ count515 b) else (if i < 517 then decide (2 ≤ count515 b) else decide (1 ≤ count517 b)))))) else (if i < 530 then (if i < 524 then (if i < 521 then (if i < 519 then decide (2 ≤ count517 b) else (if i < 520 then decide (3 ≤ count517 b) else decide (1 ≤ count520 b))) else (if i < 522 then decide (2 ≤ count520 b) else (if i < 523 then decide (1 ≤ count522 b) else decide (2 ≤ count522 b)))) else (if i < 527 then (if i < 525 then decide (1 ≤ count524 b) else (if i < 526 then decide (2 ≤ count524 b) else decide (3 ≤ count524 b))) else (if i < 528 then decide (4 ≤ count524 b) else (if i < 529 then decide (1 ≤ count528 b) else decide (2 ≤ count528 b))))) else (if i < 536 then (if i < 533 then (if i < 531 then decide (3 ≤ count528 b) else (if i < 532 then decide (4 ≤ count528 b) else decide (5 ≤ count528 b))) else (if i < 534 then decide (6 ≤ count528 b) else (if i < 535 then decide (7 ≤ count528 b) else decide (1 ≤ count535 b)))) else (if i < 539 then (if i < 537 then decide (2 ≤ count535 b) else (if i < 538 then decide (3 ≤ count535 b) else decide (4 ≤ count535 b))) else (if i < 541 then (if i < 540 then decide (5 ≤ count535 b) else decide (6 ≤ count535 b)) else (if i < 542 then decide (7 ≤ count535 b) else decide (8 ≤ count535 b))))))) else (if i < 568 then (if i < 555 then (if i < 549 then (if i < 546 then (if i < 544 then decide (9 ≤ count535 b) else (if i < 545 then decide (10 ≤ count535 b) else decide (11 ≤ count535 b))) else (if i < 547 then decide (12 ≤ count535 b) else (if i < 548 then decide (13 ≤ count535 b) else decide (14 ≤ count535 b)))) else (if i < 552 then (if i < 550 then decide (1 ≤ count549 b) else (if i < 551 then decide (2 ≤ count549 b) else decide (3 ≤ count549 b))) else (if i < 553 then decide (4 ≤ count549 b) else (if i < 554 then decide (5 ≤ count549 b) else decide (6 ≤ count549 b))))) else (if i < 561 then (if i < 558 then (if i < 556 then decide (7 ≤ count549 b) else (if i < 557 then decide (8 ≤ count549 b) else decide (9 ≤ count549 b))) else (if i < 559 then decide (10 ≤ count549 b) else (if i < 560 then decide (11 ≤ count549 b) else decide (12 ≤ count549 b)))) else (if i < 564 then (if i < 562 then decide (13 ≤ count549 b) else (if i < 563 then decide (14 ≤ count549 b) else decide (15 ≤ count549 b))) else (if i < 566 then (if i < 565 then decide (16 ≤ count549 b) else decide (17 ≤ count549 b)) else (if i < 567 then decide (18 ≤ count549 b) else decide (19 ≤ count549 b)))))) else (if i < 580 then (if i < 574 then (if i < 571 then (if i < 569 then decide (20 ≤ count549 b) else (if i < 570 then decide (21 ≤ count549 b) else decide (22 ≤ count549 b))) else (if i < 572 then decide (23 ≤ count549 b) else (if i < 573 then decide (24 ≤ count549 b) else decide (25 ≤ count549 b)))) else (if i < 577 then (if i < 575 then decide (26 ≤ count549 b) else (if i < 576 then decide (27 ≤ count549 b) else decide (28 ≤ count549 b))) else (if i < 578 then decide (1 ≤ count577 b) else (if i < 579 then decide (2 ≤ count577 b) else decide (1 ≤ count579 b))))) else (if i < 586 then (if i < 583 then (if i < 581 then decide (2 ≤ count579 b) else (if i < 582 then decide (3 ≤ count579 b) else decide (1 ≤ count582 b))) else (if i < 584 then decide (2 ≤ count582 b) else (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b)))) else (if i < 589 then (if i < 587 then decide (1 ≤ count586 b) else (if i < 588 then decide (2 ≤ count586 b) else decide (3 ≤ count586 b))) else (if i < 591 then (if i < 590 then decide (4 ≤ count586 b) else decide (1 ≤ count590 b)) else (if i < 592 then decide (2 ≤ count590 b) else decide (3 ≤ count590 b))))))))) else (if i < 692 then (if i < 642 then (if i < 617 then (if i < 605 then (if i < 599 then (if i < 596 then (if i < 594 then decide (4 ≤ count590 b) else (if i < 595 then decide (5 ≤ count590 b) else decide (6 ≤ count590 b))) else (if i < 597 then decide (7 ≤ count590 b) else (if i < 598 then decide (1 ≤ count597 b) else decide (2 ≤ count597 b)))) else (if i < 602 then (if i < 600 then decide (1 ≤ count599 b) else (if i < 601 then decide (2 ≤ count599 b) else decide (3 ≤ count599 b))) else (if i < 603 then decide (1 ≤ count602 b) else (if i < 604 then decide (2 ≤ count602 b) else decide (1 ≤ count604 b))))) else (if i < 611 then (if i < 608 then (if i < 606 then decide (2 ≤ count604 b) else (if i < 607 then decide (1 ≤ count606 b) else decide (2 ≤ count606 b))) else (if i < 609 then decide (3 ≤ count606 b) else (if i < 610 then decide (4 ≤ count606 b) else decide (1 ≤ count610 b)))) else (if i < 614 then (if i < 612 then decide (2 ≤ count610 b) else (if i < 613 then decide (3 ≤ count610 b) else decide (4 ≤ count610 b))) else (if i < 615 then decide (5 ≤ count610 b) else (if i < 616 then decide (6 ≤ count610 b) else decide (7 ≤ count610 b)))))) else (if i < 629 then (if i < 623 then (if i < 620 then (if i < 618 then decide (1 ≤ count617 b) else (if i < 619 then decide (2 ≤ count617 b) else decide (3 ≤ count617 b))) else (if i < 621 then decide (4 ≤ count617 b) else (if i < 622 then decide (5 ≤ count617 b) else decide (6 ≤ count617 b)))) else (if i < 626 then (if i < 624 then decide (7 ≤ count617 b) else (if i < 625 then decide (8 ≤ count617 b) else decide (9 ≤ count617 b))) else (if i < 627 then decide (10 ≤ count617 b) else (if i < 628 then decide (11 ≤ count617 b) else decide (12 ≤ count617 b))))) else (if i < 635 then (if i < 632 then (if i < 630 then decide (13 ≤ count617 b) else (if i < 631 then decide (14 ≤ count617 b) else decide (1 ≤ count631 b))) else (if i < 633 then decide (2 ≤ count631 b) else (if i < 634 then decide (1 ≤ count633 b) else decide (2 ≤ count633 b)))) else (if i < 638 then (if i < 636 then decide (3 ≤ count633 b) else (if i < 637 then decide (1 ≤ count636 b) else decide (2 ≤ count636 b))) else (if i < 640 then (if i < 639 then decide (1 ≤ count638 b) else decide (2 ≤ count638 b)) else (if i < 641 then decide (1 ≤ count640 b) else decide (2 ≤ count640 b))))))) else (if i < 667 then (if i < 654 then (if i < 648 then (if i < 645 then (if i < 643 then decide (3 ≤ count640 b) else (if i < 644 then decide (4 ≤ count640 b) else decide (1 ≤ count644 b))) else (if i < 646 then decide (2 ≤ count644 b) else (if i < 647 then decide (3 ≤ count644 b) else decide (4 ≤ count644 b)))) else (if i < 651 then (if i < 649 then decide (5 ≤ count644 b) else (if i < 650 then decide (6 ≤ count644 b) else decide (7 ≤ count644 b))) else (if i < 652 then decide (1 ≤ count651 b) else (if i < 653 then decide (2 ≤ count651 b) else decide (1 ≤ count653 b))))) else (if i < 660 then (if i < 657 then (if i < 655 then decide (2 ≤ count653 b) else (if i < 656 then decide (3 ≤ count653 b) else decide (1 ≤ count656 b))) else (if i < 658 then decide (2 ≤ count656 b) else (if i < 659 then decide (1 ≤ count658 b) else decide (2 ≤ count658 b)))) else (if i < 663 then (if i < 661 then decide (1 ≤ count660 b) else (if i < 662 then decide (2 ≤ count660 b) else decide (3 ≤ count660 b))) else (if i < 665 then (if i < 664 then decide (4 ≤ count660 b) else decide (1 ≤ count664 b)) else (if i < 666 then decide (2 ≤ count664 b) else decide (3 ≤ count664 b)))))) else (if i < 679 then (if i < 673 then (if i < 670 then (if i < 668 then decide (4 ≤ count664 b) else (if i < 669 then decide (5 ≤ count664 b) else decide (6 ≤ count664 b))) else (if i < 671 then decide (7 ≤ count664 b) else (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b)))) else (if i < 676 then (if i < 674 then decide (3 ≤ count671 b) else (if i < 675 then decide (4 ≤ count671 b) else decide (5 ≤ count671 b))) else (if i < 677 then decide (6 ≤ count671 b) else (if i < 678 then decide (7 ≤ count671 b) else decide (8 ≤ count671 b))))) else (if i < 685 then (if i < 682 then (if i < 680 then decide (9 ≤ count671 b) else (if i < 681 then decide (10 ≤ count671 b) else decide (11 ≤ count671 b))) else (if i < 683 then decide (12 ≤ count671 b) else (if i < 684 then decide (13 ≤ count671 b) else decide (14 ≤ count671 b)))) else (if i < 688 then (if i < 686 then decide (1 ≤ count685 b) else (if i < 687 then decide (2 ≤ count685 b) else decide (3 ≤ count685 b))) else (if i < 690 then (if i < 689 then decide (4 ≤ count685 b) else decide (5 ≤ count685 b)) else (if i < 691 then decide (6 ≤ count685 b) else decide (7 ≤ count685 b)))))))) else (if i < 741 then (if i < 716 then (if i < 704 then (if i < 698 then (if i < 695 then (if i < 693 then decide (8 ≤ count685 b) else (if i < 694 then decide (9 ≤ count685 b) else decide (10 ≤ count685 b))) else (if i < 696 then decide (11 ≤ count685 b) else (if i < 697 then decide (12 ≤ count685 b) else decide (13 ≤ count685 b)))) else (if i < 701 then (if i < 699 then decide (14 ≤ count685 b) else (if i < 700 then decide (15 ≤ count685 b) else decide (16 ≤ count685 b))) else (if i < 702 then decide (17 ≤ count685 b) else (if i < 703 then decide (18 ≤ count685 b) else decide (19 ≤ count685 b))))) else (if i < 710 then (if i < 707 then (if i < 705 then decide (20 ≤ count685 b) else (if i < 706 then decide (21 ≤ count685 b) else decide (22 ≤ count685 b))) else (if i < 708 then decide (23 ≤ count685 b) else (if i < 709 then decide (24 ≤ count685 b) else decide (25 ≤ count685 b)))) else (if i < 713 then (if i < 711 then decide (26 ≤ count685 b) else (if i < 712 then decide (27 ≤ count685 b) else decide (28 ≤ count685 b))) else (if i < 714 then decide (1 ≤ count713 b) else (if i < 715 then decide (2 ≤ count713 b) else decide (3 ≤ count713 b)))))) else (if i < 728 then (if i < 722 then (if i < 719 then (if i < 717 then decide (4 ≤ count713 b) else (if i < 718 then decide (5 ≤ count713 b) else decide (6 ≤ count713 b))) else (if i < 720 then decide (7 ≤ count713 b) else (if i < 721 then decide (8 ≤ count713 b) else decide (9 ≤ count713 b)))) else (if i < 725 then (if i < 723 then decide (10 ≤ count713 b) else (if i < 724 then decide (11 ≤ count713 b) else decide (12 ≤ count713 b))) else (if i < 726 then decide (13 ≤ count713 b) else (if i < 727 then decide (14 ≤ count713 b) else decide (15 ≤ count713 b))))) else (if i < 734 then (if i < 731 then (if i < 729 then decide (16 ≤ count713 b) else (if i < 730 then decide (17 ≤ count713 b) else decide (18 ≤ count713 b))) else (if i < 732 then decide (19 ≤ count713 b) else (if i < 733 then decide (20 ≤ count713 b) else decide (21 ≤ count713 b)))) else (if i < 737 then (if i < 735 then decide (22 ≤ count713 b) else (if i < 736 then decide (23 ≤ count713 b) else decide (24 ≤ count713 b))) else (if i < 739 then (if i < 738 then decide (25 ≤ count713 b) else decide (26 ≤ count713 b)) else (if i < 740 then decide (27 ≤ count713 b) else decide (28 ≤ count713 b))))))) else (if i < 766 then (if i < 753 then (if i < 747 then (if i < 744 then (if i < 742 then decide (29 ≤ count713 b) else (if i < 743 then decide (30 ≤ count713 b) else decide (31 ≤ count713 b))) else (if i < 745 then decide (32 ≤ count713 b) else (if i < 746 then decide (33 ≤ count713 b) else decide (34 ≤ count713 b)))) else (if i < 750 then (if i < 748 then decide (35 ≤ count713 b) else (if i < 749 then decide (36 ≤ count713 b) else decide (37 ≤ count713 b))) else (if i < 751 then decide (38 ≤ count713 b) else (if i < 752 then decide (39 ≤ count713 b) else decide (40 ≤ count713 b))))) else (if i < 759 then (if i < 756 then (if i < 754 then decide (41 ≤ count713 b) else (if i < 755 then decide (42 ≤ count713 b) else decide (1 ≤ count755 b))) else (if i < 757 then decide (2 ≤ count755 b) else (if i < 758 then decide (1 ≤ count757 b) else decide (2 ≤ count757 b)))) else (if i < 762 then (if i < 760 then decide (3 ≤ count757 b) else (if i < 761 then decide (1 ≤ count760 b) else decide (2 ≤ count760 b))) else (if i < 764 then (if i < 763 then decide (1 ≤ count762 b) else decide (2 ≤ count762 b)) else (if i < 765 then decide (1 ≤ count764 b) else decide (2 ≤ count764 b)))))) else (if i < 778 then (if i < 772 then (if i < 769 then (if i < 767 then decide (3 ≤ count764 b) else (if i < 768 then decide (4 ≤ count764 b) else decide (1 ≤ count768 b))) else (if i < 770 then decide (2 ≤ count768 b) else (if i < 771 then decide (3 ≤ count768 b) else decide (4 ≤ count768 b)))) else (if i < 775 then (if i < 773 then decide (5 ≤ count768 b) else (if i < 774 then decide (6 ≤ count768 b) else decide (7 ≤ count768 b))) else (if i < 776 then decide (1 ≤ count775 b) else (if i < 777 then decide (2 ≤ count775 b) else decide (1 ≤ count777 b))))) else (if i < 784 then (if i < 781 then (if i < 779 then decide (2 ≤ count777 b) else (if i < 780 then decide (3 ≤ count777 b) else decide (1 ≤ count780 b))) else (if i < 782 then decide (2 ≤ count780 b) else (if i < 783 then decide (1 ≤ count782 b) else decide (2 ≤ count782 b)))) else (if i < 787 then (if i < 785 then decide (1 ≤ count784 b) else (if i < 786 then decide (2 ≤ count784 b) else decide (3 ≤ count784 b))) else (if i < 789 then (if i < 788 then decide (4 ≤ count784 b) else decide (1 ≤ count788 b)) else (if i < 790 then decide (2 ≤ count788 b) else decide (3 ≤ count788 b))))))))))) else (if i < 1187 then (if i < 989 then (if i < 890 then (if i < 840 then (if i < 815 then (if i < 803 then (if i < 797 then (if i < 794 then (if i < 792 then decide (4 ≤ count788 b) else (if i < 793 then decide (5 ≤ count788 b) else decide (6 ≤ count788 b))) else (if i < 795 then decide (7 ≤ count788 b) else (if i < 796 then decide (1 ≤ count795 b) else decide (2 ≤ count795 b)))) else (if i < 800 then (if i < 798 then decide (3 ≤ count795 b) else (if i < 799 then decide (4 ≤ count795 b) else decide (5 ≤ count795 b))) else (if i < 801 then decide (6 ≤ count795 b) else (if i < 802 then decide (7 ≤ count795 b) else decide (8 ≤ count795 b))))) else (if i < 809 then (if i < 806 then (if i < 804 then decide (9 ≤ count795 b) else (if i < 805 then decide (10 ≤ count795 b) else decide (11 ≤ count795 b))) else (if i < 807 then decide (12 ≤ count795 b) else (if i < 808 then decide (13 ≤ count795 b) else decide (14 ≤ count795 b)))) else (if i < 812 then (if i < 810 then decide (1 ≤ count809 b) else (if i < 811 then decide (2 ≤ count809 b) else decide (1 ≤ count811 b))) else (if i < 813 then decide (2 ≤ count811 b) else (if i < 814 then decide (3 ≤ count811 b) else decide (1 ≤ count814 b)))))) else (if i < 827 then (if i < 821 then (if i < 818 then (if i < 816 then decide (2 ≤ count814 b) else (if i < 817 then decide (1 ≤ count816 b) else decide (2 ≤ count816 b))) else (if i < 819 then decide (1 ≤ count818 b) else (if i < 820 then decide (2 ≤ count818 b) else decide (3 ≤ count818 b)))) else (if i < 824 then (if i < 822 then decide (4 ≤ count818 b) else (if i < 823 then decide (1 ≤ count822 b) else decide (2 ≤ count822 b))) else (if i < 825 then decide (3 ≤ count822 b) else (if i < 826 then decide (4 ≤ count822 b) else decide (5 ≤ count822 b))))) else (if i < 833 then (if i < 830 then (if i < 828 then decide (6 ≤ count822 b) else (if i < 829 then decide (7 ≤ count822 b) else decide (1 ≤ count829 b))) else (if i < 831 then decide (2 ≤ count829 b) else (if i < 832 then decide (1 ≤ count831 b) else decide (2 ≤ count831 b)))) else (if i < 836 then (if i < 834 then decide (3 ≤ count831 b) else (if i < 835 then decide (1 ≤ count834 b) else decide (2 ≤ count834 b))) else (if i < 838 then (if i < 837 then decide (1 ≤ count836 b) else decide (2 ≤ count836 b)) else (if i < 839 then decide (1 ≤ count838 b) else decide (2 ≤ count838 b))))))) else (if i < 865 then (if i < 852 then (if i < 846 then (if i < 843 then (if i < 841 then decide (3 ≤ count838 b) else (if i < 842 then decide (4 ≤ count838 b) else decide (1 ≤ count842 b))) else (if i < 844 then decide (2 ≤ count842 b) else (if i < 845 then decide (3 ≤ count842 b) else decide (4 ≤ count842 b)))) else (if i < 849 then (if i < 847 then decide (5 ≤ count842 b) else (if i < 848 then decide (6 ≤ count842 b) else decide (7 ≤ count842 b))) else (if i < 850 then decide (1 ≤ count849 b) else (if i < 851 then decide (2 ≤ count849 b) else decide (3 ≤ count849 b))))) else (if i < 858 then (if i < 855 then (if i < 853 then decide (4 ≤ count849 b) else (if i < 854 then decide (5 ≤ count849 b) else decide (6 ≤ count849 b))) else (if i < 856 then decide (7 ≤ count849 b) else (if i < 857 then decide (8 ≤ count849 b) else decide (9 ≤ count849 b)))) else (if i < 861 then (if i < 859 then decide (10 ≤ count849 b) else (if i < 860 then decide (11 ≤ count849 b) else decide (12 ≤ count849 b))) else (if i < 863 then (if i < 862 then decide (13 ≤ count849 b) else decide (14 ≤ count849 b)) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b)))))) else (if i < 877 then (if i < 871 then (if i < 868 then (if i < 866 then decide (3 ≤ count863 b) else (if i < 867 then decide (4 ≤ count863 b) else decide (5 ≤ count863 b))) else (if i < 869 then decide (6 ≤ count863 b) else (if i < 870 then decide (7 ≤ count863 b) else decide (8 ≤ count863 b)))) else (if i < 874 then (if i < 872 then decide (9 ≤ count863 b) else (if i < 873 then decide (10 ≤ count863 b) else decide (11 ≤ count863 b))) else (if i < 875 then decide (12 ≤ count863 b) else (if i < 876 then decide (13 ≤ count863 b) else decide (14 ≤ count863 b))))) else (if i < 883 then (if i < 880 then (if i < 878 then decide (15 ≤ count863 b) else (if i < 879 then decide (16 ≤ count863 b) else decide (1 ≤ count879 b))) else (if i < 881 then decide (2 ≤ count879 b) else (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b)))) else (if i < 886 then (if i < 884 then decide (3 ≤ count881 b) else (if i < 885 then decide (1 ≤ count884 b) else decide (2 ≤ count884 b))) else (if i < 888 then (if i < 887 then decide (1 ≤ count886 b) else decide (2 ≤ count886 b)) else (if i < 889 then decide (1 ≤ count888 b) else decide (2 ≤ count888 b)))))))) else (if i < 939 then (if i < 914 then (if i < 902 then (if i < 896 then (if i < 893 then (if i < 891 then decide (3 ≤ count888 b) else (if i < 892 then decide (4 ≤ count888 b) else decide (1 ≤ count892 b))) else (if i < 894 then decide (2 ≤ count892 b) else (if i < 895 then decide (3 ≤ count892 b) else decide (4 ≤ count892 b)))) else (if i < 899 then (if i < 897 then decide (5 ≤ count892 b) else (if i < 898 then decide (6 ≤ count892 b) else decide (7 ≤ count892 b))) else (if i < 900 then decide (1 ≤ count899 b) else (if i < 901 then decide (2 ≤ count899 b) else decide (1 ≤ count901 b))))) else (if i < 908 then (if i < 905 then (if i < 903 then decide (2 ≤ count901 b) else (if i < 904 then decide (3 ≤ count901 b) else decide (1 ≤ count904 b))) else (if i < 906 then decide (2 ≤ count904 b) else (if i < 907 then decide (1 ≤ count906 b) else decide (2 ≤ count906 b)))) else (if i < 911 then (if i < 909 then decide (1 ≤ count908 b) else (if i < 910 then decide (2 ≤ count908 b) else decide (3 ≤ count908 b))) else (if i < 912 then decide (4 ≤ count908 b) else (if i < 913 then decide (1 ≤ count912 b) else decide (2 ≤ count912 b)))))) else (if i < 926 then (if i < 920 then (if i < 917 then (if i < 915 then decide (3 ≤ count912 b) else (if i < 916 then decide (4 ≤ count912 b) else decide (5 ≤ count912 b))) else (if i < 918 then decide (6 ≤ count912 b) else (if i < 919 then decide (7 ≤ count912 b) else decide (1 ≤ count919 b)))) else (if i < 923 then (if i < 921 then decide (2 ≤ count919 b) else (if i < 922 then decide (3 ≤ count919 b) else decide (4 ≤ count919 b))) else (if i < 924 then decide (5 ≤ count919 b) else (if i < 925 then decide (6 ≤ count919 b) else decide (7 ≤ count919 b))))) else (if i < 932 then (if i < 929 then (if i < 927 then decide (8 ≤ count919 b) else (if i < 928 then decide (9 ≤ count919 b) else decide (10 ≤ count919 b))) else (if i < 930 then decide (11 ≤ count919 b) else (if i < 931 then decide (12 ≤ count919 b) else decide (13 ≤ count919 b)))) else (if i < 935 then (if i < 933 then decide (14 ≤ count919 b) else (if i < 934 then decide (1 ≤ count933 b) else decide (2 ≤ count933 b))) else (if i < 937 then (if i < 936 then decide (1 ≤ count935 b) else decide (2 ≤ count935 b)) else (if i < 938 then decide (3 ≤ count935 b) else decide (1 ≤ count938 b))))))) else (if i < 964 then (if i < 951 then (if i < 945 then (if i < 942 then (if i < 940 then decide (2 ≤ count938 b) else (if i < 941 then decide (1 ≤ count940 b) else decide (2 ≤ count940 b))) else (if i < 943 then decide (1 ≤ count942 b) else (if i < 944 then decide (2 ≤ count942 b) else decide (3 ≤ count942 b)))) else (if i < 948 then (if i < 946 then decide (4 ≤ count942 b) else (if i < 947 then decide (1 ≤ count946 b) else decide (2 ≤ count946 b))) else (if i < 949 then decide (3 ≤ count946 b) else (if i < 950 then decide (4 ≤ count946 b) else decide (5 ≤ count946 b))))) else (if i < 957 then (if i < 954 then (if i < 952 then decide (6 ≤ count946 b) else (if i < 953 then decide (7 ≤ count946 b) else decide (1 ≤ count953 b))) else (if i < 955 then decide (2 ≤ count953 b) else (if i < 956 then decide (1 ≤ count955 b) else decide (2 ≤ count955 b)))) else (if i < 960 then (if i < 958 then decide (3 ≤ count955 b) else (if i < 959 then decide (1 ≤ count958 b) else decide (2 ≤ count958 b))) else (if i < 962 then (if i < 961 then decide (1 ≤ count960 b) else decide (2 ≤ count960 b)) else (if i < 963 then decide (1 ≤ count962 b) else decide (2 ≤ count962 b)))))) else (if i < 976 then (if i < 970 then (if i < 967 then (if i < 965 then decide (3 ≤ count962 b) else (if i < 966 then decide (4 ≤ count962 b) else decide (1 ≤ count966 b))) else (if i < 968 then decide (2 ≤ count966 b) else (if i < 969 then decide (3 ≤ count966 b) else decide (4 ≤ count966 b)))) else (if i < 973 then (if i < 971 then decide (5 ≤ count966 b) else (if i < 972 then decide (6 ≤ count966 b) else decide (7 ≤ count966 b))) else (if i < 974 then decide (1 ≤ count973 b) else (if i < 975 then decide (2 ≤ count973 b) else decide (3 ≤ count973 b))))) else (if i < 982 then (if i < 979 then (if i < 977 then decide (4 ≤ count973 b) else (if i < 978 then decide (5 ≤ count973 b) else decide (6 ≤ count973 b))) else (if i < 980 then decide (7 ≤ count973 b) else (if i < 981 then decide (8 ≤ count973 b) else decide (9 ≤ count973 b)))) else (if i < 985 then (if i < 983 then decide (10 ≤ count973 b) else (if i < 984 then decide (11 ≤ count973 b) else decide (12 ≤ count973 b))) else (if i < 987 then (if i < 986 then decide (13 ≤ count973 b) else decide (14 ≤ count973 b)) else (if i < 988 then decide (1 ≤ count987 b) else decide (2 ≤ count987 b))))))))) else (if i < 1088 then (if i < 1038 then (if i < 1013 then (if i < 1001 then (if i < 995 then (if i < 992 then (if i < 990 then decide (3 ≤ count987 b) else (if i < 991 then decide (4 ≤ count987 b) else decide (5 ≤ count987 b))) else (if i < 993 then decide (6 ≤ count987 b) else (if i < 994 then decide (7 ≤ count987 b) else decide (8 ≤ count987 b)))) else (if i < 998 then (if i < 996 then decide (9 ≤ count987 b) else (if i < 997 then decide (10 ≤ count987 b) else decide (11 ≤ count987 b))) else (if i < 999 then decide (12 ≤ count987 b) else (if i < 1000 then decide (13 ≤ count987 b) else decide (14 ≤ count987 b))))) else (if i < 1007 then (if i < 1004 then (if i < 1002 then decide (15 ≤ count987 b) else (if i < 1003 then decide (16 ≤ count987 b) else decide (1 ≤ count1003 b))) else (if i < 1005 then decide (2 ≤ count1003 b) else (if i < 1006 then decide (3 ≤ count1003 b) else decide (4 ≤ count1003 b)))) else (if i < 1010 then (if i < 1008 then decide (5 ≤ count1003 b) else (if i < 1009 then decide (6 ≤ count1003 b) else decide (7 ≤ count1003 b))) else (if i < 1011 then decide (8 ≤ count1003 b) else (if i < 1012 then decide (9 ≤ count1003 b) else decide (10 ≤ count1003 b)))))) else (if i < 1025 then (if i < 1019 then (if i < 1016 then (if i < 1014 then decide (11 ≤ count1003 b) else (if i < 1015 then decide (12 ≤ count1003 b) else decide (13 ≤ count1003 b))) else (if i < 1017 then decide (14 ≤ count1003 b) else (if i < 1018 then decide (15 ≤ count1003 b) else decide (16 ≤ count1003 b)))) else (if i < 1022 then (if i < 1020 then decide (1 ≤ count1019 b) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (1 ≤ count1021 b))) else (if i < 1023 then decide (2 ≤ count1021 b) else (if i < 1024 then decide (3 ≤ count1021 b) else decide (1 ≤ count1024 b))))) else (if i < 1031 then (if i < 1028 then (if i < 1026 then decide (2 ≤ count1024 b) else (if i < 1027 then decide (1 ≤ count1026 b) else decide (2 ≤ count1026 b))) else (if i < 1029 then decide (3 ≤ count1026 b) else (if i < 1030 then decide (1 ≤ count1029 b) else decide (2 ≤ count1029 b)))) else (if i < 1034 then (if i < 1032 then decide (3 ≤ count1029 b) else (if i < 1033 then decide (4 ≤ count1029 b) else decide (5 ≤ count1029 b))) else (if i < 1036 then (if i < 1035 then decide (6 ≤ count1029 b) else decide (1 ≤ count1035 b)) else (if i < 1037 then decide (2 ≤ count1035 b) else decide (1 ≤ count1037 b))))))) else (if i < 1063 then (if i < 1050 then (if i < 1044 then (if i < 1041 then (if i < 1039 then decide (2 ≤ count1037 b) else (if i < 1040 then decide (3 ≤ count1037 b) else decide (1 ≤ count1040 b))) else (if i < 1042 then decide (2 ≤ count1040 b) else (if i < 1043 then decide (1 ≤ count1042 b) else decide (2 ≤ count1042 b)))) else (if i < 1047 then (if i < 1045 then decide (1 ≤ count1044 b) else (if i < 1046 then decide (2 ≤ count1044 b) else decide (3 ≤ count1044 b))) else (if i < 1048 then decide (4 ≤ count1044 b) else (if i < 1049 then decide (1 ≤ count1048 b) else decide (2 ≤ count1048 b))))) else (if i < 1056 then (if i < 1053 then (if i < 1051 then decide (3 ≤ count1048 b) else (if i < 1052 then decide (4 ≤ count1048 b) else decide (5 ≤ count1048 b))) else (if i < 1054 then decide (6 ≤ count1048 b) else (if i < 1055 then decide (7 ≤ count1048 b) else decide (1 ≤ count1055 b)))) else (if i < 1059 then (if i < 1057 then decide (2 ≤ count1055 b) else (if i < 1058 then decide (3 ≤ count1055 b) else decide (4 ≤ count1055 b))) else (if i < 1061 then (if i < 1060 then decide (5 ≤ count1055 b) else decide (6 ≤ count1055 b)) else (if i < 1062 then decide (7 ≤ count1055 b) else decide (8 ≤ count1055 b)))))) else (if i < 1075 then (if i < 1069 then (if i < 1066 then (if i < 1064 then decide (9 ≤ count1055 b) else (if i < 1065 then decide (10 ≤ count1055 b) else decide (11 ≤ count1055 b))) else (if i < 1067 then decide (12 ≤ count1055 b) else (if i < 1068 then decide (13 ≤ count1055 b) else decide (1 ≤ count1068 b)))) else (if i < 1072 then (if i < 1070 then decide (2 ≤ count1068 b) else (if i < 1071 then decide (1 ≤ count1070 b) else decide (2 ≤ count1070 b))) else (if i < 1073 then decide (3 ≤ count1070 b) else (if i < 1074 then decide (1 ≤ count1073 b) else decide (2 ≤ count1073 b))))) else (if i < 1081 then (if i < 1078 then (if i < 1076 then decide (1 ≤ count1075 b) else (if i < 1077 then decide (2 ≤ count1075 b) else decide (1 ≤ count1077 b))) else (if i < 1079 then decide (2 ≤ count1077 b) else (if i < 1080 then decide (3 ≤ count1077 b) else decide (4 ≤ count1077 b)))) else (if i < 1084 then (if i < 1082 then decide (1 ≤ count1081 b) else (if i < 1083 then decide (2 ≤ count1081 b) else decide (3 ≤ count1081 b))) else (if i < 1086 then (if i < 1085 then decide (4 ≤ count1081 b) else decide (5 ≤ count1081 b)) else (if i < 1087 then decide (6 ≤ count1081 b) else decide (7 ≤ count1081 b)))))))) else (if i < 1137 then (if i < 1112 then (if i < 1100 then (if i < 1094 then (if i < 1091 then (if i < 1089 then decide (1 ≤ count1088 b) else (if i < 1090 then decide (2 ≤ count1088 b) else decide (1 ≤ count1090 b))) else (if i < 1092 then decide (2 ≤ count1090 b) else (if i < 1093 then decide (3 ≤ count1090 b) else decide (1 ≤ count1093 b)))) else (if i < 1097 then (if i < 1095 then decide (2 ≤ count1093 b) else (if i < 1096 then decide (1 ≤ count1095 b) else decide (2 ≤ count1095 b))) else (if i < 1098 then decide (1 ≤ count1097 b) else (if i < 1099 then decide (2 ≤ count1097 b) else decide (3 ≤ count1097 b))))) else (if i < 1106 then (if i < 1103 then (if i < 1101 then decide (4 ≤ count1097 b) else (if i < 1102 then decide (1 ≤ count1101 b) else decide (2 ≤ count1101 b))) else (if i < 1104 then decide (3 ≤ count1101 b) else (if i < 1105 then decide (4 ≤ count1101 b) else decide (5 ≤ count1101 b)))) else (if i < 1109 then (if i < 1107 then decide (6 ≤ count1101 b) else (if i < 1108 then decide (7 ≤ count1101 b) else decide (1 ≤ count1108 b))) else (if i < 1110 then decide (2 ≤ count1108 b) else (if i < 1111 then decide (3 ≤ count1108 b) else decide (4 ≤ count1108 b)))))) else (if i < 1124 then (if i < 1118 then (if i < 1115 then (if i < 1113 then decide (5 ≤ count1108 b) else (if i < 1114 then decide (6 ≤ count1108 b) else decide (7 ≤ count1108 b))) else (if i < 1116 then decide (8 ≤ count1108 b) else (if i < 1117 then decide (9 ≤ count1108 b) else decide (10 ≤ count1108 b)))) else (if i < 1121 then (if i < 1119 then decide (11 ≤ count1108 b) else (if i < 1120 then decide (12 ≤ count1108 b) else decide (13 ≤ count1108 b))) else (if i < 1122 then decide (14 ≤ count1108 b) else (if i < 1123 then decide (1 ≤ count1122 b) else decide (2 ≤ count1122 b))))) else (if i < 1130 then (if i < 1127 then (if i < 1125 then decide (3 ≤ count1122 b) else (if i < 1126 then decide (4 ≤ count1122 b) else decide (5 ≤ count1122 b))) else (if i < 1128 then decide (6 ≤ count1122 b) else (if i < 1129 then decide (7 ≤ count1122 b) else decide (8 ≤ count1122 b)))) else (if i < 1133 then (if i < 1131 then decide (9 ≤ count1122 b) else (if i < 1132 then decide (10 ≤ count1122 b) else decide (11 ≤ count1122 b))) else (if i < 1135 then (if i < 1134 then decide (12 ≤ count1122 b) else decide (13 ≤ count1122 b)) else (if i < 1136 then decide (14 ≤ count1122 b) else decide (15 ≤ count1122 b))))))) else (if i < 1162 then (if i < 1149 then (if i < 1143 then (if i < 1140 then (if i < 1138 then decide (16 ≤ count1122 b) else (if i < 1139 then decide (17 ≤ count1122 b) else decide (18 ≤ count1122 b))) else (if i < 1141 then decide (19 ≤ count1122 b) else (if i < 1142 then decide (20 ≤ count1122 b) else decide (21 ≤ count1122 b)))) else (if i < 1146 then (if i < 1144 then decide (22 ≤ count1122 b) else (if i < 1145 then decide (23 ≤ count1122 b) else decide (24 ≤ count1122 b))) else (if i < 1147 then decide (25 ≤ count1122 b) else (if i < 1148 then decide (26 ≤ count1122 b) else decide (27 ≤ count1122 b))))) else (if i < 1155 then (if i < 1152 then (if i < 1150 then decide (1 ≤ count1149 b) else (if i < 1151 then decide (2 ≤ count1149 b) else decide (1 ≤ count1151 b))) else (if i < 1153 then decide (2 ≤ count1151 b) else (if i < 1154 then decide (3 ≤ count1151 b) else decide (1 ≤ count1154 b)))) else (if i < 1158 then (if i < 1156 then decide (2 ≤ count1154 b) else (if i < 1157 then decide (1 ≤ count1156 b) else decide (2 ≤ count1156 b))) else (if i < 1160 then (if i < 1159 then decide (1 ≤ count1158 b) else decide (2 ≤ count1158 b)) else (if i < 1161 then decide (3 ≤ count1158 b) else decide (4 ≤ count1158 b)))))) else (if i < 1174 then (if i < 1168 then (if i < 1165 then (if i < 1163 then decide (1 ≤ count1162 b) else (if i < 1164 then decide (2 ≤ count1162 b) else decide (3 ≤ count1162 b))) else (if i < 1166 then decide (4 ≤ count1162 b) else (if i < 1167 then decide (5 ≤ count1162 b) else decide (6 ≤ count1162 b)))) else (if i < 1171 then (if i < 1169 then decide (7 ≤ count1162 b) else (if i < 1170 then decide (1 ≤ count1169 b) else decide (2 ≤ count1169 b))) else (if i < 1172 then decide (1 ≤ count1171 b) else (if i < 1173 then decide (2 ≤ count1171 b) else decide (3 ≤ count1171 b))))) else (if i < 1180 then (if i < 1177 then (if i < 1175 then decide (1 ≤ count1174 b) else (if i < 1176 then decide (2 ≤ count1174 b) else decide (1 ≤ count1176 b))) else (if i < 1178 then decide (2 ≤ count1176 b) else (if i < 1179 then decide (1 ≤ count1178 b) else decide (2 ≤ count1178 b)))) else (if i < 1183 then (if i < 1181 then decide (3 ≤ count1178 b) else (if i < 1182 then decide (4 ≤ count1178 b) else decide (1 ≤ count1182 b))) else (if i < 1185 then (if i < 1184 then decide (2 ≤ count1182 b) else decide (3 ≤ count1182 b)) else (if i < 1186 then decide (4 ≤ count1182 b) else decide (5 ≤ count1182 b)))))))))) else (if i < 1385 then (if i < 1286 then (if i < 1236 then (if i < 1211 then (if i < 1199 then (if i < 1193 then (if i < 1190 then (if i < 1188 then decide (6 ≤ count1182 b) else (if i < 1189 then decide (7 ≤ count1182 b) else decide (1 ≤ count1189 b))) else (if i < 1191 then decide (2 ≤ count1189 b) else (if i < 1192 then decide (3 ≤ count1189 b) else decide (4 ≤ count1189 b)))) else (if i < 1196 then (if i < 1194 then decide (5 ≤ count1189 b) else (if i < 1195 then decide (6 ≤ count1189 b) else decide (7 ≤ count1189 b))) else (if i < 1197 then decide (8 ≤ count1189 b) else (if i < 1198 then decide (9 ≤ count1189 b) else decide (10 ≤ count1189 b))))) else (if i < 1205 then (if i < 1202 then (if i < 1200 then decide (11 ≤ count1189 b) else (if i < 1201 then decide (12 ≤ count1189 b) else decide (13 ≤ count1189 b))) else (if i < 1203 then decide (14 ≤ count1189 b) else (if i < 1204 then decide (1 ≤ count1203 b) else decide (2 ≤ count1203 b)))) else (if i < 1208 then (if i < 1206 then decide (1 ≤ count1205 b) else (if i < 1207 then decide (2 ≤ count1205 b) else decide (3 ≤ count1205 b))) else (if i < 1209 then decide (1 ≤ count1208 b) else (if i < 1210 then decide (2 ≤ count1208 b) else decide (1 ≤ count1210 b)))))) else (if i < 1223 then (if i < 1217 then (if i < 1214 then (if i < 1212 then decide (2 ≤ count1210 b) else (if i < 1213 then decide (1 ≤ count1212 b) else decide (2 ≤ count1212 b))) else (if i < 1215 then decide (3 ≤ count1212 b) else (if i < 1216 then decide (4 ≤ count1212 b) else decide (1 ≤ count1216 b)))) else (if i < 1220 then (if i < 1218 then decide (2 ≤ count1216 b) else (if i < 1219 then decide (3 ≤ count1216 b) else decide (4 ≤ count1216 b))) else (if i < 1221 then decide (5 ≤ count1216 b) else (if i < 1222 then decide (6 ≤ count1216 b) else decide (7 ≤ count1216 b))))) else (if i < 1229 then (if i < 1226 then (if i < 1224 then decide (1 ≤ count1223 b) else (if i < 1225 then decide (2 ≤ count1223 b) else decide (1 ≤ count1225 b))) else (if i < 1227 then decide (2 ≤ count1225 b) else (if i < 1228 then decide (3 ≤ count1225 b) else decide (1 ≤ count1228 b)))) else (if i < 1232 then (if i < 1230 then decide (2 ≤ count1228 b) else (if i < 1231 then decide (1 ≤ count1230 b) else decide (2 ≤ count1230 b))) else (if i < 1234 then (if i < 1233 then decide (1 ≤ count1232 b) else decide (2 ≤ count1232 b)) else (if i < 1235 then decide (3 ≤ count1232 b) else decide (4 ≤ count1232 b))))))) else (if i < 1261 then (if i < 1248 then (if i < 1242 then (if i < 1239 then (if i < 1237 then decide (1 ≤ count1236 b) else (if i < 1238 then decide (2 ≤ count1236 b) else decide (3 ≤ count1236 b))) else (if i < 1240 then decide (4 ≤ count1236 b) else (if i < 1241 then decide (5 ≤ count1236 b) else decide (6 ≤ count1236 b)))) else (if i < 1245 then (if i < 1243 then decide (7 ≤ count1236 b) else (if i < 1244 then decide (1 ≤ count1243 b) else decide (2 ≤ count1243 b))) else (if i < 1246 then decide (3 ≤ count1243 b) else (if i < 1247 then decide (4 ≤ count1243 b) else decide (5 ≤ count1243 b))))) else (if i < 1254 then (if i < 1251 then (if i < 1249 then decide (6 ≤ count1243 b) else (if i < 1250 then decide (7 ≤ count1243 b) else decide (8 ≤ count1243 b))) else (if i < 1252 then decide (9 ≤ count1243 b) else (if i < 1253 then decide (10 ≤ count1243 b) else decide (11 ≤ count1243 b)))) else (if i < 1257 then (if i < 1255 then decide (12 ≤ count1243 b) else (if i < 1256 then decide (13 ≤ count1243 b) else decide (14 ≤ count1243 b))) else (if i < 1259 then (if i < 1258 then decide (1 ≤ count1257 b) else decide (2 ≤ count1257 b)) else (if i < 1260 then decide (3 ≤ count1257 b) else decide (4 ≤ count1257 b)))))) else (if i < 1273 then (if i < 1267 then (if i < 1264 then (if i < 1262 then decide (5 ≤ count1257 b) else (if i < 1263 then decide (6 ≤ count1257 b) else decide (7 ≤ count1257 b))) else (if i < 1265 then decide (8 ≤ count1257 b) else (if i < 1266 then decide (9 ≤ count1257 b) else decide (10 ≤ count1257 b)))) else (if i < 1270 then (if i < 1268 then decide (11 ≤ count1257 b) else (if i < 1269 then decide (12 ≤ count1257 b) else decide (13 ≤ count1257 b))) else (if i < 1271 then decide (14 ≤ count1257 b) else (if i < 1272 then decide (15 ≤ count1257 b) else decide (16 ≤ count1257 b))))) else (if i < 1279 then (if i < 1276 then (if i < 1274 then decide (17 ≤ count1257 b) else (if i < 1275 then decide (18 ≤ count1257 b) else decide (19 ≤ count1257 b))) else (if i < 1277 then decide (20 ≤ count1257 b) else (if i < 1278 then decide (21 ≤ count1257 b) else decide (22 ≤ count1257 b)))) else (if i < 1282 then (if i < 1280 then decide (23 ≤ count1257 b) else (if i < 1281 then decide (24 ≤ count1257 b) else decide (25 ≤ count1257 b))) else (if i < 1284 then (if i < 1283 then decide (26 ≤ count1257 b) else decide (27 ≤ count1257 b)) else (if i < 1285 then decide (28 ≤ count1257 b) else decide (1 ≤ count1285 b)))))))) else (if i < 1335 then (if i < 1310 then (if i < 1298 then (if i < 1292 then (if i < 1289 then (if i < 1287 then decide (2 ≤ count1285 b) else (if i < 1288 then decide (3 ≤ count1285 b) else decide (4 ≤ count1285 b))) else (if i < 1290 then decide (5 ≤ count1285 b) else (if i < 1291 then decide (6 ≤ count1285 b) else decide (7 ≤ count1285 b)))) else (if i < 1295 then (if i < 1293 then decide (8 ≤ count1285 b) else (if i < 1294 then decide (9 ≤ count1285 b) else decide (10 ≤ count1285 b))) else (if i < 1296 then decide (11 ≤ count1285 b) else (if i < 1297 then decide (12 ≤ count1285 b) else decide (13 ≤ count1285 b))))) else (if i < 1304 then (if i < 1301 then (if i < 1299 then decide (14 ≤ count1285 b) else (if i < 1300 then decide (15 ≤ count1285 b) else decide (16 ≤ count1285 b))) else (if i < 1302 then decide (17 ≤ count1285 b) else (if i < 1303 then decide (18 ≤ count1285 b) else decide (19 ≤ count1285 b)))) else (if i < 1307 then (if i < 1305 then decide (20 ≤ count1285 b) else (if i < 1306 then decide (21 ≤ count1285 b) else decide (22 ≤ count1285 b))) else (if i < 1308 then decide (23 ≤ count1285 b) else (if i < 1309 then decide (24 ≤ count1285 b) else decide (25 ≤ count1285 b)))))) else (if i < 1322 then (if i < 1316 then (if i < 1313 then (if i < 1311 then decide (26 ≤ count1285 b) else (if i < 1312 then decide (27 ≤ count1285 b) else decide (28 ≤ count1285 b))) else (if i < 1314 then decide (29 ≤ count1285 b) else (if i < 1315 then decide (30 ≤ count1285 b) else decide (31 ≤ count1285 b)))) else (if i < 1319 then (if i < 1317 then decide (32 ≤ count1285 b) else (if i < 1318 then decide (33 ≤ count1285 b) else decide (34 ≤ count1285 b))) else (if i < 1320 then decide (35 ≤ count1285 b) else (if i < 1321 then decide (36 ≤ count1285 b) else decide (37 ≤ count1285 b))))) else (if i < 1328 then (if i < 1325 then (if i < 1323 then decide (38 ≤ count1285 b) else (if i < 1324 then decide (39 ≤ count1285 b) else decide (40 ≤ count1285 b))) else (if i < 1326 then decide (41 ≤ count1285 b) else (if i < 1327 then decide (42 ≤ count1285 b) else decide (1 ≤ count1327 b)))) else (if i < 1331 then (if i < 1329 then decide (2 ≤ count1327 b) else (if i < 1330 then decide (1 ≤ count1329 b) else decide (2 ≤ count1329 b))) else (if i < 1333 then (if i < 1332 then decide (3 ≤ count1329 b) else decide (1 ≤ count1332 b)) else (if i < 1334 then decide (2 ≤ count1332 b) else decide (1 ≤ count1334 b))))))) else (if i < 1360 then (if i < 1347 then (if i < 1341 then (if i < 1338 then (if i < 1336 then decide (2 ≤ count1334 b) else (if i < 1337 then decide (3 ≤ count1334 b) else decide (1 ≤ count1337 b))) else (if i < 1339 then decide (2 ≤ count1337 b) else (if i < 1340 then decide (3 ≤ count1337 b) else decide (4 ≤ count1337 b)))) else (if i < 1344 then (if i < 1342 then decide (5 ≤ count1337 b) else (if i < 1343 then decide (6 ≤ count1337 b) else decide (1 ≤ count1343 b))) else (if i < 1345 then decide (2 ≤ count1343 b) else (if i < 1346 then decide (1 ≤ count1345 b) else decide (2 ≤ count1345 b))))) else (if i < 1353 then (if i < 1350 then (if i < 1348 then decide (3 ≤ count1345 b) else (if i < 1349 then decide (1 ≤ count1348 b) else decide (2 ≤ count1348 b))) else (if i < 1351 then decide (1 ≤ count1350 b) else (if i < 1352 then decide (2 ≤ count1350 b) else decide (1 ≤ count1352 b)))) else (if i < 1356 then (if i < 1354 then decide (2 ≤ count1352 b) else (if i < 1355 then decide (3 ≤ count1352 b) else decide (4 ≤ count1352 b))) else (if i < 1358 then (if i < 1357 then decide (1 ≤ count1356 b) else decide (2 ≤ count1356 b)) else (if i < 1359 then decide (3 ≤ count1356 b) else decide (4 ≤ count1356 b)))))) else (if i < 1372 then (if i < 1366 then (if i < 1363 then (if i < 1361 then decide (5 ≤ count1356 b) else (if i < 1362 then decide (6 ≤ count1356 b) else decide (7 ≤ count1356 b))) else (if i < 1364 then decide (1 ≤ count1363 b) else (if i < 1365 then decide (2 ≤ count1363 b) else decide (3 ≤ count1363 b)))) else (if i < 1369 then (if i < 1367 then decide (4 ≤ count1363 b) else (if i < 1368 then decide (5 ≤ count1363 b) else decide (6 ≤ count1363 b))) else (if i < 1370 then decide (7 ≤ count1363 b) else (if i < 1371 then decide (8 ≤ count1363 b) else decide (9 ≤ count1363 b))))) else (if i < 1378 then (if i < 1375 then (if i < 1373 then decide (10 ≤ count1363 b) else (if i < 1374 then decide (11 ≤ count1363 b) else decide (12 ≤ count1363 b))) else (if i < 1376 then decide (13 ≤ count1363 b) else (if i < 1377 then decide (1 ≤ count1376 b) else decide (2 ≤ count1376 b)))) else (if i < 1381 then (if i < 1379 then decide (1 ≤ count1378 b) else (if i < 1380 then decide (2 ≤ count1378 b) else decide (3 ≤ count1378 b))) else (if i < 1383 then (if i < 1382 then decide (1 ≤ count1381 b) else decide (2 ≤ count1381 b)) else (if i < 1384 then decide (1 ≤ count1383 b) else decide (2 ≤ count1383 b))))))))) else (if i < 1484 then (if i < 1434 then (if i < 1409 then (if i < 1397 then (if i < 1391 then (if i < 1388 then (if i < 1386 then decide (1 ≤ count1385 b) else (if i < 1387 then decide (2 ≤ count1385 b) else decide (3 ≤ count1385 b))) else (if i < 1389 then decide (4 ≤ count1385 b) else (if i < 1390 then decide (1 ≤ count1389 b) else decide (2 ≤ count1389 b)))) else (if i < 1394 then (if i < 1392 then decide (3 ≤ count1389 b) else (if i < 1393 then decide (4 ≤ count1389 b) else decide (5 ≤ count1389 b))) else (if i < 1395 then decide (6 ≤ count1389 b) else (if i < 1396 then decide (7 ≤ count1389 b) else decide (1 ≤ count1396 b))))) else (if i < 1403 then (if i < 1400 then (if i < 1398 then decide (2 ≤ count1396 b) else (if i < 1399 then decide (1 ≤ count1398 b) else decide (2 ≤ count1398 b))) else (if i < 1401 then decide (3 ≤ count1398 b) else (if i < 1402 then decide (1 ≤ count1401 b) else decide (2 ≤ count1401 b)))) else (if i < 1406 then (if i < 1404 then decide (1 ≤ count1403 b) else (if i < 1405 then decide (2 ≤ count1403 b) else decide (1 ≤ count1405 b))) else (if i < 1407 then decide (2 ≤ count1405 b) else (if i < 1408 then decide (3 ≤ count1405 b) else decide (4 ≤ count1405 b)))))) else (if i < 1421 then (if i < 1415 then (if i < 1412 then (if i < 1410 then decide (1 ≤ count1409 b) else (if i < 1411 then decide (2 ≤ count1409 b) else decide (3 ≤ count1409 b))) else (if i < 1413 then decide (4 ≤ count1409 b) else (if i < 1414 then decide (5 ≤ count1409 b) else decide (6 ≤ count1409 b)))) else (if i < 1418 then (if i < 1416 then decide (7 ≤ count1409 b) else (if i < 1417 then decide (1 ≤ count1416 b) else decide (2 ≤ count1416 b))) else (if i < 1419 then decide (3 ≤ count1416 b) else (if i < 1420 then decide (4 ≤ count1416 b) else decide (5 ≤ count1416 b))))) else (if i < 1427 then (if i < 1424 then (if i < 1422 then decide (6 ≤ count1416 b) else (if i < 1423 then decide (7 ≤ count1416 b) else decide (8 ≤ count1416 b))) else (if i < 1425 then decide (9 ≤ count1416 b) else (if i < 1426 then decide (10 ≤ count1416 b) else decide (11 ≤ count1416 b)))) else (if i < 1430 then (if i < 1428 then decide (12 ≤ count1416 b) else (if i < 1429 then decide (13 ≤ count1416 b) else decide (14 ≤ count1416 b))) else (if i < 1432 then (if i < 1431 then decide (1 ≤ count1430 b) else decide (2 ≤ count1430 b)) else (if i < 1433 then decide (3 ≤ count1430 b) else decide (4 ≤ count1430 b))))))) else (if i < 1459 then (if i < 1446 then (if i < 1440 then (if i < 1437 then (if i < 1435 then decide (5 ≤ count1430 b) else (if i < 1436 then decide (6 ≤ count1430 b) else decide (7 ≤ count1430 b))) else (if i < 1438 then decide (8 ≤ count1430 b) else (if i < 1439 then decide (9 ≤ count1430 b) else decide (10 ≤ count1430 b)))) else (if i < 1443 then (if i < 1441 then decide (11 ≤ count1430 b) else (if i < 1442 then decide (12 ≤ count1430 b) else decide (13 ≤ count1430 b))) else (if i < 1444 then decide (14 ≤ count1430 b) else (if i < 1445 then decide (15 ≤ count1430 b) else decide (1 ≤ count1445 b))))) else (if i < 1452 then (if i < 1449 then (if i < 1447 then decide (2 ≤ count1445 b) else (if i < 1448 then decide (1 ≤ count1447 b) else decide (2 ≤ count1447 b))) else (if i < 1450 then decide (3 ≤ count1447 b) else (if i < 1451 then decide (1 ≤ count1450 b) else decide (2 ≤ count1450 b)))) else (if i < 1455 then (if i < 1453 then decide (1 ≤ count1452 b) else (if i < 1454 then decide (2 ≤ count1452 b) else decide (1 ≤ count1454 b))) else (if i < 1457 then (if i < 1456 then decide (2 ≤ count1454 b) else decide (3 ≤ count1454 b)) else (if i < 1458 then decide (4 ≤ count1454 b) else decide (1 ≤ count1458 b)))))) else (if i < 1471 then (if i < 1465 then (if i < 1462 then (if i < 1460 then decide (2 ≤ count1458 b) else (if i < 1461 then decide (3 ≤ count1458 b) else decide (4 ≤ count1458 b))) else (if i < 1463 then decide (5 ≤ count1458 b) else (if i < 1464 then decide (6 ≤ count1458 b) else decide (7 ≤ count1458 b)))) else (if i < 1468 then (if i < 1466 then decide (1 ≤ count1465 b) else (if i < 1467 then decide (2 ≤ count1465 b) else decide (1 ≤ count1467 b))) else (if i < 1469 then decide (2 ≤ count1467 b) else (if i < 1470 then decide (3 ≤ count1467 b) else decide (1 ≤ count1470 b))))) else (if i < 1477 then (if i < 1474 then (if i < 1472 then decide (2 ≤ count1470 b) else (if i < 1473 then decide (1 ≤ count1472 b) else decide (2 ≤ count1472 b))) else (if i < 1475 then decide (1 ≤ count1474 b) else (if i < 1476 then decide (2 ≤ count1474 b) else decide (3 ≤ count1474 b)))) else (if i < 1480 then (if i < 1478 then decide (4 ≤ count1474 b) else (if i < 1479 then decide (1 ≤ count1478 b) else decide (2 ≤ count1478 b))) else (if i < 1482 then (if i < 1481 then decide (3 ≤ count1478 b) else decide (4 ≤ count1478 b)) else (if i < 1483 then decide (5 ≤ count1478 b) else decide (6 ≤ count1478 b)))))))) else (if i < 1533 then (if i < 1508 then (if i < 1496 then (if i < 1490 then (if i < 1487 then (if i < 1485 then decide (7 ≤ count1478 b) else (if i < 1486 then decide (1 ≤ count1485 b) else decide (2 ≤ count1485 b))) else (if i < 1488 then decide (3 ≤ count1485 b) else (if i < 1489 then decide (4 ≤ count1485 b) else decide (5 ≤ count1485 b)))) else (if i < 1493 then (if i < 1491 then decide (6 ≤ count1485 b) else (if i < 1492 then decide (7 ≤ count1485 b) else decide (8 ≤ count1485 b))) else (if i < 1494 then decide (9 ≤ count1485 b) else (if i < 1495 then decide (10 ≤ count1485 b) else decide (11 ≤ count1485 b))))) else (if i < 1502 then (if i < 1499 then (if i < 1497 then decide (12 ≤ count1485 b) else (if i < 1498 then decide (13 ≤ count1485 b) else decide (14 ≤ count1485 b))) else (if i < 1500 then decide (1 ≤ count1499 b) else (if i < 1501 then decide (2 ≤ count1499 b) else decide (1 ≤ count1501 b)))) else (if i < 1505 then (if i < 1503 then decide (2 ≤ count1501 b) else (if i < 1504 then decide (3 ≤ count1501 b) else decide (1 ≤ count1504 b))) else (if i < 1506 then decide (2 ≤ count1504 b) else (if i < 1507 then decide (1 ≤ count1506 b) else decide (2 ≤ count1506 b)))))) else (if i < 1520 then (if i < 1514 then (if i < 1511 then (if i < 1509 then decide (1 ≤ count1508 b) else (if i < 1510 then decide (2 ≤ count1508 b) else decide (3 ≤ count1508 b))) else (if i < 1512 then decide (4 ≤ count1508 b) else (if i < 1513 then decide (1 ≤ count1512 b) else decide (2 ≤ count1512 b)))) else (if i < 1517 then (if i < 1515 then decide (3 ≤ count1512 b) else (if i < 1516 then decide (4 ≤ count1512 b) else decide (5 ≤ count1512 b))) else (if i < 1518 then decide (6 ≤ count1512 b) else (if i < 1519 then decide (7 ≤ count1512 b) else decide (1 ≤ count1519 b))))) else (if i < 1526 then (if i < 1523 then (if i < 1521 then decide (2 ≤ count1519 b) else (if i < 1522 then decide (1 ≤ count1521 b) else decide (2 ≤ count1521 b))) else (if i < 1524 then decide (3 ≤ count1521 b) else (if i < 1525 then decide (1 ≤ count1524 b) else decide (2 ≤ count1524 b)))) else (if i < 1529 then (if i < 1527 then decide (1 ≤ count1526 b) else (if i < 1528 then decide (2 ≤ count1526 b) else decide (1 ≤ count1528 b))) else (if i < 1531 then (if i < 1530 then decide (2 ≤ count1528 b) else decide (3 ≤ count1528 b)) else (if i < 1532 then decide (4 ≤ count1528 b) else decide (1 ≤ count1532 b))))))) else (if i < 1558 then (if i < 1545 then (if i < 1539 then (if i < 1536 then (if i < 1534 then decide (2 ≤ count1532 b) else (if i < 1535 then decide (3 ≤ count1532 b) else decide (4 ≤ count1532 b))) else (if i < 1537 then decide (5 ≤ count1532 b) else (if i < 1538 then decide (6 ≤ count1532 b) else decide (7 ≤ count1532 b)))) else (if i < 1542 then (if i < 1540 then decide (1 ≤ count1539 b) else (if i < 1541 then decide (2 ≤ count1539 b) else decide (3 ≤ count1539 b))) else (if i < 1543 then decide (4 ≤ count1539 b) else (if i < 1544 then decide (5 ≤ count1539 b) else decide (6 ≤ count1539 b))))) else (if i < 1551 then (if i < 1548 then (if i < 1546 then decide (7 ≤ count1539 b) else (if i < 1547 then decide (8 ≤ count1539 b) else decide (9 ≤ count1539 b))) else (if i < 1549 then decide (10 ≤ count1539 b) else (if i < 1550 then decide (11 ≤ count1539 b) else decide (12 ≤ count1539 b)))) else (if i < 1554 then (if i < 1552 then decide (13 ≤ count1539 b) else (if i < 1553 then decide (14 ≤ count1539 b) else decide (1 ≤ count1553 b))) else (if i < 1556 then (if i < 1555 then decide (2 ≤ count1553 b) else decide (3 ≤ count1553 b)) else (if i < 1557 then decide (4 ≤ count1553 b) else decide (5 ≤ count1553 b)))))) else (if i < 1570 then (if i < 1564 then (if i < 1561 then (if i < 1559 then decide (6 ≤ count1553 b) else (if i < 1560 then decide (7 ≤ count1553 b) else decide (8 ≤ count1553 b))) else (if i < 1562 then decide (9 ≤ count1553 b) else (if i < 1563 then decide (10 ≤ count1553 b) else decide (11 ≤ count1553 b)))) else (if i < 1567 then (if i < 1565 then decide (12 ≤ count1553 b) else (if i < 1566 then decide (13 ≤ count1553 b) else decide (14 ≤ count1553 b))) else (if i < 1568 then decide (15 ≤ count1553 b) else (if i < 1569 then decide (1 ≤ count1568 b) else decide (2 ≤ count1568 b))))) else (if i < 1576 then (if i < 1573 then (if i < 1571 then decide (3 ≤ count1568 b) else (if i < 1572 then decide (4 ≤ count1568 b) else decide (5 ≤ count1568 b))) else (if i < 1574 then decide (6 ≤ count1568 b) else (if i < 1575 then decide (7 ≤ count1568 b) else decide (8 ≤ count1568 b)))) else (if i < 1579 then (if i < 1577 then decide (9 ≤ count1568 b) else (if i < 1578 then decide (10 ≤ count1568 b) else decide (11 ≤ count1568 b))) else (if i < 1581 then (if i < 1580 then decide (12 ≤ count1568 b) else decide (13 ≤ count1568 b)) else (if i < 1582 then decide (14 ≤ count1568 b) else decide (15 ≤ count1568 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (11 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (25 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (27 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (65 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (67 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (71 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (75 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (77 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (79 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (80 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (81 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (82 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (83 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (84 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (88 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (90 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (91 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (92 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (94 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (95 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (129 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (130 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (131 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (135 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (137 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (141 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (143 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (144 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (145 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (146 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (147 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (148 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (154 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (156 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (157 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (158 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (159 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (192 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (193 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (198 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (199 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (200 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (201 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (203 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (204 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (206 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (213 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (214 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (215 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (217 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (218 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (219 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (221 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (288 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (289 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (294 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (296 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (300 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (302 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (310 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (321 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (326 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (327 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (328 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (329 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (331 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (332 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (334 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (338 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (340 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (341 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (342 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (343 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (345 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (346 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (347 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (385 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (391 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (393 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (402 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (405 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (406 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (407 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (409 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (411 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (413 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (417 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (433 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (434 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (481 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (486 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (487 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (494 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (502 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (77 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (81 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (143 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (145 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (147 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (203 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (213 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (289 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (294 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (296 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (300 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (302 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (334 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (405 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (411 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (433 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (1 ≤ count223 (baseVal q)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (1 ≤ count225 (baseVal q)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value274 (q : Snake 81) : valuation q 274 = decide (2 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value382 (q : Snake 81) : valuation q 382 = decide (2 ≤ count381 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value408 (q : Snake 81) : valuation q 408 = decide (2 ≤ count407 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value440 (q : Snake 81) : valuation q 440 = decide (2 ≤ count439 (baseVal q)) := rfl
theorem value1327 (q : Snake 81) : valuation q 1327 = decide (1 ≤ count1327 (baseVal q)) := rfl
theorem value1328 (q : Snake 81) : valuation q 1328 = decide (2 ≤ count1327 (baseVal q)) := rfl
theorem value1329 (q : Snake 81) : valuation q 1329 = decide (1 ≤ count1329 (baseVal q)) := rfl
theorem value1330 (q : Snake 81) : valuation q 1330 = decide (2 ≤ count1329 (baseVal q)) := rfl
theorem value1331 (q : Snake 81) : valuation q 1331 = decide (3 ≤ count1329 (baseVal q)) := rfl
theorem value1332 (q : Snake 81) : valuation q 1332 = decide (1 ≤ count1332 (baseVal q)) := rfl
theorem value1333 (q : Snake 81) : valuation q 1333 = decide (2 ≤ count1332 (baseVal q)) := rfl
theorem value1334 (q : Snake 81) : valuation q 1334 = decide (1 ≤ count1334 (baseVal q)) := rfl
theorem value1335 (q : Snake 81) : valuation q 1335 = decide (2 ≤ count1334 (baseVal q)) := rfl
theorem value1336 (q : Snake 81) : valuation q 1336 = decide (3 ≤ count1334 (baseVal q)) := rfl
theorem value1338 (q : Snake 81) : valuation q 1338 = decide (2 ≤ count1337 (baseVal q)) := rfl
theorem value1339 (q : Snake 81) : valuation q 1339 = decide (3 ≤ count1337 (baseVal q)) := rfl
theorem value1340 (q : Snake 81) : valuation q 1340 = decide (4 ≤ count1337 (baseVal q)) := rfl
theorem value1341 (q : Snake 81) : valuation q 1341 = decide (5 ≤ count1337 (baseVal q)) := rfl
theorem value1343 (q : Snake 81) : valuation q 1343 = decide (1 ≤ count1343 (baseVal q)) := rfl
theorem value1344 (q : Snake 81) : valuation q 1344 = decide (2 ≤ count1343 (baseVal q)) := rfl
theorem value1345 (q : Snake 81) : valuation q 1345 = decide (1 ≤ count1345 (baseVal q)) := rfl
theorem value1346 (q : Snake 81) : valuation q 1346 = decide (2 ≤ count1345 (baseVal q)) := rfl
theorem value1347 (q : Snake 81) : valuation q 1347 = decide (3 ≤ count1345 (baseVal q)) := rfl
theorem value1348 (q : Snake 81) : valuation q 1348 = decide (1 ≤ count1348 (baseVal q)) := rfl
theorem value1349 (q : Snake 81) : valuation q 1349 = decide (2 ≤ count1348 (baseVal q)) := rfl
theorem value1350 (q : Snake 81) : valuation q 1350 = decide (1 ≤ count1350 (baseVal q)) := rfl
theorem value1352 (q : Snake 81) : valuation q 1352 = decide (1 ≤ count1352 (baseVal q)) := rfl
theorem value1353 (q : Snake 81) : valuation q 1353 = decide (2 ≤ count1352 (baseVal q)) := rfl
theorem value1354 (q : Snake 81) : valuation q 1354 = decide (3 ≤ count1352 (baseVal q)) := rfl
theorem value1356 (q : Snake 81) : valuation q 1356 = decide (1 ≤ count1356 (baseVal q)) := rfl
theorem value1357 (q : Snake 81) : valuation q 1357 = decide (2 ≤ count1356 (baseVal q)) := rfl
theorem value1358 (q : Snake 81) : valuation q 1358 = decide (3 ≤ count1356 (baseVal q)) := rfl
theorem value1359 (q : Snake 81) : valuation q 1359 = decide (4 ≤ count1356 (baseVal q)) := rfl
theorem value1366 (q : Snake 81) : valuation q 1366 = decide (4 ≤ count1363 (baseVal q)) := rfl
theorem value1367 (q : Snake 81) : valuation q 1367 = decide (5 ≤ count1363 (baseVal q)) := rfl
theorem value1368 (q : Snake 81) : valuation q 1368 = decide (6 ≤ count1363 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (1 ≤ count1376 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (2 ≤ count1376 (baseVal q)) := rfl
theorem value1378 (q : Snake 81) : valuation q 1378 = decide (1 ≤ count1378 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (2 ≤ count1378 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (1 ≤ count1381 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (1 ≤ count1383 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (2 ≤ count1383 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (1 ≤ count1385 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (2 ≤ count1385 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (3 ≤ count1385 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (1 ≤ count1389 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (2 ≤ count1389 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (3 ≤ count1389 (baseVal q)) := rfl
theorem value1392 (q : Snake 81) : valuation q 1392 = decide (4 ≤ count1389 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (1 ≤ count1396 (baseVal q)) := rfl
theorem value1397 (q : Snake 81) : valuation q 1397 = decide (2 ≤ count1396 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (1 ≤ count1398 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (2 ≤ count1398 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (3 ≤ count1398 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (1 ≤ count1401 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (2 ≤ count1401 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (1 ≤ count1403 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (2 ≤ count1403 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (1 ≤ count1405 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (2 ≤ count1405 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (3 ≤ count1405 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (1 ≤ count1409 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (2 ≤ count1409 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (3 ≤ count1409 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (3 ≤ count1416 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (4 ≤ count1416 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (5 ≤ count1416 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (8 ≤ count1430 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (9 ≤ count1430 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (10 ≤ count1430 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (1 ≤ count1445 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (1 ≤ count1447 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (2 ≤ count1447 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (1 ≤ count1450 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (2 ≤ count1452 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (1 ≤ count1454 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (2 ≤ count1454 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (1 ≤ count1458 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (2 ≤ count1458 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (3 ≤ count1458 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (1 ≤ count1465 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (1 ≤ count1467 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (2 ≤ count1467 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (1 ≤ count1470 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (2 ≤ count1470 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (1 ≤ count1472 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (2 ≤ count1472 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (1 ≤ count1474 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (2 ≤ count1474 (baseVal q)) := rfl
theorem value1476 (q : Snake 81) : valuation q 1476 = decide (3 ≤ count1474 (baseVal q)) := rfl
theorem value1478 (q : Snake 81) : valuation q 1478 = decide (1 ≤ count1478 (baseVal q)) := rfl
theorem value1479 (q : Snake 81) : valuation q 1479 = decide (2 ≤ count1478 (baseVal q)) := rfl
theorem value1480 (q : Snake 81) : valuation q 1480 = decide (3 ≤ count1478 (baseVal q)) := rfl
theorem value1481 (q : Snake 81) : valuation q 1481 = decide (4 ≤ count1478 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (3 ≤ count1485 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (4 ≤ count1485 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (1 ≤ count1499 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (2 ≤ count1499 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (1 ≤ count1501 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (2 ≤ count1501 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (3 ≤ count1501 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (1 ≤ count1504 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (2 ≤ count1504 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (1 ≤ count1506 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (2 ≤ count1506 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (1 ≤ count1508 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (2 ≤ count1508 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (3 ≤ count1508 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (1 ≤ count1512 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (2 ≤ count1512 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (3 ≤ count1512 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (4 ≤ count1512 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (1 ≤ count1519 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (1 ≤ count1521 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (1 ≤ count1524 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (1 ≤ count1528 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (1 ≤ count1532 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (2 ≤ count1539 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (3 ≤ count1539 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (4 ≤ count1539 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (5 ≤ count1539 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (5 ≤ count1553 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (6 ≤ count1553 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (7 ≤ count1553 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (15 ≤ count1568 (baseVal q)) := rfl
theorem meaningNeg106 (b : Nat → Bool) : literal (valuationOf b) (-106) = decide (1 ≤ countLit b [-106]) := by
  change literal b (-106) = decide (1 ≤ countLit b [-106])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-106) <;> decide
theorem meaningNeg103 (b : Nat → Bool) : literal (valuationOf b) (-103) = decide (1 ≤ countLit b [-103]) := by
  change literal b (-103) = decide (1 ≤ countLit b [-103])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-103) <;> decide
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
theorem meaningNeg59 (b : Nat → Bool) : literal (valuationOf b) (-59) = decide (1 ≤ countLit b [-59]) := by
  change literal b (-59) = decide (1 ≤ countLit b [-59])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-59) <;> decide
theorem meaningNeg57 (b : Nat → Bool) : literal (valuationOf b) (-57) = decide (1 ≤ countLit b [-57]) := by
  change literal b (-57) = decide (1 ≤ countLit b [-57])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-57) <;> decide
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
theorem meaningNeg40 (b : Nat → Bool) : literal (valuationOf b) (-40) = decide (1 ≤ countLit b [-40]) := by
  change literal b (-40) = decide (1 ≤ countLit b [-40])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-40) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning114 (b : Nat → Bool) : literal (valuationOf b) (114) = decide (1 ≤ countLit b [114]) := by
  change literal b (114) = decide (1 ≤ countLit b [114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (114) <;> decide
theorem meaning120 (b : Nat → Bool) : literal (valuationOf b) (120) = decide (1 ≤ countLit b [120]) := by
  change literal b (120) = decide (1 ≤ countLit b [120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (120) <;> decide
theorem meaning132 (b : Nat → Bool) : literal (valuationOf b) (132) = decide (1 ≤ countLit b [132]) := by
  change literal b (132) = decide (1 ≤ countLit b [132])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (132) <;> decide
theorem meaning134 (b : Nat → Bool) : literal (valuationOf b) (134) = decide (1 ≤ countLit b [134]) := by
  change literal b (134) = decide (1 ≤ countLit b [134])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (134) <;> decide
theorem meaning140 (b : Nat → Bool) : literal (valuationOf b) (140) = decide (1 ≤ countLit b [140]) := by
  change literal b (140) = decide (1 ≤ countLit b [140])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (140) <;> decide
theorem meaning143 (b : Nat → Bool) : literal (valuationOf b) (143) = decide (1 ≤ countLit b [143]) := by
  change literal b (143) = decide (1 ≤ countLit b [143])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (143) <;> decide
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
theorem meaning157 (b : Nat → Bool) : literal (valuationOf b) (157) = decide (1 ≤ countLit b [157]) := by
  change literal b (157) = decide (1 ≤ countLit b [157])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (157) <;> decide
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
theorem meaning181 (b : Nat → Bool) : literal (valuationOf b) (181) = decide (1 ≤ countLit b [181]) := by
  change literal b (181) = decide (1 ≤ countLit b [181])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (181) <;> decide
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
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) 223 = decide (1 ≤ count223 b) := rfl
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) 225 = decide (1 ≤ count225 b) := rfl
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning274 (b : Nat → Bool) : literal (valuationOf b) 274 = decide (2 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning382 (b : Nat → Bool) : literal (valuationOf b) 382 = decide (2 ≤ count381 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning408 (b : Nat → Bool) : literal (valuationOf b) 408 = decide (2 ≤ count407 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning440 (b : Nat → Bool) : literal (valuationOf b) 440 = decide (2 ≤ count439 b) := rfl
theorem meaning1327 (b : Nat → Bool) : literal (valuationOf b) 1327 = decide (1 ≤ count1327 b) := rfl
theorem meaning1328 (b : Nat → Bool) : literal (valuationOf b) 1328 = decide (2 ≤ count1327 b) := rfl
theorem meaning1329 (b : Nat → Bool) : literal (valuationOf b) 1329 = decide (1 ≤ count1329 b) := rfl
theorem meaning1330 (b : Nat → Bool) : literal (valuationOf b) 1330 = decide (2 ≤ count1329 b) := rfl
theorem meaning1331 (b : Nat → Bool) : literal (valuationOf b) 1331 = decide (3 ≤ count1329 b) := rfl
theorem meaning1332 (b : Nat → Bool) : literal (valuationOf b) 1332 = decide (1 ≤ count1332 b) := rfl
theorem meaning1333 (b : Nat → Bool) : literal (valuationOf b) 1333 = decide (2 ≤ count1332 b) := rfl
theorem meaning1334 (b : Nat → Bool) : literal (valuationOf b) 1334 = decide (1 ≤ count1334 b) := rfl
theorem meaning1335 (b : Nat → Bool) : literal (valuationOf b) 1335 = decide (2 ≤ count1334 b) := rfl
theorem meaning1336 (b : Nat → Bool) : literal (valuationOf b) 1336 = decide (3 ≤ count1334 b) := rfl
theorem meaning1338 (b : Nat → Bool) : literal (valuationOf b) 1338 = decide (2 ≤ count1337 b) := rfl
theorem meaning1339 (b : Nat → Bool) : literal (valuationOf b) 1339 = decide (3 ≤ count1337 b) := rfl
theorem meaning1340 (b : Nat → Bool) : literal (valuationOf b) 1340 = decide (4 ≤ count1337 b) := rfl
theorem meaning1341 (b : Nat → Bool) : literal (valuationOf b) 1341 = decide (5 ≤ count1337 b) := rfl
theorem meaning1343 (b : Nat → Bool) : literal (valuationOf b) 1343 = decide (1 ≤ count1343 b) := rfl
theorem meaning1344 (b : Nat → Bool) : literal (valuationOf b) 1344 = decide (2 ≤ count1343 b) := rfl
theorem meaning1345 (b : Nat → Bool) : literal (valuationOf b) 1345 = decide (1 ≤ count1345 b) := rfl
theorem meaning1346 (b : Nat → Bool) : literal (valuationOf b) 1346 = decide (2 ≤ count1345 b) := rfl
theorem meaning1347 (b : Nat → Bool) : literal (valuationOf b) 1347 = decide (3 ≤ count1345 b) := rfl
theorem meaning1348 (b : Nat → Bool) : literal (valuationOf b) 1348 = decide (1 ≤ count1348 b) := rfl
theorem meaning1349 (b : Nat → Bool) : literal (valuationOf b) 1349 = decide (2 ≤ count1348 b) := rfl
theorem meaning1350 (b : Nat → Bool) : literal (valuationOf b) 1350 = decide (1 ≤ count1350 b) := rfl
theorem meaning1352 (b : Nat → Bool) : literal (valuationOf b) 1352 = decide (1 ≤ count1352 b) := rfl
theorem meaning1353 (b : Nat → Bool) : literal (valuationOf b) 1353 = decide (2 ≤ count1352 b) := rfl
theorem meaning1354 (b : Nat → Bool) : literal (valuationOf b) 1354 = decide (3 ≤ count1352 b) := rfl
theorem meaning1356 (b : Nat → Bool) : literal (valuationOf b) 1356 = decide (1 ≤ count1356 b) := rfl
theorem meaning1357 (b : Nat → Bool) : literal (valuationOf b) 1357 = decide (2 ≤ count1356 b) := rfl
theorem meaning1358 (b : Nat → Bool) : literal (valuationOf b) 1358 = decide (3 ≤ count1356 b) := rfl
theorem meaning1359 (b : Nat → Bool) : literal (valuationOf b) 1359 = decide (4 ≤ count1356 b) := rfl
theorem meaning1366 (b : Nat → Bool) : literal (valuationOf b) 1366 = decide (4 ≤ count1363 b) := rfl
theorem meaning1367 (b : Nat → Bool) : literal (valuationOf b) 1367 = decide (5 ≤ count1363 b) := rfl
theorem meaning1368 (b : Nat → Bool) : literal (valuationOf b) 1368 = decide (6 ≤ count1363 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (1 ≤ count1376 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (2 ≤ count1376 b) := rfl
theorem meaning1378 (b : Nat → Bool) : literal (valuationOf b) 1378 = decide (1 ≤ count1378 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (2 ≤ count1378 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (1 ≤ count1381 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (1 ≤ count1383 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (2 ≤ count1383 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (1 ≤ count1385 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (2 ≤ count1385 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (3 ≤ count1385 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (1 ≤ count1389 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (2 ≤ count1389 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (3 ≤ count1389 b) := rfl
theorem meaning1392 (b : Nat → Bool) : literal (valuationOf b) 1392 = decide (4 ≤ count1389 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (1 ≤ count1396 b) := rfl
theorem meaning1397 (b : Nat → Bool) : literal (valuationOf b) 1397 = decide (2 ≤ count1396 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (1 ≤ count1398 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (2 ≤ count1398 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (3 ≤ count1398 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (1 ≤ count1401 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (2 ≤ count1401 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (1 ≤ count1403 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (2 ≤ count1403 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (1 ≤ count1405 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (2 ≤ count1405 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (3 ≤ count1405 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (1 ≤ count1409 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (2 ≤ count1409 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (3 ≤ count1409 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (3 ≤ count1416 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (4 ≤ count1416 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (5 ≤ count1416 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (8 ≤ count1430 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (9 ≤ count1430 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (10 ≤ count1430 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (1 ≤ count1445 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (1 ≤ count1447 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (2 ≤ count1447 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (1 ≤ count1450 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (2 ≤ count1452 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (1 ≤ count1454 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (2 ≤ count1454 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (1 ≤ count1458 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (2 ≤ count1458 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (3 ≤ count1458 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (1 ≤ count1465 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (1 ≤ count1467 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (2 ≤ count1467 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (1 ≤ count1470 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (2 ≤ count1470 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (1 ≤ count1472 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (2 ≤ count1472 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (1 ≤ count1474 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (2 ≤ count1474 b) := rfl
theorem meaning1476 (b : Nat → Bool) : literal (valuationOf b) 1476 = decide (3 ≤ count1474 b) := rfl
theorem meaning1478 (b : Nat → Bool) : literal (valuationOf b) 1478 = decide (1 ≤ count1478 b) := rfl
theorem meaning1479 (b : Nat → Bool) : literal (valuationOf b) 1479 = decide (2 ≤ count1478 b) := rfl
theorem meaning1480 (b : Nat → Bool) : literal (valuationOf b) 1480 = decide (3 ≤ count1478 b) := rfl
theorem meaning1481 (b : Nat → Bool) : literal (valuationOf b) 1481 = decide (4 ≤ count1478 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (2 ≤ count1485 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (3 ≤ count1485 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (4 ≤ count1485 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (1 ≤ count1499 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (2 ≤ count1499 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (1 ≤ count1501 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (2 ≤ count1501 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (3 ≤ count1501 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (1 ≤ count1504 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (2 ≤ count1504 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (1 ≤ count1506 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (2 ≤ count1506 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (1 ≤ count1508 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (2 ≤ count1508 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (3 ≤ count1508 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (1 ≤ count1512 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (2 ≤ count1512 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (3 ≤ count1512 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (4 ≤ count1512 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (1 ≤ count1519 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (1 ≤ count1521 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (1 ≤ count1524 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (1 ≤ count1528 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (1 ≤ count1532 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (2 ≤ count1539 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (3 ≤ count1539 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (4 ≤ count1539 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (5 ≤ count1539 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (5 ≤ count1553 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (6 ≤ count1553 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (7 ≤ count1553 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (15 ≤ count1568 b) := rfl
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
end Snake9.Regrowth.E112148
