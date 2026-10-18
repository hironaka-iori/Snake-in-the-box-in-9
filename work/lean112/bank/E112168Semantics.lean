import E112168Data
namespace Snake9.Regrowth.E112168
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 114 then (if i < 57 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (18 : Vertex)) else decide (InPath q (19 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (22 : Vertex)) else decide (InPath q (24 : Vertex))) else (if i < 6 then decide (InPath q (28 : Vertex)) else decide (InPath q (30 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (66 : Vertex)) else (if i < 9 then decide (InPath q (67 : Vertex)) else decide (InPath q (68 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (73 : Vertex)) else decide (InPath q (74 : Vertex))) else (if i < 13 then decide (InPath q (76 : Vertex)) else decide (InPath q (78 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (80 : Vertex)) else (if i < 16 then decide (InPath q (84 : Vertex)) else decide (InPath q (85 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (87 : Vertex)) else decide (InPath q (88 : Vertex))) else (if i < 20 then decide (InPath q (89 : Vertex)) else decide (InPath q (90 : Vertex))))) else (if i < 24 then (if i < 22 then decide (InPath q (91 : Vertex)) else (if i < 23 then decide (InPath q (95 : Vertex)) else decide (InPath q (130 : Vertex)))) else (if i < 26 then (if i < 25 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex))) else (if i < 27 then decide (InPath q (134 : Vertex)) else decide (InPath q (135 : Vertex))))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then decide (InPath q (136 : Vertex)) else (if i < 30 then decide (InPath q (137 : Vertex)) else decide (InPath q (138 : Vertex)))) else (if i < 33 then (if i < 32 then decide (InPath q (140 : Vertex)) else decide (InPath q (142 : Vertex))) else (if i < 34 then decide (InPath q (144 : Vertex)) else decide (InPath q (148 : Vertex))))) else (if i < 38 then (if i < 36 then decide (InPath q (149 : Vertex)) else (if i < 37 then decide (InPath q (151 : Vertex)) else decide (InPath q (153 : Vertex)))) else (if i < 40 then (if i < 39 then decide (InPath q (154 : Vertex)) else decide (InPath q (155 : Vertex))) else (if i < 41 then decide (InPath q (157 : Vertex)) else decide (InPath q (159 : Vertex)))))) else (if i < 49 then (if i < 45 then (if i < 43 then decide (InPath q (192 : Vertex)) else (if i < 44 then decide (InPath q (193 : Vertex)) else decide (InPath q (194 : Vertex)))) else (if i < 47 then (if i < 46 then decide (InPath q (195 : Vertex)) else decide (InPath q (197 : Vertex))) else (if i < 48 then decide (InPath q (199 : Vertex)) else decide (InPath q (201 : Vertex))))) else (if i < 53 then (if i < 51 then (if i < 50 then decide (InPath q (202 : Vertex)) else decide (InPath q (204 : Vertex))) else (if i < 52 then decide (InPath q (205 : Vertex)) else decide (InPath q (206 : Vertex)))) else (if i < 55 then (if i < 54 then decide (InPath q (207 : Vertex)) else decide (InPath q (208 : Vertex))) else (if i < 56 then decide (InPath q (209 : Vertex)) else decide (InPath q (210 : Vertex)))))))) else (if i < 85 then (if i < 71 then (if i < 64 then (if i < 60 then (if i < 58 then decide (InPath q (211 : Vertex)) else (if i < 59 then decide (InPath q (214 : Vertex)) else decide (InPath q (216 : Vertex)))) else (if i < 62 then (if i < 61 then decide (InPath q (217 : Vertex)) else decide (InPath q (218 : Vertex))) else (if i < 63 then decide (InPath q (220 : Vertex)) else decide (InPath q (221 : Vertex))))) else (if i < 67 then (if i < 65 then decide (InPath q (222 : Vertex)) else (if i < 66 then decide (InPath q (264 : Vertex)) else decide (InPath q (268 : Vertex)))) else (if i < 69 then (if i < 68 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex))) else (if i < 70 then decide (InPath q (327 : Vertex)) else decide (InPath q (328 : Vertex)))))) else (if i < 78 then (if i < 74 then (if i < 72 then decide (InPath q (329 : Vertex)) else (if i < 73 then decide (InPath q (333 : Vertex)) else decide (InPath q (335 : Vertex)))) else (if i < 76 then (if i < 75 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex))) else (if i < 77 then decide (InPath q (339 : Vertex)) else decide (InPath q (346 : Vertex))))) else (if i < 81 then (if i < 79 then decide (InPath q (348 : Vertex)) else (if i < 80 then decide (InPath q (349 : Vertex)) else decide (InPath q (350 : Vertex)))) else (if i < 83 then (if i < 82 then decide (InPath q (384 : Vertex)) else decide (InPath q (385 : Vertex))) else (if i < 84 then decide (InPath q (389 : Vertex)) else decide (InPath q (391 : Vertex))))))) else (if i < 99 then (if i < 92 then (if i < 88 then (if i < 86 then decide (InPath q (392 : Vertex)) else (if i < 87 then decide (InPath q (393 : Vertex)) else decide (InPath q (397 : Vertex)))) else (if i < 90 then (if i < 89 then decide (InPath q (399 : Vertex)) else decide (InPath q (401 : Vertex))) else (if i < 91 then decide (InPath q (402 : Vertex)) else decide (InPath q (403 : Vertex))))) else (if i < 95 then (if i < 93 then decide (InPath q (406 : Vertex)) else (if i < 94 then decide (InPath q (410 : Vertex)) else decide (InPath q (412 : Vertex)))) else (if i < 97 then (if i < 96 then decide (InPath q (413 : Vertex)) else decide (InPath q (414 : Vertex))) else (if i < 98 then decide (InPath q (450 : Vertex)) else decide (InPath q (451 : Vertex)))))) else (if i < 106 then (if i < 102 then (if i < 100 then decide (InPath q (452 : Vertex)) else (if i < 101 then decide (InPath q (453 : Vertex)) else decide (InPath q (457 : Vertex)))) else (if i < 104 then (if i < 103 then decide (InPath q (458 : Vertex)) else decide (InPath q (459 : Vertex))) else (if i < 105 then decide (InPath q (460 : Vertex)) else decide (InPath q (462 : Vertex))))) else (if i < 110 then (if i < 108 then (if i < 107 then decide (InPath q (464 : Vertex)) else decide (InPath q (468 : Vertex))) else (if i < 109 then decide (InPath q (469 : Vertex)) else decide (InPath q (470 : Vertex)))) else (if i < 112 then (if i < 111 then decide (InPath q (471 : Vertex)) else decide (InPath q (472 : Vertex))) else (if i < 113 then decide (InPath q (473 : Vertex)) else decide (InPath q (475 : Vertex))))))))) else (if i < 171 then (if i < 142 then (if i < 128 then (if i < 121 then (if i < 117 then (if i < 115 then decide (InPath q (479 : Vertex)) else (if i < 116 then decide (BallClauseLogic.Endpoint q (18 : Vertex)) else decide (BallClauseLogic.Endpoint q (19 : Vertex)))) else (if i < 119 then (if i < 118 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (24 : Vertex))) else (if i < 120 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (30 : Vertex))))) else (if i < 124 then (if i < 122 then decide (BallClauseLogic.Endpoint q (66 : Vertex)) else (if i < 123 then decide (BallClauseLogic.Endpoint q (67 : Vertex)) else decide (BallClauseLogic.Endpoint q (68 : Vertex)))) else (if i < 126 then (if i < 125 then decide (BallClauseLogic.Endpoint q (73 : Vertex)) else decide (BallClauseLogic.Endpoint q (74 : Vertex))) else (if i < 127 then decide (BallClauseLogic.Endpoint q (76 : Vertex)) else decide (BallClauseLogic.Endpoint q (78 : Vertex)))))) else (if i < 135 then (if i < 131 then (if i < 129 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else (if i < 130 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (85 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (87 : Vertex)) else decide (BallClauseLogic.Endpoint q (88 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (89 : Vertex)) else decide (BallClauseLogic.Endpoint q (90 : Vertex))))) else (if i < 138 then (if i < 136 then decide (BallClauseLogic.Endpoint q (91 : Vertex)) else (if i < 137 then decide (BallClauseLogic.Endpoint q (95 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex)))) else (if i < 140 then (if i < 139 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex))) else (if i < 141 then decide (BallClauseLogic.Endpoint q (134 : Vertex)) else decide (BallClauseLogic.Endpoint q (135 : Vertex))))))) else (if i < 156 then (if i < 149 then (if i < 145 then (if i < 143 then decide (BallClauseLogic.Endpoint q (136 : Vertex)) else (if i < 144 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (138 : Vertex)))) else (if i < 147 then (if i < 146 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (142 : Vertex))) else (if i < 148 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))))) else (if i < 152 then (if i < 150 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else (if i < 151 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (153 : Vertex)))) else (if i < 154 then (if i < 153 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else decide (BallClauseLogic.Endpoint q (155 : Vertex))) else (if i < 155 then decide (BallClauseLogic.Endpoint q (157 : Vertex)) else decide (BallClauseLogic.Endpoint q (159 : Vertex)))))) else (if i < 163 then (if i < 159 then (if i < 157 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else (if i < 158 then decide (BallClauseLogic.Endpoint q (193 : Vertex)) else decide (BallClauseLogic.Endpoint q (194 : Vertex)))) else (if i < 161 then (if i < 160 then decide (BallClauseLogic.Endpoint q (195 : Vertex)) else decide (BallClauseLogic.Endpoint q (197 : Vertex))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (199 : Vertex)) else decide (BallClauseLogic.Endpoint q (201 : Vertex))))) else (if i < 167 then (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (202 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (205 : Vertex)) else decide (BallClauseLogic.Endpoint q (206 : Vertex)))) else (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else decide (BallClauseLogic.Endpoint q (208 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else decide (BallClauseLogic.Endpoint q (210 : Vertex)))))))) else (if i < 200 then (if i < 185 then (if i < 178 then (if i < 174 then (if i < 172 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else (if i < 173 then decide (BallClauseLogic.Endpoint q (214 : Vertex)) else decide (BallClauseLogic.Endpoint q (216 : Vertex)))) else (if i < 176 then (if i < 175 then decide (BallClauseLogic.Endpoint q (217 : Vertex)) else decide (BallClauseLogic.Endpoint q (218 : Vertex))) else (if i < 177 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex))))) else (if i < 181 then (if i < 179 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else (if i < 180 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex)))) else (if i < 183 then (if i < 182 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else decide (BallClauseLogic.Endpoint q (321 : Vertex))) else (if i < 184 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (328 : Vertex)))))) else (if i < 192 then (if i < 188 then (if i < 186 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else (if i < 187 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (335 : Vertex)))) else (if i < 190 then (if i < 189 then decide (BallClauseLogic.Endpoint q (337 : Vertex)) else decide (BallClauseLogic.Endpoint q (338 : Vertex))) else (if i < 191 then decide (BallClauseLogic.Endpoint q (339 : Vertex)) else decide (BallClauseLogic.Endpoint q (346 : Vertex))))) else (if i < 196 then (if i < 194 then (if i < 193 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else decide (BallClauseLogic.Endpoint q (349 : Vertex))) else (if i < 195 then decide (BallClauseLogic.Endpoint q (350 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex)))) else (if i < 198 then (if i < 197 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (389 : Vertex))) else (if i < 199 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (392 : Vertex))))))) else (if i < 214 then (if i < 207 then (if i < 203 then (if i < 201 then decide (BallClauseLogic.Endpoint q (393 : Vertex)) else (if i < 202 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else decide (BallClauseLogic.Endpoint q (399 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (402 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (406 : Vertex))))) else (if i < 210 then (if i < 208 then decide (BallClauseLogic.Endpoint q (410 : Vertex)) else (if i < 209 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex)))) else (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else decide (BallClauseLogic.Endpoint q (450 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (451 : Vertex)) else decide (BallClauseLogic.Endpoint q (452 : Vertex)))))) else (if i < 221 then (if i < 217 then (if i < 215 then decide (BallClauseLogic.Endpoint q (453 : Vertex)) else (if i < 216 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else decide (BallClauseLogic.Endpoint q (458 : Vertex)))) else (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (459 : Vertex)) else decide (BallClauseLogic.Endpoint q (460 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (464 : Vertex))))) else (if i < 225 then (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (468 : Vertex)) else decide (BallClauseLogic.Endpoint q (469 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (470 : Vertex)) else decide (BallClauseLogic.Endpoint q (471 : Vertex)))) else (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (472 : Vertex)) else decide (BallClauseLogic.Endpoint q (473 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (475 : Vertex)) else decide (BallClauseLogic.Endpoint q (479 : Vertex))))))))))
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
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [178, 179, 180]
def count355 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count359 (b : Nat → Bool) : Nat := countLit b [181, 182, 184, 185]
def count361 (b : Nat → Bool) : Nat := countLit b [178, 179, 180, 181, 182, 184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185]
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
def count391 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199]
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
def count449 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count451 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count453 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count455 (b : Nat → Bool) : Nat := countLit b [1, 4, 6]
def count458 (b : Nat → Bool) : Nat := countLit b [7, 9]
def count460 (b : Nat → Bool) : Nat := countLit b [13, 14]
def count462 (b : Nat → Bool) : Nat := countLit b [7, 9, 13, 14]
def count466 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 13, 14]
def count473 (b : Nat → Bool) : Nat := countLit b [19, 20]
def count475 (b : Nat → Bool) : Nat := countLit b [16, 19, 20]
def count478 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count480 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count482 (b : Nat → Bool) : Nat := countLit b [22, 23, 25, 27]
def count486 (b : Nat → Bool) : Nat := countLit b [16, 19, 20, 22, 23, 25, 27]
def count493 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 13, 14, 16, 19, 20, 22, 23, 25, 27]
def count507 (b : Nat → Bool) : Nat := countLit b [32, 33]
def count509 (b : Nat → Bool) : Nat := countLit b [28, 32, 33]
def count512 (b : Nat → Bool) : Nat := countLit b [35, 37]
def count514 (b : Nat → Bool) : Nat := countLit b [38, 41]
def count516 (b : Nat → Bool) : Nat := countLit b [35, 37, 38, 41]
def count520 (b : Nat → Bool) : Nat := countLit b [28, 32, 33, 35, 37, 38, 41]
def count527 (b : Nat → Bool) : Nat := countLit b [42, 45]
def count529 (b : Nat → Bool) : Nat := countLit b [46, 48]
def count531 (b : Nat → Bool) : Nat := countLit b [42, 45, 46, 48]
def count535 (b : Nat → Bool) : Nat := countLit b [49, 50]
def count537 (b : Nat → Bool) : Nat := countLit b [53, 55]
def count539 (b : Nat → Bool) : Nat := countLit b [49, 50, 53, 55]
def count543 (b : Nat → Bool) : Nat := countLit b [42, 45, 46, 48, 49, 50, 53, 55]
def count551 (b : Nat → Bool) : Nat := countLit b [28, 32, 33, 35, 37, 38, 41, 42, 45, 46, 48, 49, 50, 53, 55]
def count566 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 13, 14, 16, 19, 20, 22, 23, 25, 27, 28, 32, 33, 35, 37, 38, 41, 42, 45, 46, 48, 49, 50, 53, 55]
def count595 (b : Nat → Bool) : Nat := countLit b [59, 63]
def count597 (b : Nat → Bool) : Nat := countLit b [56, 59, 63]
def count600 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count602 (b : Nat → Bool) : Nat := countLit b [67, 71]
def count604 (b : Nat → Bool) : Nat := countLit b [64, 65, 67, 71]
def count608 (b : Nat → Bool) : Nat := countLit b [56, 59, 63, 64, 65, 67, 71]
def count615 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count617 (b : Nat → Bool) : Nat := countLit b [73, 74, 75]
def count620 (b : Nat → Bool) : Nat := countLit b [79, 80]
def count622 (b : Nat → Bool) : Nat := countLit b [81, 83]
def count624 (b : Nat → Bool) : Nat := countLit b [79, 80, 81, 83]
def count628 (b : Nat → Bool) : Nat := countLit b [73, 74, 75, 79, 80, 81, 83]
def count635 (b : Nat → Bool) : Nat := countLit b [56, 59, 63, 64, 65, 67, 71, 73, 74, 75, 79, 80, 81, 83]
def count649 (b : Nat → Bool) : Nat := countLit b [88, 89]
def count651 (b : Nat → Bool) : Nat := countLit b [86, 88, 89]
def count654 (b : Nat → Bool) : Nat := countLit b [90, 95]
def count656 (b : Nat → Bool) : Nat := countLit b [96, 97]
def count658 (b : Nat → Bool) : Nat := countLit b [90, 95, 96, 97]
def count662 (b : Nat → Bool) : Nat := countLit b [86, 88, 89, 90, 95, 96, 97]
def count669 (b : Nat → Bool) : Nat := countLit b [99, 103]
def count671 (b : Nat → Bool) : Nat := countLit b [105, 106]
def count673 (b : Nat → Bool) : Nat := countLit b [99, 103, 105, 106]
def count677 (b : Nat → Bool) : Nat := countLit b [108, 109]
def count679 (b : Nat → Bool) : Nat := countLit b [112, 114]
def count681 (b : Nat → Bool) : Nat := countLit b [108, 109, 112, 114]
def count685 (b : Nat → Bool) : Nat := countLit b [99, 103, 105, 106, 108, 109, 112, 114]
def count693 (b : Nat → Bool) : Nat := countLit b [86, 88, 89, 90, 95, 96, 97, 99, 103, 105, 106, 108, 109, 112, 114]
def count708 (b : Nat → Bool) : Nat := countLit b [56, 59, 63, 64, 65, 67, 71, 73, 74, 75, 79, 80, 81, 83, 86, 88, 89, 90, 95, 96, 97, 99, 103, 105, 106, 108, 109, 112, 114]
def count737 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 13, 14, 16, 19, 20, 22, 23, 25, 27, 28, 32, 33, 35, 37, 38, 41, 42, 45, 46, 48, 49, 50, 53, 55, 56, 59, 63, 64, 65, 67, 71, 73, 74, 75, 79, 80, 81, 83, 86, 88, 89, 90, 95, 96, 97, 99, 103, 105, 106, 108, 109, 112, 114]
def count779 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count781 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6]
def count784 (b : Nat → Bool) : Nat := countLit b [-7, -9]
def count786 (b : Nat → Bool) : Nat := countLit b [-13, -14]
def count788 (b : Nat → Bool) : Nat := countLit b [-7, -9, -13, -14]
def count792 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -13, -14]
def count799 (b : Nat → Bool) : Nat := countLit b [-19, -20]
def count801 (b : Nat → Bool) : Nat := countLit b [-16, -19, -20]
def count804 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count806 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count808 (b : Nat → Bool) : Nat := countLit b [-22, -23, -25, -27]
def count812 (b : Nat → Bool) : Nat := countLit b [-16, -19, -20, -22, -23, -25, -27]
def count819 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -13, -14, -16, -19, -20, -22, -23, -25, -27]
def count833 (b : Nat → Bool) : Nat := countLit b [-32, -33]
def count835 (b : Nat → Bool) : Nat := countLit b [-28, -32, -33]
def count838 (b : Nat → Bool) : Nat := countLit b [-35, -37]
def count840 (b : Nat → Bool) : Nat := countLit b [-38, -41]
def count842 (b : Nat → Bool) : Nat := countLit b [-35, -37, -38, -41]
def count846 (b : Nat → Bool) : Nat := countLit b [-28, -32, -33, -35, -37, -38, -41]
def count853 (b : Nat → Bool) : Nat := countLit b [-42, -45]
def count855 (b : Nat → Bool) : Nat := countLit b [-46, -48]
def count857 (b : Nat → Bool) : Nat := countLit b [-42, -45, -46, -48]
def count861 (b : Nat → Bool) : Nat := countLit b [-49, -50]
def count863 (b : Nat → Bool) : Nat := countLit b [-53, -55]
def count865 (b : Nat → Bool) : Nat := countLit b [-49, -50, -53, -55]
def count869 (b : Nat → Bool) : Nat := countLit b [-42, -45, -46, -48, -49, -50, -53, -55]
def count877 (b : Nat → Bool) : Nat := countLit b [-28, -32, -33, -35, -37, -38, -41, -42, -45, -46, -48, -49, -50, -53, -55]
def count892 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -13, -14, -16, -19, -20, -22, -23, -25, -27, -28, -32, -33, -35, -37, -38, -41, -42, -45, -46, -48, -49, -50, -53, -55]
def count910 (b : Nat → Bool) : Nat := countLit b [-59, -63]
def count912 (b : Nat → Bool) : Nat := countLit b [-56, -59, -63]
def count915 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count917 (b : Nat → Bool) : Nat := countLit b [-67, -71]
def count919 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67, -71]
def count923 (b : Nat → Bool) : Nat := countLit b [-56, -59, -63, -64, -65, -67, -71]
def count930 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count932 (b : Nat → Bool) : Nat := countLit b [-73, -74, -75]
def count935 (b : Nat → Bool) : Nat := countLit b [-79, -80]
def count937 (b : Nat → Bool) : Nat := countLit b [-81, -83]
def count939 (b : Nat → Bool) : Nat := countLit b [-79, -80, -81, -83]
def count943 (b : Nat → Bool) : Nat := countLit b [-73, -74, -75, -79, -80, -81, -83]
def count950 (b : Nat → Bool) : Nat := countLit b [-56, -59, -63, -64, -65, -67, -71, -73, -74, -75, -79, -80, -81, -83]
def count964 (b : Nat → Bool) : Nat := countLit b [-88, -89]
def count966 (b : Nat → Bool) : Nat := countLit b [-86, -88, -89]
def count969 (b : Nat → Bool) : Nat := countLit b [-90, -95]
def count971 (b : Nat → Bool) : Nat := countLit b [-96, -97]
def count973 (b : Nat → Bool) : Nat := countLit b [-90, -95, -96, -97]
def count977 (b : Nat → Bool) : Nat := countLit b [-86, -88, -89, -90, -95, -96, -97]
def count984 (b : Nat → Bool) : Nat := countLit b [-99, -103]
def count986 (b : Nat → Bool) : Nat := countLit b [-105, -106]
def count988 (b : Nat → Bool) : Nat := countLit b [-99, -103, -105, -106]
def count992 (b : Nat → Bool) : Nat := countLit b [-108, -109]
def count994 (b : Nat → Bool) : Nat := countLit b [-112, -114]
def count996 (b : Nat → Bool) : Nat := countLit b [-108, -109, -112, -114]
def count1000 (b : Nat → Bool) : Nat := countLit b [-99, -103, -105, -106, -108, -109, -112, -114]
def count1008 (b : Nat → Bool) : Nat := countLit b [-86, -88, -89, -90, -95, -96, -97, -99, -103, -105, -106, -108, -109, -112, -114]
def count1023 (b : Nat → Bool) : Nat := countLit b [-56, -59, -63, -64, -65, -67, -71, -73, -74, -75, -79, -80, -81, -83, -86, -88, -89, -90, -95, -96, -97, -99, -103, -105, -106, -108, -109, -112, -114]
def count1041 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -13, -14, -16, -19, -20, -22, -23, -25, -27, -28, -32, -33, -35, -37, -38, -41, -42, -45, -46, -48, -49, -50, -53, -55, -56, -59, -63, -64, -65, -67, -71, -73, -74, -75, -79, -80, -81, -83, -86, -88, -89, -90, -95, -96, -97, -99, -103, -105, -106, -108, -109, -112, -114]
def count1059 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count1061 (b : Nat → Bool) : Nat := countLit b [2, 3, 5]
def count1064 (b : Nat → Bool) : Nat := countLit b [8, 10]
def count1066 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count1068 (b : Nat → Bool) : Nat := countLit b [8, 10, 11, 12]
def count1072 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 10, 11, 12]
def count1079 (b : Nat → Bool) : Nat := countLit b [17, 18]
def count1081 (b : Nat → Bool) : Nat := countLit b [15, 17, 18]
def count1084 (b : Nat → Bool) : Nat := countLit b [21, 24]
def count1086 (b : Nat → Bool) : Nat := countLit b [26, 29]
def count1088 (b : Nat → Bool) : Nat := countLit b [21, 24, 26, 29]
def count1092 (b : Nat → Bool) : Nat := countLit b [15, 17, 18, 21, 24, 26, 29]
def count1099 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 10, 11, 12, 15, 17, 18, 21, 24, 26, 29]
def count1113 (b : Nat → Bool) : Nat := countLit b [31, 34]
def count1115 (b : Nat → Bool) : Nat := countLit b [30, 31, 34]
def count1118 (b : Nat → Bool) : Nat := countLit b [36, 39]
def count1120 (b : Nat → Bool) : Nat := countLit b [40, 43]
def count1122 (b : Nat → Bool) : Nat := countLit b [36, 39, 40, 43]
def count1126 (b : Nat → Bool) : Nat := countLit b [30, 31, 34, 36, 39, 40, 43]
def count1133 (b : Nat → Bool) : Nat := countLit b [47, 51]
def count1135 (b : Nat → Bool) : Nat := countLit b [44, 47, 51]
def count1138 (b : Nat → Bool) : Nat := countLit b [52, 54]
def count1140 (b : Nat → Bool) : Nat := countLit b [57, 58]
def count1142 (b : Nat → Bool) : Nat := countLit b [52, 54, 57, 58]
def count1146 (b : Nat → Bool) : Nat := countLit b [44, 47, 51, 52, 54, 57, 58]
def count1153 (b : Nat → Bool) : Nat := countLit b [30, 31, 34, 36, 39, 40, 43, 44, 47, 51, 52, 54, 57, 58]
def count1167 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 10, 11, 12, 15, 17, 18, 21, 24, 26, 29, 30, 31, 34, 36, 39, 40, 43, 44, 47, 51, 52, 54, 57, 58]
def count1195 (b : Nat → Bool) : Nat := countLit b [61, 62]
def count1197 (b : Nat → Bool) : Nat := countLit b [60, 61, 62]
def count1200 (b : Nat → Bool) : Nat := countLit b [66, 68]
def count1202 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count1204 (b : Nat → Bool) : Nat := countLit b [66, 68, 69, 70]
def count1208 (b : Nat → Bool) : Nat := countLit b [60, 61, 62, 66, 68, 69, 70]
def count1215 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count1217 (b : Nat → Bool) : Nat := countLit b [72, 76, 77]
def count1220 (b : Nat → Bool) : Nat := countLit b [78, 82]
def count1222 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count1224 (b : Nat → Bool) : Nat := countLit b [78, 82, 84, 85]
def count1228 (b : Nat → Bool) : Nat := countLit b [72, 76, 77, 78, 82, 84, 85]
def count1235 (b : Nat → Bool) : Nat := countLit b [60, 61, 62, 66, 68, 69, 70, 72, 76, 77, 78, 82, 84, 85]
def count1249 (b : Nat → Bool) : Nat := countLit b [91, 92]
def count1251 (b : Nat → Bool) : Nat := countLit b [87, 91, 92]
def count1254 (b : Nat → Bool) : Nat := countLit b [93, 94]
def count1256 (b : Nat → Bool) : Nat := countLit b [98, 100]
def count1258 (b : Nat → Bool) : Nat := countLit b [93, 94, 98, 100]
def count1262 (b : Nat → Bool) : Nat := countLit b [87, 91, 92, 93, 94, 98, 100]
def count1269 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count1271 (b : Nat → Bool) : Nat := countLit b [101, 102, 104]
def count1274 (b : Nat → Bool) : Nat := countLit b [107, 110]
def count1276 (b : Nat → Bool) : Nat := countLit b [111, 113]
def count1278 (b : Nat → Bool) : Nat := countLit b [107, 110, 111, 113]
def count1282 (b : Nat → Bool) : Nat := countLit b [101, 102, 104, 107, 110, 111, 113]
def count1289 (b : Nat → Bool) : Nat := countLit b [87, 91, 92, 93, 94, 98, 100, 101, 102, 104, 107, 110, 111, 113]
def count1303 (b : Nat → Bool) : Nat := countLit b [60, 61, 62, 66, 68, 69, 70, 72, 76, 77, 78, 82, 84, 85, 87, 91, 92, 93, 94, 98, 100, 101, 102, 104, 107, 110, 111, 113]
def count1331 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 10, 11, 12, 15, 17, 18, 21, 24, 26, 29, 30, 31, 34, 36, 39, 40, 43, 44, 47, 51, 52, 54, 57, 58, 60, 61, 62, 66, 68, 69, 70, 72, 76, 77, 78, 82, 84, 85, 87, 91, 92, 93, 94, 98, 100, 101, 102, 104, 107, 110, 111, 113]
def count1373 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1375 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5]
def count1378 (b : Nat → Bool) : Nat := countLit b [-8, -10]
def count1380 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count1382 (b : Nat → Bool) : Nat := countLit b [-8, -10, -11, -12]
def count1386 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -10, -11, -12]
def count1393 (b : Nat → Bool) : Nat := countLit b [-17, -18]
def count1395 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18]
def count1398 (b : Nat → Bool) : Nat := countLit b [-21, -24]
def count1400 (b : Nat → Bool) : Nat := countLit b [-26, -29]
def count1402 (b : Nat → Bool) : Nat := countLit b [-21, -24, -26, -29]
def count1406 (b : Nat → Bool) : Nat := countLit b [-15, -17, -18, -21, -24, -26, -29]
def count1413 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29]
def count1427 (b : Nat → Bool) : Nat := countLit b [-31, -34]
def count1429 (b : Nat → Bool) : Nat := countLit b [-30, -31, -34]
def count1432 (b : Nat → Bool) : Nat := countLit b [-36, -39]
def count1434 (b : Nat → Bool) : Nat := countLit b [-40, -43]
def count1436 (b : Nat → Bool) : Nat := countLit b [-36, -39, -40, -43]
def count1440 (b : Nat → Bool) : Nat := countLit b [-30, -31, -34, -36, -39, -40, -43]
def count1447 (b : Nat → Bool) : Nat := countLit b [-47, -51]
def count1449 (b : Nat → Bool) : Nat := countLit b [-44, -47, -51]
def count1452 (b : Nat → Bool) : Nat := countLit b [-52, -54]
def count1454 (b : Nat → Bool) : Nat := countLit b [-57, -58]
def count1456 (b : Nat → Bool) : Nat := countLit b [-52, -54, -57, -58]
def count1460 (b : Nat → Bool) : Nat := countLit b [-44, -47, -51, -52, -54, -57, -58]
def count1467 (b : Nat → Bool) : Nat := countLit b [-30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]
def count1481 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]
def count1497 (b : Nat → Bool) : Nat := countLit b [-61, -62]
def count1499 (b : Nat → Bool) : Nat := countLit b [-60, -61, -62]
def count1502 (b : Nat → Bool) : Nat := countLit b [-66, -68]
def count1504 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count1506 (b : Nat → Bool) : Nat := countLit b [-66, -68, -69, -70]
def count1510 (b : Nat → Bool) : Nat := countLit b [-60, -61, -62, -66, -68, -69, -70]
def count1517 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count1519 (b : Nat → Bool) : Nat := countLit b [-72, -76, -77]
def count1522 (b : Nat → Bool) : Nat := countLit b [-78, -82]
def count1524 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count1526 (b : Nat → Bool) : Nat := countLit b [-78, -82, -84, -85]
def count1530 (b : Nat → Bool) : Nat := countLit b [-72, -76, -77, -78, -82, -84, -85]
def count1537 (b : Nat → Bool) : Nat := countLit b [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]
def count1551 (b : Nat → Bool) : Nat := countLit b [-91, -92]
def count1553 (b : Nat → Bool) : Nat := countLit b [-87, -91, -92]
def count1556 (b : Nat → Bool) : Nat := countLit b [-93, -94]
def count1558 (b : Nat → Bool) : Nat := countLit b [-98, -100]
def count1560 (b : Nat → Bool) : Nat := countLit b [-93, -94, -98, -100]
def count1564 (b : Nat → Bool) : Nat := countLit b [-87, -91, -92, -93, -94, -98, -100]
def count1571 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count1573 (b : Nat → Bool) : Nat := countLit b [-101, -102, -104]
def count1576 (b : Nat → Bool) : Nat := countLit b [-107, -110]
def count1578 (b : Nat → Bool) : Nat := countLit b [-111, -113]
def count1580 (b : Nat → Bool) : Nat := countLit b [-107, -110, -111, -113]
def count1584 (b : Nat → Bool) : Nat := countLit b [-101, -102, -104, -107, -110, -111, -113]
def count1591 (b : Nat → Bool) : Nat := countLit b [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]
def count1605 (b : Nat → Bool) : Nat := countLit b [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]
def count1621 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58, -60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 818 then (if i < 409 then (if i < 204 then (if i < 102 then (if i < 51 then (if i < 25 then (if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 10 then b 9 else (if i < 11 then b 10 else b 11)))) else (if i < 18 then (if i < 15 then (if i < 13 then b 12 else (if i < 14 then b 13 else b 14)) else (if i < 16 then b 15 else (if i < 17 then b 16 else b 17))) else (if i < 21 then (if i < 19 then b 18 else (if i < 20 then b 19 else b 20)) else (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else b 24))))) else (if i < 38 then (if i < 31 then (if i < 28 then (if i < 26 then b 25 else (if i < 27 then b 26 else b 27)) else (if i < 29 then b 28 else (if i < 30 then b 29 else b 30))) else (if i < 34 then (if i < 32 then b 31 else (if i < 33 then b 32 else b 33)) else (if i < 36 then (if i < 35 then b 34 else b 35) else (if i < 37 then b 36 else b 37)))) else (if i < 44 then (if i < 41 then (if i < 39 then b 38 else (if i < 40 then b 39 else b 40)) else (if i < 42 then b 41 else (if i < 43 then b 42 else b 43))) else (if i < 47 then (if i < 45 then b 44 else (if i < 46 then b 45 else b 46)) else (if i < 49 then (if i < 48 then b 47 else b 48) else (if i < 50 then b 49 else b 50)))))) else (if i < 76 then (if i < 63 then (if i < 57 then (if i < 54 then (if i < 52 then b 51 else (if i < 53 then b 52 else b 53)) else (if i < 55 then b 54 else (if i < 56 then b 55 else b 56))) else (if i < 60 then (if i < 58 then b 57 else (if i < 59 then b 58 else b 59)) else (if i < 61 then b 60 else (if i < 62 then b 61 else b 62)))) else (if i < 69 then (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 67 then b 66 else (if i < 68 then b 67 else b 68))) else (if i < 72 then (if i < 70 then b 69 else (if i < 71 then b 70 else b 71)) else (if i < 74 then (if i < 73 then b 72 else b 73) else (if i < 75 then b 74 else b 75))))) else (if i < 89 then (if i < 82 then (if i < 79 then (if i < 77 then b 76 else (if i < 78 then b 77 else b 78)) else (if i < 80 then b 79 else (if i < 81 then b 80 else b 81))) else (if i < 85 then (if i < 83 then b 82 else (if i < 84 then b 83 else b 84)) else (if i < 87 then (if i < 86 then b 85 else b 86) else (if i < 88 then b 87 else b 88)))) else (if i < 95 then (if i < 92 then (if i < 90 then b 89 else (if i < 91 then b 90 else b 91)) else (if i < 93 then b 92 else (if i < 94 then b 93 else b 94))) else (if i < 98 then (if i < 96 then b 95 else (if i < 97 then b 96 else b 97)) else (if i < 100 then (if i < 99 then b 98 else b 99) else (if i < 101 then b 100 else b 101))))))) else (if i < 153 then (if i < 127 then (if i < 114 then (if i < 108 then (if i < 105 then (if i < 103 then b 102 else (if i < 104 then b 103 else b 104)) else (if i < 106 then b 105 else (if i < 107 then b 106 else b 107))) else (if i < 111 then (if i < 109 then b 108 else (if i < 110 then b 109 else b 110)) else (if i < 112 then b 111 else (if i < 113 then b 112 else b 113)))) else (if i < 120 then (if i < 117 then (if i < 115 then b 114 else (if i < 116 then b 115 else b 116)) else (if i < 118 then b 117 else (if i < 119 then b 118 else b 119))) else (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 125 then (if i < 124 then b 123 else b 124) else (if i < 126 then b 125 else b 126))))) else (if i < 140 then (if i < 133 then (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 131 then b 130 else (if i < 132 then b 131 else b 132))) else (if i < 136 then (if i < 134 then b 133 else (if i < 135 then b 134 else b 135)) else (if i < 138 then (if i < 137 then b 136 else b 137) else (if i < 139 then b 138 else b 139)))) else (if i < 146 then (if i < 143 then (if i < 141 then b 140 else (if i < 142 then b 141 else b 142)) else (if i < 144 then b 143 else (if i < 145 then b 144 else b 145))) else (if i < 149 then (if i < 147 then b 146 else (if i < 148 then b 147 else b 148)) else (if i < 151 then (if i < 150 then b 149 else b 150) else (if i < 152 then b 151 else b 152)))))) else (if i < 178 then (if i < 165 then (if i < 159 then (if i < 156 then (if i < 154 then b 153 else (if i < 155 then b 154 else b 155)) else (if i < 157 then b 156 else (if i < 158 then b 157 else b 158))) else (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 163 then b 162 else (if i < 164 then b 163 else b 164)))) else (if i < 171 then (if i < 168 then (if i < 166 then b 165 else (if i < 167 then b 166 else b 167)) else (if i < 169 then b 168 else (if i < 170 then b 169 else b 170))) else (if i < 174 then (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)) else (if i < 176 then (if i < 175 then b 174 else b 175) else (if i < 177 then b 176 else b 177))))) else (if i < 191 then (if i < 184 then (if i < 181 then (if i < 179 then b 178 else (if i < 180 then b 179 else b 180)) else (if i < 182 then b 181 else (if i < 183 then b 182 else b 183))) else (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 189 then (if i < 188 then b 187 else b 188) else (if i < 190 then b 189 else b 190)))) else (if i < 197 then (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 195 then b 194 else (if i < 196 then b 195 else b 196))) else (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 202 then (if i < 201 then b 200 else b 201) else (if i < 203 then b 202 else b 203)))))))) else (if i < 306 then (if i < 255 then (if i < 229 then (if i < 216 then (if i < 210 then (if i < 207 then (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)) else (if i < 208 then b 207 else (if i < 209 then b 208 else b 209))) else (if i < 213 then (if i < 211 then b 210 else (if i < 212 then b 211 else b 212)) else (if i < 214 then b 213 else (if i < 215 then b 214 else b 215)))) else (if i < 222 then (if i < 219 then (if i < 217 then b 216 else (if i < 218 then b 217 else b 218)) else (if i < 220 then b 219 else (if i < 221 then b 220 else b 221))) else (if i < 225 then (if i < 223 then b 222 else (if i < 224 then b 223 else b 224)) else (if i < 227 then (if i < 226 then b 225 else b 226) else (if i < 228 then b 227 else b 228))))) else (if i < 242 then (if i < 235 then (if i < 232 then (if i < 230 then decide (1 ≤ count229 b) else (if i < 231 then decide (2 ≤ count229 b) else decide (1 ≤ count231 b))) else (if i < 233 then decide (2 ≤ count231 b) else (if i < 234 then decide (1 ≤ count233 b) else decide (2 ≤ count233 b)))) else (if i < 238 then (if i < 236 then decide (1 ≤ count235 b) else (if i < 237 then decide (2 ≤ count235 b) else decide (1 ≤ count237 b))) else (if i < 240 then (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b)) else (if i < 241 then decide (2 ≤ count239 b) else decide (1 ≤ count241 b))))) else (if i < 248 then (if i < 245 then (if i < 243 then decide (2 ≤ count241 b) else (if i < 244 then decide (1 ≤ count243 b) else decide (2 ≤ count243 b))) else (if i < 246 then decide (1 ≤ count245 b) else (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b)))) else (if i < 251 then (if i < 249 then decide (2 ≤ count247 b) else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 253 then (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b))))))) else (if i < 280 then (if i < 267 then (if i < 261 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 259 then decide (2 ≤ count257 b) else (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)))) else (if i < 264 then (if i < 262 then decide (1 ≤ count261 b) else (if i < 263 then decide (2 ≤ count261 b) else decide (1 ≤ count263 b))) else (if i < 265 then decide (2 ≤ count263 b) else (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b))))) else (if i < 273 then (if i < 270 then (if i < 268 then decide (1 ≤ count267 b) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b))) else (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b)))) else (if i < 276 then (if i < 274 then decide (1 ≤ count273 b) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))) else (if i < 278 then (if i < 277 then decide (2 ≤ count275 b) else decide (1 ≤ count277 b)) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b)))))) else (if i < 293 then (if i < 286 then (if i < 283 then (if i < 281 then decide (2 ≤ count279 b) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))) else (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b)))) else (if i < 289 then (if i < 287 then decide (2 ≤ count285 b) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b))) else (if i < 291 then (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b)) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))))) else (if i < 299 then (if i < 296 then (if i < 294 then decide (1 ≤ count293 b) else (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b))) else (if i < 297 then decide (2 ≤ count295 b) else (if i < 298 then decide (1 ≤ count297 b) else decide (2 ≤ count297 b)))) else (if i < 302 then (if i < 300 then decide (1 ≤ count299 b) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))) else (if i < 304 then (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)) else (if i < 305 then decide (2 ≤ count303 b) else decide (1 ≤ count305 b)))))))) else (if i < 357 then (if i < 331 then (if i < 318 then (if i < 312 then (if i < 309 then (if i < 307 then decide (2 ≤ count305 b) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b))) else (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))) else (if i < 315 then (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))) else (if i < 316 then decide (1 ≤ count315 b) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b))))) else (if i < 324 then (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 322 then decide (1 ≤ count321 b) else (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)))) else (if i < 327 then (if i < 325 then decide (2 ≤ count323 b) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b))) else (if i < 329 then (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)))))) else (if i < 344 then (if i < 337 then (if i < 334 then (if i < 332 then decide (1 ≤ count331 b) else (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b))) else (if i < 335 then decide (2 ≤ count333 b) else (if i < 336 then decide (1 ≤ count335 b) else decide (2 ≤ count335 b)))) else (if i < 340 then (if i < 338 then decide (1 ≤ count337 b) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b))) else (if i < 342 then (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)) else (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b))))) else (if i < 350 then (if i < 347 then (if i < 345 then decide (2 ≤ count343 b) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b))) else (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))) else (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 355 then (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))))))) else (if i < 383 then (if i < 370 then (if i < 363 then (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 361 then decide (2 ≤ count359 b) else (if i < 362 then decide (1 ≤ count361 b) else decide (2 ≤ count361 b)))) else (if i < 366 then (if i < 364 then decide (1 ≤ count363 b) else (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b))) else (if i < 368 then (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)) else (if i < 369 then decide (2 ≤ count367 b) else decide (1 ≤ count369 b))))) else (if i < 376 then (if i < 373 then (if i < 371 then decide (2 ≤ count369 b) else (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b))) else (if i < 374 then decide (1 ≤ count373 b) else (if i < 375 then decide (2 ≤ count373 b) else decide (1 ≤ count375 b)))) else (if i < 379 then (if i < 377 then decide (2 ≤ count375 b) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b))) else (if i < 381 then (if i < 380 then decide (1 ≤ count379 b) else decide (2 ≤ count379 b)) else (if i < 382 then decide (1 ≤ count381 b) else decide (2 ≤ count381 b)))))) else (if i < 396 then (if i < 389 then (if i < 386 then (if i < 384 then decide (1 ≤ count383 b) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b))) else (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 394 then (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b)) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))))) else (if i < 402 then (if i < 399 then (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b))) else (if i < 400 then decide (1 ≤ count399 b) else (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)))) else (if i < 405 then (if i < 403 then decide (2 ≤ count401 b) else (if i < 404 then decide (1 ≤ count403 b) else decide (2 ≤ count403 b))) else (if i < 407 then (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b)) else (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)))))))))) else (if i < 613 then (if i < 511 then (if i < 460 then (if i < 434 then (if i < 421 then (if i < 415 then (if i < 412 then (if i < 410 then decide (1 ≤ count409 b) else (if i < 411 then decide (2 ≤ count409 b) else decide (1 ≤ count411 b))) else (if i < 413 then decide (2 ≤ count411 b) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))))) else (if i < 427 then (if i < 424 then (if i < 422 then decide (1 ≤ count421 b) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b))) else (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)))) else (if i < 430 then (if i < 428 then decide (1 ≤ count427 b) else (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b))) else (if i < 432 then (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b)))))) else (if i < 447 then (if i < 440 then (if i < 437 then (if i < 435 then decide (2 ≤ count433 b) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b))) else (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b)))) else (if i < 443 then (if i < 441 then decide (2 ≤ count439 b) else (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b))) else (if i < 445 then (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b)) else (if i < 446 then decide (1 ≤ count445 b) else decide (2 ≤ count445 b))))) else (if i < 453 then (if i < 450 then (if i < 448 then decide (1 ≤ count447 b) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b))) else (if i < 451 then decide (2 ≤ count449 b) else (if i < 452 then decide (1 ≤ count451 b) else decide (2 ≤ count451 b)))) else (if i < 456 then (if i < 454 then decide (1 ≤ count453 b) else (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b))) else (if i < 458 then (if i < 457 then decide (2 ≤ count455 b) else decide (3 ≤ count455 b)) else (if i < 459 then decide (1 ≤ count458 b) else decide (2 ≤ count458 b))))))) else (if i < 485 then (if i < 472 then (if i < 466 then (if i < 463 then (if i < 461 then decide (1 ≤ count460 b) else (if i < 462 then decide (2 ≤ count460 b) else decide (1 ≤ count462 b))) else (if i < 464 then decide (2 ≤ count462 b) else (if i < 465 then decide (3 ≤ count462 b) else decide (4 ≤ count462 b)))) else (if i < 469 then (if i < 467 then decide (1 ≤ count466 b) else (if i < 468 then decide (2 ≤ count466 b) else decide (3 ≤ count466 b))) else (if i < 470 then decide (4 ≤ count466 b) else (if i < 471 then decide (5 ≤ count466 b) else decide (6 ≤ count466 b))))) else (if i < 478 then (if i < 475 then (if i < 473 then decide (7 ≤ count466 b) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b))) else (if i < 476 then decide (1 ≤ count475 b) else (if i < 477 then decide (2 ≤ count475 b) else decide (3 ≤ count475 b)))) else (if i < 481 then (if i < 479 then decide (1 ≤ count478 b) else (if i < 480 then decide (2 ≤ count478 b) else decide (1 ≤ count480 b))) else (if i < 483 then (if i < 482 then decide (2 ≤ count480 b) else decide (1 ≤ count482 b)) else (if i < 484 then decide (2 ≤ count482 b) else decide (3 ≤ count482 b)))))) else (if i < 498 then (if i < 491 then (if i < 488 then (if i < 486 then decide (4 ≤ count482 b) else (if i < 487 then decide (1 ≤ count486 b) else decide (2 ≤ count486 b))) else (if i < 489 then decide (3 ≤ count486 b) else (if i < 490 then decide (4 ≤ count486 b) else decide (5 ≤ count486 b)))) else (if i < 494 then (if i < 492 then decide (6 ≤ count486 b) else (if i < 493 then decide (7 ≤ count486 b) else decide (1 ≤ count493 b))) else (if i < 496 then (if i < 495 then decide (2 ≤ count493 b) else decide (3 ≤ count493 b)) else (if i < 497 then decide (4 ≤ count493 b) else decide (5 ≤ count493 b))))) else (if i < 504 then (if i < 501 then (if i < 499 then decide (6 ≤ count493 b) else (if i < 500 then decide (7 ≤ count493 b) else decide (8 ≤ count493 b))) else (if i < 502 then decide (9 ≤ count493 b) else (if i < 503 then decide (10 ≤ count493 b) else decide (11 ≤ count493 b)))) else (if i < 507 then (if i < 505 then decide (12 ≤ count493 b) else (if i < 506 then decide (13 ≤ count493 b) else decide (14 ≤ count493 b))) else (if i < 509 then (if i < 508 then decide (1 ≤ count507 b) else decide (2 ≤ count507 b)) else (if i < 510 then decide (1 ≤ count509 b) else decide (2 ≤ count509 b)))))))) else (if i < 562 then (if i < 536 then (if i < 523 then (if i < 517 then (if i < 514 then (if i < 512 then decide (3 ≤ count509 b) else (if i < 513 then decide (1 ≤ count512 b) else decide (2 ≤ count512 b))) else (if i < 515 then decide (1 ≤ count514 b) else (if i < 516 then decide (2 ≤ count514 b) else decide (1 ≤ count516 b)))) else (if i < 520 then (if i < 518 then decide (2 ≤ count516 b) else (if i < 519 then decide (3 ≤ count516 b) else decide (4 ≤ count516 b))) else (if i < 521 then decide (1 ≤ count520 b) else (if i < 522 then decide (2 ≤ count520 b) else decide (3 ≤ count520 b))))) else (if i < 529 then (if i < 526 then (if i < 524 then decide (4 ≤ count520 b) else (if i < 525 then decide (5 ≤ count520 b) else decide (6 ≤ count520 b))) else (if i < 527 then decide (7 ≤ count520 b) else (if i < 528 then decide (1 ≤ count527 b) else decide (2 ≤ count527 b)))) else (if i < 532 then (if i < 530 then decide (1 ≤ count529 b) else (if i < 531 then decide (2 ≤ count529 b) else decide (1 ≤ count531 b))) else (if i < 534 then (if i < 533 then decide (2 ≤ count531 b) else decide (3 ≤ count531 b)) else (if i < 535 then decide (4 ≤ count531 b) else decide (1 ≤ count535 b)))))) else (if i < 549 then (if i < 542 then (if i < 539 then (if i < 537 then decide (2 ≤ count535 b) else (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b))) else (if i < 540 then decide (1 ≤ count539 b) else (if i < 541 then decide (2 ≤ count539 b) else decide (3 ≤ count539 b)))) else (if i < 545 then (if i < 543 then decide (4 ≤ count539 b) else (if i < 544 then decide (1 ≤ count543 b) else decide (2 ≤ count543 b))) else (if i < 547 then (if i < 546 then decide (3 ≤ count543 b) else decide (4 ≤ count543 b)) else (if i < 548 then decide (5 ≤ count543 b) else decide (6 ≤ count543 b))))) else (if i < 555 then (if i < 552 then (if i < 550 then decide (7 ≤ count543 b) else (if i < 551 then decide (8 ≤ count543 b) else decide (1 ≤ count551 b))) else (if i < 553 then decide (2 ≤ count551 b) else (if i < 554 then decide (3 ≤ count551 b) else decide (4 ≤ count551 b)))) else (if i < 558 then (if i < 556 then decide (5 ≤ count551 b) else (if i < 557 then decide (6 ≤ count551 b) else decide (7 ≤ count551 b))) else (if i < 560 then (if i < 559 then decide (8 ≤ count551 b) else decide (9 ≤ count551 b)) else (if i < 561 then decide (10 ≤ count551 b) else decide (11 ≤ count551 b))))))) else (if i < 587 then (if i < 574 then (if i < 568 then (if i < 565 then (if i < 563 then decide (12 ≤ count551 b) else (if i < 564 then decide (13 ≤ count551 b) else decide (14 ≤ count551 b))) else (if i < 566 then decide (15 ≤ count551 b) else (if i < 567 then decide (1 ≤ count566 b) else decide (2 ≤ count566 b)))) else (if i < 571 then (if i < 569 then decide (3 ≤ count566 b) else (if i < 570 then decide (4 ≤ count566 b) else decide (5 ≤ count566 b))) else (if i < 572 then decide (6 ≤ count566 b) else (if i < 573 then decide (7 ≤ count566 b) else decide (8 ≤ count566 b))))) else (if i < 580 then (if i < 577 then (if i < 575 then decide (9 ≤ count566 b) else (if i < 576 then decide (10 ≤ count566 b) else decide (11 ≤ count566 b))) else (if i < 578 then decide (12 ≤ count566 b) else (if i < 579 then decide (13 ≤ count566 b) else decide (14 ≤ count566 b)))) else (if i < 583 then (if i < 581 then decide (15 ≤ count566 b) else (if i < 582 then decide (16 ≤ count566 b) else decide (17 ≤ count566 b))) else (if i < 585 then (if i < 584 then decide (18 ≤ count566 b) else decide (19 ≤ count566 b)) else (if i < 586 then decide (20 ≤ count566 b) else decide (21 ≤ count566 b)))))) else (if i < 600 then (if i < 593 then (if i < 590 then (if i < 588 then decide (22 ≤ count566 b) else (if i < 589 then decide (23 ≤ count566 b) else decide (24 ≤ count566 b))) else (if i < 591 then decide (25 ≤ count566 b) else (if i < 592 then decide (26 ≤ count566 b) else decide (27 ≤ count566 b)))) else (if i < 596 then (if i < 594 then decide (28 ≤ count566 b) else (if i < 595 then decide (29 ≤ count566 b) else decide (1 ≤ count595 b))) else (if i < 598 then (if i < 597 then decide (2 ≤ count595 b) else decide (1 ≤ count597 b)) else (if i < 599 then decide (2 ≤ count597 b) else decide (3 ≤ count597 b))))) else (if i < 606 then (if i < 603 then (if i < 601 then decide (1 ≤ count600 b) else (if i < 602 then decide (2 ≤ count600 b) else decide (1 ≤ count602 b))) else (if i < 604 then decide (2 ≤ count602 b) else (if i < 605 then decide (1 ≤ count604 b) else decide (2 ≤ count604 b)))) else (if i < 609 then (if i < 607 then decide (3 ≤ count604 b) else (if i < 608 then decide (4 ≤ count604 b) else decide (1 ≤ count608 b))) else (if i < 611 then (if i < 610 then decide (2 ≤ count608 b) else decide (3 ≤ count608 b)) else (if i < 612 then decide (4 ≤ count608 b) else decide (5 ≤ count608 b))))))))) else (if i < 715 then (if i < 664 then (if i < 638 then (if i < 625 then (if i < 619 then (if i < 616 then (if i < 614 then decide (6 ≤ count608 b) else (if i < 615 then decide (7 ≤ count608 b) else decide (1 ≤ count615 b))) else (if i < 617 then decide (2 ≤ count615 b) else (if i < 618 then decide (1 ≤ count617 b) else decide (2 ≤ count617 b)))) else (if i < 622 then (if i < 620 then decide (3 ≤ count617 b) else (if i < 621 then decide (1 ≤ count620 b) else decide (2 ≤ count620 b))) else (if i < 623 then decide (1 ≤ count622 b) else (if i < 624 then decide (2 ≤ count622 b) else decide (1 ≤ count624 b))))) else (if i < 631 then (if i < 628 then (if i < 626 then decide (2 ≤ count624 b) else (if i < 627 then decide (3 ≤ count624 b) else decide (4 ≤ count624 b))) else (if i < 629 then decide (1 ≤ count628 b) else (if i < 630 then decide (2 ≤ count628 b) else decide (3 ≤ count628 b)))) else (if i < 634 then (if i < 632 then decide (4 ≤ count628 b) else (if i < 633 then decide (5 ≤ count628 b) else decide (6 ≤ count628 b))) else (if i < 636 then (if i < 635 then decide (7 ≤ count628 b) else decide (1 ≤ count635 b)) else (if i < 637 then decide (2 ≤ count635 b) else decide (3 ≤ count635 b)))))) else (if i < 651 then (if i < 644 then (if i < 641 then (if i < 639 then decide (4 ≤ count635 b) else (if i < 640 then decide (5 ≤ count635 b) else decide (6 ≤ count635 b))) else (if i < 642 then decide (7 ≤ count635 b) else (if i < 643 then decide (8 ≤ count635 b) else decide (9 ≤ count635 b)))) else (if i < 647 then (if i < 645 then decide (10 ≤ count635 b) else (if i < 646 then decide (11 ≤ count635 b) else decide (12 ≤ count635 b))) else (if i < 649 then (if i < 648 then decide (13 ≤ count635 b) else decide (14 ≤ count635 b)) else (if i < 650 then decide (1 ≤ count649 b) else decide (2 ≤ count649 b))))) else (if i < 657 then (if i < 654 then (if i < 652 then decide (1 ≤ count651 b) else (if i < 653 then decide (2 ≤ count651 b) else decide (3 ≤ count651 b))) else (if i < 655 then decide (1 ≤ count654 b) else (if i < 656 then decide (2 ≤ count654 b) else decide (1 ≤ count656 b)))) else (if i < 660 then (if i < 658 then decide (2 ≤ count656 b) else (if i < 659 then decide (1 ≤ count658 b) else decide (2 ≤ count658 b))) else (if i < 662 then (if i < 661 then decide (3 ≤ count658 b) else decide (4 ≤ count658 b)) else (if i < 663 then decide (1 ≤ count662 b) else decide (2 ≤ count662 b))))))) else (if i < 689 then (if i < 676 then (if i < 670 then (if i < 667 then (if i < 665 then decide (3 ≤ count662 b) else (if i < 666 then decide (4 ≤ count662 b) else decide (5 ≤ count662 b))) else (if i < 668 then decide (6 ≤ count662 b) else (if i < 669 then decide (7 ≤ count662 b) else decide (1 ≤ count669 b)))) else (if i < 673 then (if i < 671 then decide (2 ≤ count669 b) else (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b))) else (if i < 674 then decide (1 ≤ count673 b) else (if i < 675 then decide (2 ≤ count673 b) else decide (3 ≤ count673 b))))) else (if i < 682 then (if i < 679 then (if i < 677 then decide (4 ≤ count673 b) else (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b))) else (if i < 680 then decide (1 ≤ count679 b) else (if i < 681 then decide (2 ≤ count679 b) else decide (1 ≤ count681 b)))) else (if i < 685 then (if i < 683 then decide (2 ≤ count681 b) else (if i < 684 then decide (3 ≤ count681 b) else decide (4 ≤ count681 b))) else (if i < 687 then (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b)) else (if i < 688 then decide (3 ≤ count685 b) else decide (4 ≤ count685 b)))))) else (if i < 702 then (if i < 695 then (if i < 692 then (if i < 690 then decide (5 ≤ count685 b) else (if i < 691 then decide (6 ≤ count685 b) else decide (7 ≤ count685 b))) else (if i < 693 then decide (8 ≤ count685 b) else (if i < 694 then decide (1 ≤ count693 b) else decide (2 ≤ count693 b)))) else (if i < 698 then (if i < 696 then decide (3 ≤ count693 b) else (if i < 697 then decide (4 ≤ count693 b) else decide (5 ≤ count693 b))) else (if i < 700 then (if i < 699 then decide (6 ≤ count693 b) else decide (7 ≤ count693 b)) else (if i < 701 then decide (8 ≤ count693 b) else decide (9 ≤ count693 b))))) else (if i < 708 then (if i < 705 then (if i < 703 then decide (10 ≤ count693 b) else (if i < 704 then decide (11 ≤ count693 b) else decide (12 ≤ count693 b))) else (if i < 706 then decide (13 ≤ count693 b) else (if i < 707 then decide (14 ≤ count693 b) else decide (15 ≤ count693 b)))) else (if i < 711 then (if i < 709 then decide (1 ≤ count708 b) else (if i < 710 then decide (2 ≤ count708 b) else decide (3 ≤ count708 b))) else (if i < 713 then (if i < 712 then decide (4 ≤ count708 b) else decide (5 ≤ count708 b)) else (if i < 714 then decide (6 ≤ count708 b) else decide (7 ≤ count708 b)))))))) else (if i < 766 then (if i < 740 then (if i < 727 then (if i < 721 then (if i < 718 then (if i < 716 then decide (8 ≤ count708 b) else (if i < 717 then decide (9 ≤ count708 b) else decide (10 ≤ count708 b))) else (if i < 719 then decide (11 ≤ count708 b) else (if i < 720 then decide (12 ≤ count708 b) else decide (13 ≤ count708 b)))) else (if i < 724 then (if i < 722 then decide (14 ≤ count708 b) else (if i < 723 then decide (15 ≤ count708 b) else decide (16 ≤ count708 b))) else (if i < 725 then decide (17 ≤ count708 b) else (if i < 726 then decide (18 ≤ count708 b) else decide (19 ≤ count708 b))))) else (if i < 733 then (if i < 730 then (if i < 728 then decide (20 ≤ count708 b) else (if i < 729 then decide (21 ≤ count708 b) else decide (22 ≤ count708 b))) else (if i < 731 then decide (23 ≤ count708 b) else (if i < 732 then decide (24 ≤ count708 b) else decide (25 ≤ count708 b)))) else (if i < 736 then (if i < 734 then decide (26 ≤ count708 b) else (if i < 735 then decide (27 ≤ count708 b) else decide (28 ≤ count708 b))) else (if i < 738 then (if i < 737 then decide (29 ≤ count708 b) else decide (1 ≤ count737 b)) else (if i < 739 then decide (2 ≤ count737 b) else decide (3 ≤ count737 b)))))) else (if i < 753 then (if i < 746 then (if i < 743 then (if i < 741 then decide (4 ≤ count737 b) else (if i < 742 then decide (5 ≤ count737 b) else decide (6 ≤ count737 b))) else (if i < 744 then decide (7 ≤ count737 b) else (if i < 745 then decide (8 ≤ count737 b) else decide (9 ≤ count737 b)))) else (if i < 749 then (if i < 747 then decide (10 ≤ count737 b) else (if i < 748 then decide (11 ≤ count737 b) else decide (12 ≤ count737 b))) else (if i < 751 then (if i < 750 then decide (13 ≤ count737 b) else decide (14 ≤ count737 b)) else (if i < 752 then decide (15 ≤ count737 b) else decide (16 ≤ count737 b))))) else (if i < 759 then (if i < 756 then (if i < 754 then decide (17 ≤ count737 b) else (if i < 755 then decide (18 ≤ count737 b) else decide (19 ≤ count737 b))) else (if i < 757 then decide (20 ≤ count737 b) else (if i < 758 then decide (21 ≤ count737 b) else decide (22 ≤ count737 b)))) else (if i < 762 then (if i < 760 then decide (23 ≤ count737 b) else (if i < 761 then decide (24 ≤ count737 b) else decide (25 ≤ count737 b))) else (if i < 764 then (if i < 763 then decide (26 ≤ count737 b) else decide (27 ≤ count737 b)) else (if i < 765 then decide (28 ≤ count737 b) else decide (29 ≤ count737 b))))))) else (if i < 792 then (if i < 779 then (if i < 772 then (if i < 769 then (if i < 767 then decide (30 ≤ count737 b) else (if i < 768 then decide (31 ≤ count737 b) else decide (32 ≤ count737 b))) else (if i < 770 then decide (33 ≤ count737 b) else (if i < 771 then decide (34 ≤ count737 b) else decide (35 ≤ count737 b)))) else (if i < 775 then (if i < 773 then decide (36 ≤ count737 b) else (if i < 774 then decide (37 ≤ count737 b) else decide (38 ≤ count737 b))) else (if i < 777 then (if i < 776 then decide (39 ≤ count737 b) else decide (40 ≤ count737 b)) else (if i < 778 then decide (41 ≤ count737 b) else decide (42 ≤ count737 b))))) else (if i < 785 then (if i < 782 then (if i < 780 then decide (1 ≤ count779 b) else (if i < 781 then decide (2 ≤ count779 b) else decide (1 ≤ count781 b))) else (if i < 783 then decide (2 ≤ count781 b) else (if i < 784 then decide (3 ≤ count781 b) else decide (1 ≤ count784 b)))) else (if i < 788 then (if i < 786 then decide (2 ≤ count784 b) else (if i < 787 then decide (1 ≤ count786 b) else decide (2 ≤ count786 b))) else (if i < 790 then (if i < 789 then decide (1 ≤ count788 b) else decide (2 ≤ count788 b)) else (if i < 791 then decide (3 ≤ count788 b) else decide (4 ≤ count788 b)))))) else (if i < 805 then (if i < 798 then (if i < 795 then (if i < 793 then decide (1 ≤ count792 b) else (if i < 794 then decide (2 ≤ count792 b) else decide (3 ≤ count792 b))) else (if i < 796 then decide (4 ≤ count792 b) else (if i < 797 then decide (5 ≤ count792 b) else decide (6 ≤ count792 b)))) else (if i < 801 then (if i < 799 then decide (7 ≤ count792 b) else (if i < 800 then decide (1 ≤ count799 b) else decide (2 ≤ count799 b))) else (if i < 803 then (if i < 802 then decide (1 ≤ count801 b) else decide (2 ≤ count801 b)) else (if i < 804 then decide (3 ≤ count801 b) else decide (1 ≤ count804 b))))) else (if i < 811 then (if i < 808 then (if i < 806 then decide (2 ≤ count804 b) else (if i < 807 then decide (1 ≤ count806 b) else decide (2 ≤ count806 b))) else (if i < 809 then decide (1 ≤ count808 b) else (if i < 810 then decide (2 ≤ count808 b) else decide (3 ≤ count808 b)))) else (if i < 814 then (if i < 812 then decide (4 ≤ count808 b) else (if i < 813 then decide (1 ≤ count812 b) else decide (2 ≤ count812 b))) else (if i < 816 then (if i < 815 then decide (3 ≤ count812 b) else decide (4 ≤ count812 b)) else (if i < 817 then decide (5 ≤ count812 b) else decide (6 ≤ count812 b))))))))))) else (if i < 1227 then (if i < 1022 then (if i < 920 then (if i < 869 then (if i < 843 then (if i < 830 then (if i < 824 then (if i < 821 then (if i < 819 then decide (7 ≤ count812 b) else (if i < 820 then decide (1 ≤ count819 b) else decide (2 ≤ count819 b))) else (if i < 822 then decide (3 ≤ count819 b) else (if i < 823 then decide (4 ≤ count819 b) else decide (5 ≤ count819 b)))) else (if i < 827 then (if i < 825 then decide (6 ≤ count819 b) else (if i < 826 then decide (7 ≤ count819 b) else decide (8 ≤ count819 b))) else (if i < 828 then decide (9 ≤ count819 b) else (if i < 829 then decide (10 ≤ count819 b) else decide (11 ≤ count819 b))))) else (if i < 836 then (if i < 833 then (if i < 831 then decide (12 ≤ count819 b) else (if i < 832 then decide (13 ≤ count819 b) else decide (14 ≤ count819 b))) else (if i < 834 then decide (1 ≤ count833 b) else (if i < 835 then decide (2 ≤ count833 b) else decide (1 ≤ count835 b)))) else (if i < 839 then (if i < 837 then decide (2 ≤ count835 b) else (if i < 838 then decide (3 ≤ count835 b) else decide (1 ≤ count838 b))) else (if i < 841 then (if i < 840 then decide (2 ≤ count838 b) else decide (1 ≤ count840 b)) else (if i < 842 then decide (2 ≤ count840 b) else decide (1 ≤ count842 b)))))) else (if i < 856 then (if i < 849 then (if i < 846 then (if i < 844 then decide (2 ≤ count842 b) else (if i < 845 then decide (3 ≤ count842 b) else decide (4 ≤ count842 b))) else (if i < 847 then decide (1 ≤ count846 b) else (if i < 848 then decide (2 ≤ count846 b) else decide (3 ≤ count846 b)))) else (if i < 852 then (if i < 850 then decide (4 ≤ count846 b) else (if i < 851 then decide (5 ≤ count846 b) else decide (6 ≤ count846 b))) else (if i < 854 then (if i < 853 then decide (7 ≤ count846 b) else decide (1 ≤ count853 b)) else (if i < 855 then decide (2 ≤ count853 b) else decide (1 ≤ count855 b))))) else (if i < 862 then (if i < 859 then (if i < 857 then decide (2 ≤ count855 b) else (if i < 858 then decide (1 ≤ count857 b) else decide (2 ≤ count857 b))) else (if i < 860 then decide (3 ≤ count857 b) else (if i < 861 then decide (4 ≤ count857 b) else decide (1 ≤ count861 b)))) else (if i < 865 then (if i < 863 then decide (2 ≤ count861 b) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b))) else (if i < 867 then (if i < 866 then decide (1 ≤ count865 b) else decide (2 ≤ count865 b)) else (if i < 868 then decide (3 ≤ count865 b) else decide (4 ≤ count865 b))))))) else (if i < 894 then (if i < 881 then (if i < 875 then (if i < 872 then (if i < 870 then decide (1 ≤ count869 b) else (if i < 871 then decide (2 ≤ count869 b) else decide (3 ≤ count869 b))) else (if i < 873 then decide (4 ≤ count869 b) else (if i < 874 then decide (5 ≤ count869 b) else decide (6 ≤ count869 b)))) else (if i < 878 then (if i < 876 then decide (7 ≤ count869 b) else (if i < 877 then decide (8 ≤ count869 b) else decide (1 ≤ count877 b))) else (if i < 879 then decide (2 ≤ count877 b) else (if i < 880 then decide (3 ≤ count877 b) else decide (4 ≤ count877 b))))) else (if i < 887 then (if i < 884 then (if i < 882 then decide (5 ≤ count877 b) else (if i < 883 then decide (6 ≤ count877 b) else decide (7 ≤ count877 b))) else (if i < 885 then decide (8 ≤ count877 b) else (if i < 886 then decide (9 ≤ count877 b) else decide (10 ≤ count877 b)))) else (if i < 890 then (if i < 888 then decide (11 ≤ count877 b) else (if i < 889 then decide (12 ≤ count877 b) else decide (13 ≤ count877 b))) else (if i < 892 then (if i < 891 then decide (14 ≤ count877 b) else decide (15 ≤ count877 b)) else (if i < 893 then decide (1 ≤ count892 b) else decide (2 ≤ count892 b)))))) else (if i < 907 then (if i < 900 then (if i < 897 then (if i < 895 then decide (3 ≤ count892 b) else (if i < 896 then decide (4 ≤ count892 b) else decide (5 ≤ count892 b))) else (if i < 898 then decide (6 ≤ count892 b) else (if i < 899 then decide (7 ≤ count892 b) else decide (8 ≤ count892 b)))) else (if i < 903 then (if i < 901 then decide (9 ≤ count892 b) else (if i < 902 then decide (10 ≤ count892 b) else decide (11 ≤ count892 b))) else (if i < 905 then (if i < 904 then decide (12 ≤ count892 b) else decide (13 ≤ count892 b)) else (if i < 906 then decide (14 ≤ count892 b) else decide (15 ≤ count892 b))))) else (if i < 913 then (if i < 910 then (if i < 908 then decide (16 ≤ count892 b) else (if i < 909 then decide (17 ≤ count892 b) else decide (18 ≤ count892 b))) else (if i < 911 then decide (1 ≤ count910 b) else (if i < 912 then decide (2 ≤ count910 b) else decide (1 ≤ count912 b)))) else (if i < 916 then (if i < 914 then decide (2 ≤ count912 b) else (if i < 915 then decide (3 ≤ count912 b) else decide (1 ≤ count915 b))) else (if i < 918 then (if i < 917 then decide (2 ≤ count915 b) else decide (1 ≤ count917 b)) else (if i < 919 then decide (2 ≤ count917 b) else decide (1 ≤ count919 b)))))))) else (if i < 971 then (if i < 945 then (if i < 932 then (if i < 926 then (if i < 923 then (if i < 921 then decide (2 ≤ count919 b) else (if i < 922 then decide (3 ≤ count919 b) else decide (4 ≤ count919 b))) else (if i < 924 then decide (1 ≤ count923 b) else (if i < 925 then decide (2 ≤ count923 b) else decide (3 ≤ count923 b)))) else (if i < 929 then (if i < 927 then decide (4 ≤ count923 b) else (if i < 928 then decide (5 ≤ count923 b) else decide (6 ≤ count923 b))) else (if i < 930 then decide (7 ≤ count923 b) else (if i < 931 then decide (1 ≤ count930 b) else decide (2 ≤ count930 b))))) else (if i < 938 then (if i < 935 then (if i < 933 then decide (1 ≤ count932 b) else (if i < 934 then decide (2 ≤ count932 b) else decide (3 ≤ count932 b))) else (if i < 936 then decide (1 ≤ count935 b) else (if i < 937 then decide (2 ≤ count935 b) else decide (1 ≤ count937 b)))) else (if i < 941 then (if i < 939 then decide (2 ≤ count937 b) else (if i < 940 then decide (1 ≤ count939 b) else decide (2 ≤ count939 b))) else (if i < 943 then (if i < 942 then decide (3 ≤ count939 b) else decide (4 ≤ count939 b)) else (if i < 944 then decide (1 ≤ count943 b) else decide (2 ≤ count943 b)))))) else (if i < 958 then (if i < 951 then (if i < 948 then (if i < 946 then decide (3 ≤ count943 b) else (if i < 947 then decide (4 ≤ count943 b) else decide (5 ≤ count943 b))) else (if i < 949 then decide (6 ≤ count943 b) else (if i < 950 then decide (7 ≤ count943 b) else decide (1 ≤ count950 b)))) else (if i < 954 then (if i < 952 then decide (2 ≤ count950 b) else (if i < 953 then decide (3 ≤ count950 b) else decide (4 ≤ count950 b))) else (if i < 956 then (if i < 955 then decide (5 ≤ count950 b) else decide (6 ≤ count950 b)) else (if i < 957 then decide (7 ≤ count950 b) else decide (8 ≤ count950 b))))) else (if i < 964 then (if i < 961 then (if i < 959 then decide (9 ≤ count950 b) else (if i < 960 then decide (10 ≤ count950 b) else decide (11 ≤ count950 b))) else (if i < 962 then decide (12 ≤ count950 b) else (if i < 963 then decide (13 ≤ count950 b) else decide (14 ≤ count950 b)))) else (if i < 967 then (if i < 965 then decide (1 ≤ count964 b) else (if i < 966 then decide (2 ≤ count964 b) else decide (1 ≤ count966 b))) else (if i < 969 then (if i < 968 then decide (2 ≤ count966 b) else decide (3 ≤ count966 b)) else (if i < 970 then decide (1 ≤ count969 b) else decide (2 ≤ count969 b))))))) else (if i < 996 then (if i < 983 then (if i < 977 then (if i < 974 then (if i < 972 then decide (1 ≤ count971 b) else (if i < 973 then decide (2 ≤ count971 b) else decide (1 ≤ count973 b))) else (if i < 975 then decide (2 ≤ count973 b) else (if i < 976 then decide (3 ≤ count973 b) else decide (4 ≤ count973 b)))) else (if i < 980 then (if i < 978 then decide (1 ≤ count977 b) else (if i < 979 then decide (2 ≤ count977 b) else decide (3 ≤ count977 b))) else (if i < 981 then decide (4 ≤ count977 b) else (if i < 982 then decide (5 ≤ count977 b) else decide (6 ≤ count977 b))))) else (if i < 989 then (if i < 986 then (if i < 984 then decide (7 ≤ count977 b) else (if i < 985 then decide (1 ≤ count984 b) else decide (2 ≤ count984 b))) else (if i < 987 then decide (1 ≤ count986 b) else (if i < 988 then decide (2 ≤ count986 b) else decide (1 ≤ count988 b)))) else (if i < 992 then (if i < 990 then decide (2 ≤ count988 b) else (if i < 991 then decide (3 ≤ count988 b) else decide (4 ≤ count988 b))) else (if i < 994 then (if i < 993 then decide (1 ≤ count992 b) else decide (2 ≤ count992 b)) else (if i < 995 then decide (1 ≤ count994 b) else decide (2 ≤ count994 b)))))) else (if i < 1009 then (if i < 1002 then (if i < 999 then (if i < 997 then decide (1 ≤ count996 b) else (if i < 998 then decide (2 ≤ count996 b) else decide (3 ≤ count996 b))) else (if i < 1000 then decide (4 ≤ count996 b) else (if i < 1001 then decide (1 ≤ count1000 b) else decide (2 ≤ count1000 b)))) else (if i < 1005 then (if i < 1003 then decide (3 ≤ count1000 b) else (if i < 1004 then decide (4 ≤ count1000 b) else decide (5 ≤ count1000 b))) else (if i < 1007 then (if i < 1006 then decide (6 ≤ count1000 b) else decide (7 ≤ count1000 b)) else (if i < 1008 then decide (8 ≤ count1000 b) else decide (1 ≤ count1008 b))))) else (if i < 1015 then (if i < 1012 then (if i < 1010 then decide (2 ≤ count1008 b) else (if i < 1011 then decide (3 ≤ count1008 b) else decide (4 ≤ count1008 b))) else (if i < 1013 then decide (5 ≤ count1008 b) else (if i < 1014 then decide (6 ≤ count1008 b) else decide (7 ≤ count1008 b)))) else (if i < 1018 then (if i < 1016 then decide (8 ≤ count1008 b) else (if i < 1017 then decide (9 ≤ count1008 b) else decide (10 ≤ count1008 b))) else (if i < 1020 then (if i < 1019 then decide (11 ≤ count1008 b) else decide (12 ≤ count1008 b)) else (if i < 1021 then decide (13 ≤ count1008 b) else decide (14 ≤ count1008 b))))))))) else (if i < 1124 then (if i < 1073 then (if i < 1047 then (if i < 1034 then (if i < 1028 then (if i < 1025 then (if i < 1023 then decide (15 ≤ count1008 b) else (if i < 1024 then decide (1 ≤ count1023 b) else decide (2 ≤ count1023 b))) else (if i < 1026 then decide (3 ≤ count1023 b) else (if i < 1027 then decide (4 ≤ count1023 b) else decide (5 ≤ count1023 b)))) else (if i < 1031 then (if i < 1029 then decide (6 ≤ count1023 b) else (if i < 1030 then decide (7 ≤ count1023 b) else decide (8 ≤ count1023 b))) else (if i < 1032 then decide (9 ≤ count1023 b) else (if i < 1033 then decide (10 ≤ count1023 b) else decide (11 ≤ count1023 b))))) else (if i < 1040 then (if i < 1037 then (if i < 1035 then decide (12 ≤ count1023 b) else (if i < 1036 then decide (13 ≤ count1023 b) else decide (14 ≤ count1023 b))) else (if i < 1038 then decide (15 ≤ count1023 b) else (if i < 1039 then decide (16 ≤ count1023 b) else decide (17 ≤ count1023 b)))) else (if i < 1043 then (if i < 1041 then decide (18 ≤ count1023 b) else (if i < 1042 then decide (1 ≤ count1041 b) else decide (2 ≤ count1041 b))) else (if i < 1045 then (if i < 1044 then decide (3 ≤ count1041 b) else decide (4 ≤ count1041 b)) else (if i < 1046 then decide (5 ≤ count1041 b) else decide (6 ≤ count1041 b)))))) else (if i < 1060 then (if i < 1053 then (if i < 1050 then (if i < 1048 then decide (7 ≤ count1041 b) else (if i < 1049 then decide (8 ≤ count1041 b) else decide (9 ≤ count1041 b))) else (if i < 1051 then decide (10 ≤ count1041 b) else (if i < 1052 then decide (11 ≤ count1041 b) else decide (12 ≤ count1041 b)))) else (if i < 1056 then (if i < 1054 then decide (13 ≤ count1041 b) else (if i < 1055 then decide (14 ≤ count1041 b) else decide (15 ≤ count1041 b))) else (if i < 1058 then (if i < 1057 then decide (16 ≤ count1041 b) else decide (17 ≤ count1041 b)) else (if i < 1059 then decide (18 ≤ count1041 b) else decide (1 ≤ count1059 b))))) else (if i < 1066 then (if i < 1063 then (if i < 1061 then decide (2 ≤ count1059 b) else (if i < 1062 then decide (1 ≤ count1061 b) else decide (2 ≤ count1061 b))) else (if i < 1064 then decide (3 ≤ count1061 b) else (if i < 1065 then decide (1 ≤ count1064 b) else decide (2 ≤ count1064 b)))) else (if i < 1069 then (if i < 1067 then decide (1 ≤ count1066 b) else (if i < 1068 then decide (2 ≤ count1066 b) else decide (1 ≤ count1068 b))) else (if i < 1071 then (if i < 1070 then decide (2 ≤ count1068 b) else decide (3 ≤ count1068 b)) else (if i < 1072 then decide (4 ≤ count1068 b) else decide (1 ≤ count1072 b))))))) else (if i < 1098 then (if i < 1085 then (if i < 1079 then (if i < 1076 then (if i < 1074 then decide (2 ≤ count1072 b) else (if i < 1075 then decide (3 ≤ count1072 b) else decide (4 ≤ count1072 b))) else (if i < 1077 then decide (5 ≤ count1072 b) else (if i < 1078 then decide (6 ≤ count1072 b) else decide (7 ≤ count1072 b)))) else (if i < 1082 then (if i < 1080 then decide (1 ≤ count1079 b) else (if i < 1081 then decide (2 ≤ count1079 b) else decide (1 ≤ count1081 b))) else (if i < 1083 then decide (2 ≤ count1081 b) else (if i < 1084 then decide (3 ≤ count1081 b) else decide (1 ≤ count1084 b))))) else (if i < 1091 then (if i < 1088 then (if i < 1086 then decide (2 ≤ count1084 b) else (if i < 1087 then decide (1 ≤ count1086 b) else decide (2 ≤ count1086 b))) else (if i < 1089 then decide (1 ≤ count1088 b) else (if i < 1090 then decide (2 ≤ count1088 b) else decide (3 ≤ count1088 b)))) else (if i < 1094 then (if i < 1092 then decide (4 ≤ count1088 b) else (if i < 1093 then decide (1 ≤ count1092 b) else decide (2 ≤ count1092 b))) else (if i < 1096 then (if i < 1095 then decide (3 ≤ count1092 b) else decide (4 ≤ count1092 b)) else (if i < 1097 then decide (5 ≤ count1092 b) else decide (6 ≤ count1092 b)))))) else (if i < 1111 then (if i < 1104 then (if i < 1101 then (if i < 1099 then decide (7 ≤ count1092 b) else (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b))) else (if i < 1102 then decide (3 ≤ count1099 b) else (if i < 1103 then decide (4 ≤ count1099 b) else decide (5 ≤ count1099 b)))) else (if i < 1107 then (if i < 1105 then decide (6 ≤ count1099 b) else (if i < 1106 then decide (7 ≤ count1099 b) else decide (8 ≤ count1099 b))) else (if i < 1109 then (if i < 1108 then decide (9 ≤ count1099 b) else decide (10 ≤ count1099 b)) else (if i < 1110 then decide (11 ≤ count1099 b) else decide (12 ≤ count1099 b))))) else (if i < 1117 then (if i < 1114 then (if i < 1112 then decide (13 ≤ count1099 b) else (if i < 1113 then decide (14 ≤ count1099 b) else decide (1 ≤ count1113 b))) else (if i < 1115 then decide (2 ≤ count1113 b) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b)))) else (if i < 1120 then (if i < 1118 then decide (3 ≤ count1115 b) else (if i < 1119 then decide (1 ≤ count1118 b) else decide (2 ≤ count1118 b))) else (if i < 1122 then (if i < 1121 then decide (1 ≤ count1120 b) else decide (2 ≤ count1120 b)) else (if i < 1123 then decide (1 ≤ count1122 b) else decide (2 ≤ count1122 b)))))))) else (if i < 1175 then (if i < 1149 then (if i < 1136 then (if i < 1130 then (if i < 1127 then (if i < 1125 then decide (3 ≤ count1122 b) else (if i < 1126 then decide (4 ≤ count1122 b) else decide (1 ≤ count1126 b))) else (if i < 1128 then decide (2 ≤ count1126 b) else (if i < 1129 then decide (3 ≤ count1126 b) else decide (4 ≤ count1126 b)))) else (if i < 1133 then (if i < 1131 then decide (5 ≤ count1126 b) else (if i < 1132 then decide (6 ≤ count1126 b) else decide (7 ≤ count1126 b))) else (if i < 1134 then decide (1 ≤ count1133 b) else (if i < 1135 then decide (2 ≤ count1133 b) else decide (1 ≤ count1135 b))))) else (if i < 1142 then (if i < 1139 then (if i < 1137 then decide (2 ≤ count1135 b) else (if i < 1138 then decide (3 ≤ count1135 b) else decide (1 ≤ count1138 b))) else (if i < 1140 then decide (2 ≤ count1138 b) else (if i < 1141 then decide (1 ≤ count1140 b) else decide (2 ≤ count1140 b)))) else (if i < 1145 then (if i < 1143 then decide (1 ≤ count1142 b) else (if i < 1144 then decide (2 ≤ count1142 b) else decide (3 ≤ count1142 b))) else (if i < 1147 then (if i < 1146 then decide (4 ≤ count1142 b) else decide (1 ≤ count1146 b)) else (if i < 1148 then decide (2 ≤ count1146 b) else decide (3 ≤ count1146 b)))))) else (if i < 1162 then (if i < 1155 then (if i < 1152 then (if i < 1150 then decide (4 ≤ count1146 b) else (if i < 1151 then decide (5 ≤ count1146 b) else decide (6 ≤ count1146 b))) else (if i < 1153 then decide (7 ≤ count1146 b) else (if i < 1154 then decide (1 ≤ count1153 b) else decide (2 ≤ count1153 b)))) else (if i < 1158 then (if i < 1156 then decide (3 ≤ count1153 b) else (if i < 1157 then decide (4 ≤ count1153 b) else decide (5 ≤ count1153 b))) else (if i < 1160 then (if i < 1159 then decide (6 ≤ count1153 b) else decide (7 ≤ count1153 b)) else (if i < 1161 then decide (8 ≤ count1153 b) else decide (9 ≤ count1153 b))))) else (if i < 1168 then (if i < 1165 then (if i < 1163 then decide (10 ≤ count1153 b) else (if i < 1164 then decide (11 ≤ count1153 b) else decide (12 ≤ count1153 b))) else (if i < 1166 then decide (13 ≤ count1153 b) else (if i < 1167 then decide (14 ≤ count1153 b) else decide (1 ≤ count1167 b)))) else (if i < 1171 then (if i < 1169 then decide (2 ≤ count1167 b) else (if i < 1170 then decide (3 ≤ count1167 b) else decide (4 ≤ count1167 b))) else (if i < 1173 then (if i < 1172 then decide (5 ≤ count1167 b) else decide (6 ≤ count1167 b)) else (if i < 1174 then decide (7 ≤ count1167 b) else decide (8 ≤ count1167 b))))))) else (if i < 1201 then (if i < 1188 then (if i < 1181 then (if i < 1178 then (if i < 1176 then decide (9 ≤ count1167 b) else (if i < 1177 then decide (10 ≤ count1167 b) else decide (11 ≤ count1167 b))) else (if i < 1179 then decide (12 ≤ count1167 b) else (if i < 1180 then decide (13 ≤ count1167 b) else decide (14 ≤ count1167 b)))) else (if i < 1184 then (if i < 1182 then decide (15 ≤ count1167 b) else (if i < 1183 then decide (16 ≤ count1167 b) else decide (17 ≤ count1167 b))) else (if i < 1186 then (if i < 1185 then decide (18 ≤ count1167 b) else decide (19 ≤ count1167 b)) else (if i < 1187 then decide (20 ≤ count1167 b) else decide (21 ≤ count1167 b))))) else (if i < 1194 then (if i < 1191 then (if i < 1189 then decide (22 ≤ count1167 b) else (if i < 1190 then decide (23 ≤ count1167 b) else decide (24 ≤ count1167 b))) else (if i < 1192 then decide (25 ≤ count1167 b) else (if i < 1193 then decide (26 ≤ count1167 b) else decide (27 ≤ count1167 b)))) else (if i < 1197 then (if i < 1195 then decide (28 ≤ count1167 b) else (if i < 1196 then decide (1 ≤ count1195 b) else decide (2 ≤ count1195 b))) else (if i < 1199 then (if i < 1198 then decide (1 ≤ count1197 b) else decide (2 ≤ count1197 b)) else (if i < 1200 then decide (3 ≤ count1197 b) else decide (1 ≤ count1200 b)))))) else (if i < 1214 then (if i < 1207 then (if i < 1204 then (if i < 1202 then decide (2 ≤ count1200 b) else (if i < 1203 then decide (1 ≤ count1202 b) else decide (2 ≤ count1202 b))) else (if i < 1205 then decide (1 ≤ count1204 b) else (if i < 1206 then decide (2 ≤ count1204 b) else decide (3 ≤ count1204 b)))) else (if i < 1210 then (if i < 1208 then decide (4 ≤ count1204 b) else (if i < 1209 then decide (1 ≤ count1208 b) else decide (2 ≤ count1208 b))) else (if i < 1212 then (if i < 1211 then decide (3 ≤ count1208 b) else decide (4 ≤ count1208 b)) else (if i < 1213 then decide (5 ≤ count1208 b) else decide (6 ≤ count1208 b))))) else (if i < 1220 then (if i < 1217 then (if i < 1215 then decide (7 ≤ count1208 b) else (if i < 1216 then decide (1 ≤ count1215 b) else decide (2 ≤ count1215 b))) else (if i < 1218 then decide (1 ≤ count1217 b) else (if i < 1219 then decide (2 ≤ count1217 b) else decide (3 ≤ count1217 b)))) else (if i < 1223 then (if i < 1221 then decide (1 ≤ count1220 b) else (if i < 1222 then decide (2 ≤ count1220 b) else decide (1 ≤ count1222 b))) else (if i < 1225 then (if i < 1224 then decide (2 ≤ count1222 b) else decide (1 ≤ count1224 b)) else (if i < 1226 then decide (2 ≤ count1224 b) else decide (3 ≤ count1224 b)))))))))) else (if i < 1432 then (if i < 1329 then (if i < 1278 then (if i < 1252 then (if i < 1239 then (if i < 1233 then (if i < 1230 then (if i < 1228 then decide (4 ≤ count1224 b) else (if i < 1229 then decide (1 ≤ count1228 b) else decide (2 ≤ count1228 b))) else (if i < 1231 then decide (3 ≤ count1228 b) else (if i < 1232 then decide (4 ≤ count1228 b) else decide (5 ≤ count1228 b)))) else (if i < 1236 then (if i < 1234 then decide (6 ≤ count1228 b) else (if i < 1235 then decide (7 ≤ count1228 b) else decide (1 ≤ count1235 b))) else (if i < 1237 then decide (2 ≤ count1235 b) else (if i < 1238 then decide (3 ≤ count1235 b) else decide (4 ≤ count1235 b))))) else (if i < 1245 then (if i < 1242 then (if i < 1240 then decide (5 ≤ count1235 b) else (if i < 1241 then decide (6 ≤ count1235 b) else decide (7 ≤ count1235 b))) else (if i < 1243 then decide (8 ≤ count1235 b) else (if i < 1244 then decide (9 ≤ count1235 b) else decide (10 ≤ count1235 b)))) else (if i < 1248 then (if i < 1246 then decide (11 ≤ count1235 b) else (if i < 1247 then decide (12 ≤ count1235 b) else decide (13 ≤ count1235 b))) else (if i < 1250 then (if i < 1249 then decide (14 ≤ count1235 b) else decide (1 ≤ count1249 b)) else (if i < 1251 then decide (2 ≤ count1249 b) else decide (1 ≤ count1251 b)))))) else (if i < 1265 then (if i < 1258 then (if i < 1255 then (if i < 1253 then decide (2 ≤ count1251 b) else (if i < 1254 then decide (3 ≤ count1251 b) else decide (1 ≤ count1254 b))) else (if i < 1256 then decide (2 ≤ count1254 b) else (if i < 1257 then decide (1 ≤ count1256 b) else decide (2 ≤ count1256 b)))) else (if i < 1261 then (if i < 1259 then decide (1 ≤ count1258 b) else (if i < 1260 then decide (2 ≤ count1258 b) else decide (3 ≤ count1258 b))) else (if i < 1263 then (if i < 1262 then decide (4 ≤ count1258 b) else decide (1 ≤ count1262 b)) else (if i < 1264 then decide (2 ≤ count1262 b) else decide (3 ≤ count1262 b))))) else (if i < 1271 then (if i < 1268 then (if i < 1266 then decide (4 ≤ count1262 b) else (if i < 1267 then decide (5 ≤ count1262 b) else decide (6 ≤ count1262 b))) else (if i < 1269 then decide (7 ≤ count1262 b) else (if i < 1270 then decide (1 ≤ count1269 b) else decide (2 ≤ count1269 b)))) else (if i < 1274 then (if i < 1272 then decide (1 ≤ count1271 b) else (if i < 1273 then decide (2 ≤ count1271 b) else decide (3 ≤ count1271 b))) else (if i < 1276 then (if i < 1275 then decide (1 ≤ count1274 b) else decide (2 ≤ count1274 b)) else (if i < 1277 then decide (1 ≤ count1276 b) else decide (2 ≤ count1276 b))))))) else (if i < 1303 then (if i < 1290 then (if i < 1284 then (if i < 1281 then (if i < 1279 then decide (1 ≤ count1278 b) else (if i < 1280 then decide (2 ≤ count1278 b) else decide (3 ≤ count1278 b))) else (if i < 1282 then decide (4 ≤ count1278 b) else (if i < 1283 then decide (1 ≤ count1282 b) else decide (2 ≤ count1282 b)))) else (if i < 1287 then (if i < 1285 then decide (3 ≤ count1282 b) else (if i < 1286 then decide (4 ≤ count1282 b) else decide (5 ≤ count1282 b))) else (if i < 1288 then decide (6 ≤ count1282 b) else (if i < 1289 then decide (7 ≤ count1282 b) else decide (1 ≤ count1289 b))))) else (if i < 1296 then (if i < 1293 then (if i < 1291 then decide (2 ≤ count1289 b) else (if i < 1292 then decide (3 ≤ count1289 b) else decide (4 ≤ count1289 b))) else (if i < 1294 then decide (5 ≤ count1289 b) else (if i < 1295 then decide (6 ≤ count1289 b) else decide (7 ≤ count1289 b)))) else (if i < 1299 then (if i < 1297 then decide (8 ≤ count1289 b) else (if i < 1298 then decide (9 ≤ count1289 b) else decide (10 ≤ count1289 b))) else (if i < 1301 then (if i < 1300 then decide (11 ≤ count1289 b) else decide (12 ≤ count1289 b)) else (if i < 1302 then decide (13 ≤ count1289 b) else decide (14 ≤ count1289 b)))))) else (if i < 1316 then (if i < 1309 then (if i < 1306 then (if i < 1304 then decide (1 ≤ count1303 b) else (if i < 1305 then decide (2 ≤ count1303 b) else decide (3 ≤ count1303 b))) else (if i < 1307 then decide (4 ≤ count1303 b) else (if i < 1308 then decide (5 ≤ count1303 b) else decide (6 ≤ count1303 b)))) else (if i < 1312 then (if i < 1310 then decide (7 ≤ count1303 b) else (if i < 1311 then decide (8 ≤ count1303 b) else decide (9 ≤ count1303 b))) else (if i < 1314 then (if i < 1313 then decide (10 ≤ count1303 b) else decide (11 ≤ count1303 b)) else (if i < 1315 then decide (12 ≤ count1303 b) else decide (13 ≤ count1303 b))))) else (if i < 1322 then (if i < 1319 then (if i < 1317 then decide (14 ≤ count1303 b) else (if i < 1318 then decide (15 ≤ count1303 b) else decide (16 ≤ count1303 b))) else (if i < 1320 then decide (17 ≤ count1303 b) else (if i < 1321 then decide (18 ≤ count1303 b) else decide (19 ≤ count1303 b)))) else (if i < 1325 then (if i < 1323 then decide (20 ≤ count1303 b) else (if i < 1324 then decide (21 ≤ count1303 b) else decide (22 ≤ count1303 b))) else (if i < 1327 then (if i < 1326 then decide (23 ≤ count1303 b) else decide (24 ≤ count1303 b)) else (if i < 1328 then decide (25 ≤ count1303 b) else decide (26 ≤ count1303 b)))))))) else (if i < 1380 then (if i < 1354 then (if i < 1341 then (if i < 1335 then (if i < 1332 then (if i < 1330 then decide (27 ≤ count1303 b) else (if i < 1331 then decide (28 ≤ count1303 b) else decide (1 ≤ count1331 b))) else (if i < 1333 then decide (2 ≤ count1331 b) else (if i < 1334 then decide (3 ≤ count1331 b) else decide (4 ≤ count1331 b)))) else (if i < 1338 then (if i < 1336 then decide (5 ≤ count1331 b) else (if i < 1337 then decide (6 ≤ count1331 b) else decide (7 ≤ count1331 b))) else (if i < 1339 then decide (8 ≤ count1331 b) else (if i < 1340 then decide (9 ≤ count1331 b) else decide (10 ≤ count1331 b))))) else (if i < 1347 then (if i < 1344 then (if i < 1342 then decide (11 ≤ count1331 b) else (if i < 1343 then decide (12 ≤ count1331 b) else decide (13 ≤ count1331 b))) else (if i < 1345 then decide (14 ≤ count1331 b) else (if i < 1346 then decide (15 ≤ count1331 b) else decide (16 ≤ count1331 b)))) else (if i < 1350 then (if i < 1348 then decide (17 ≤ count1331 b) else (if i < 1349 then decide (18 ≤ count1331 b) else decide (19 ≤ count1331 b))) else (if i < 1352 then (if i < 1351 then decide (20 ≤ count1331 b) else decide (21 ≤ count1331 b)) else (if i < 1353 then decide (22 ≤ count1331 b) else decide (23 ≤ count1331 b)))))) else (if i < 1367 then (if i < 1360 then (if i < 1357 then (if i < 1355 then decide (24 ≤ count1331 b) else (if i < 1356 then decide (25 ≤ count1331 b) else decide (26 ≤ count1331 b))) else (if i < 1358 then decide (27 ≤ count1331 b) else (if i < 1359 then decide (28 ≤ count1331 b) else decide (29 ≤ count1331 b)))) else (if i < 1363 then (if i < 1361 then decide (30 ≤ count1331 b) else (if i < 1362 then decide (31 ≤ count1331 b) else decide (32 ≤ count1331 b))) else (if i < 1365 then (if i < 1364 then decide (33 ≤ count1331 b) else decide (34 ≤ count1331 b)) else (if i < 1366 then decide (35 ≤ count1331 b) else decide (36 ≤ count1331 b))))) else (if i < 1373 then (if i < 1370 then (if i < 1368 then decide (37 ≤ count1331 b) else (if i < 1369 then decide (38 ≤ count1331 b) else decide (39 ≤ count1331 b))) else (if i < 1371 then decide (40 ≤ count1331 b) else (if i < 1372 then decide (41 ≤ count1331 b) else decide (42 ≤ count1331 b)))) else (if i < 1376 then (if i < 1374 then decide (1 ≤ count1373 b) else (if i < 1375 then decide (2 ≤ count1373 b) else decide (1 ≤ count1375 b))) else (if i < 1378 then (if i < 1377 then decide (2 ≤ count1375 b) else decide (3 ≤ count1375 b)) else (if i < 1379 then decide (1 ≤ count1378 b) else decide (2 ≤ count1378 b))))))) else (if i < 1406 then (if i < 1393 then (if i < 1386 then (if i < 1383 then (if i < 1381 then decide (1 ≤ count1380 b) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (1 ≤ count1382 b))) else (if i < 1384 then decide (2 ≤ count1382 b) else (if i < 1385 then decide (3 ≤ count1382 b) else decide (4 ≤ count1382 b)))) else (if i < 1389 then (if i < 1387 then decide (1 ≤ count1386 b) else (if i < 1388 then decide (2 ≤ count1386 b) else decide (3 ≤ count1386 b))) else (if i < 1391 then (if i < 1390 then decide (4 ≤ count1386 b) else decide (5 ≤ count1386 b)) else (if i < 1392 then decide (6 ≤ count1386 b) else decide (7 ≤ count1386 b))))) else (if i < 1399 then (if i < 1396 then (if i < 1394 then decide (1 ≤ count1393 b) else (if i < 1395 then decide (2 ≤ count1393 b) else decide (1 ≤ count1395 b))) else (if i < 1397 then decide (2 ≤ count1395 b) else (if i < 1398 then decide (3 ≤ count1395 b) else decide (1 ≤ count1398 b)))) else (if i < 1402 then (if i < 1400 then decide (2 ≤ count1398 b) else (if i < 1401 then decide (1 ≤ count1400 b) else decide (2 ≤ count1400 b))) else (if i < 1404 then (if i < 1403 then decide (1 ≤ count1402 b) else decide (2 ≤ count1402 b)) else (if i < 1405 then decide (3 ≤ count1402 b) else decide (4 ≤ count1402 b)))))) else (if i < 1419 then (if i < 1412 then (if i < 1409 then (if i < 1407 then decide (1 ≤ count1406 b) else (if i < 1408 then decide (2 ≤ count1406 b) else decide (3 ≤ count1406 b))) else (if i < 1410 then decide (4 ≤ count1406 b) else (if i < 1411 then decide (5 ≤ count1406 b) else decide (6 ≤ count1406 b)))) else (if i < 1415 then (if i < 1413 then decide (7 ≤ count1406 b) else (if i < 1414 then decide (1 ≤ count1413 b) else decide (2 ≤ count1413 b))) else (if i < 1417 then (if i < 1416 then decide (3 ≤ count1413 b) else decide (4 ≤ count1413 b)) else (if i < 1418 then decide (5 ≤ count1413 b) else decide (6 ≤ count1413 b))))) else (if i < 1425 then (if i < 1422 then (if i < 1420 then decide (7 ≤ count1413 b) else (if i < 1421 then decide (8 ≤ count1413 b) else decide (9 ≤ count1413 b))) else (if i < 1423 then decide (10 ≤ count1413 b) else (if i < 1424 then decide (11 ≤ count1413 b) else decide (12 ≤ count1413 b)))) else (if i < 1428 then (if i < 1426 then decide (13 ≤ count1413 b) else (if i < 1427 then decide (14 ≤ count1413 b) else decide (1 ≤ count1427 b))) else (if i < 1430 then (if i < 1429 then decide (2 ≤ count1427 b) else decide (1 ≤ count1429 b)) else (if i < 1431 then decide (2 ≤ count1429 b) else decide (3 ≤ count1429 b))))))))) else (if i < 1534 then (if i < 1483 then (if i < 1457 then (if i < 1444 then (if i < 1438 then (if i < 1435 then (if i < 1433 then decide (1 ≤ count1432 b) else (if i < 1434 then decide (2 ≤ count1432 b) else decide (1 ≤ count1434 b))) else (if i < 1436 then decide (2 ≤ count1434 b) else (if i < 1437 then decide (1 ≤ count1436 b) else decide (2 ≤ count1436 b)))) else (if i < 1441 then (if i < 1439 then decide (3 ≤ count1436 b) else (if i < 1440 then decide (4 ≤ count1436 b) else decide (1 ≤ count1440 b))) else (if i < 1442 then decide (2 ≤ count1440 b) else (if i < 1443 then decide (3 ≤ count1440 b) else decide (4 ≤ count1440 b))))) else (if i < 1450 then (if i < 1447 then (if i < 1445 then decide (5 ≤ count1440 b) else (if i < 1446 then decide (6 ≤ count1440 b) else decide (7 ≤ count1440 b))) else (if i < 1448 then decide (1 ≤ count1447 b) else (if i < 1449 then decide (2 ≤ count1447 b) else decide (1 ≤ count1449 b)))) else (if i < 1453 then (if i < 1451 then decide (2 ≤ count1449 b) else (if i < 1452 then decide (3 ≤ count1449 b) else decide (1 ≤ count1452 b))) else (if i < 1455 then (if i < 1454 then decide (2 ≤ count1452 b) else decide (1 ≤ count1454 b)) else (if i < 1456 then decide (2 ≤ count1454 b) else decide (1 ≤ count1456 b)))))) else (if i < 1470 then (if i < 1463 then (if i < 1460 then (if i < 1458 then decide (2 ≤ count1456 b) else (if i < 1459 then decide (3 ≤ count1456 b) else decide (4 ≤ count1456 b))) else (if i < 1461 then decide (1 ≤ count1460 b) else (if i < 1462 then decide (2 ≤ count1460 b) else decide (3 ≤ count1460 b)))) else (if i < 1466 then (if i < 1464 then decide (4 ≤ count1460 b) else (if i < 1465 then decide (5 ≤ count1460 b) else decide (6 ≤ count1460 b))) else (if i < 1468 then (if i < 1467 then decide (7 ≤ count1460 b) else decide (1 ≤ count1467 b)) else (if i < 1469 then decide (2 ≤ count1467 b) else decide (3 ≤ count1467 b))))) else (if i < 1476 then (if i < 1473 then (if i < 1471 then decide (4 ≤ count1467 b) else (if i < 1472 then decide (5 ≤ count1467 b) else decide (6 ≤ count1467 b))) else (if i < 1474 then decide (7 ≤ count1467 b) else (if i < 1475 then decide (8 ≤ count1467 b) else decide (9 ≤ count1467 b)))) else (if i < 1479 then (if i < 1477 then decide (10 ≤ count1467 b) else (if i < 1478 then decide (11 ≤ count1467 b) else decide (12 ≤ count1467 b))) else (if i < 1481 then (if i < 1480 then decide (13 ≤ count1467 b) else decide (14 ≤ count1467 b)) else (if i < 1482 then decide (1 ≤ count1481 b) else decide (2 ≤ count1481 b))))))) else (if i < 1508 then (if i < 1495 then (if i < 1489 then (if i < 1486 then (if i < 1484 then decide (3 ≤ count1481 b) else (if i < 1485 then decide (4 ≤ count1481 b) else decide (5 ≤ count1481 b))) else (if i < 1487 then decide (6 ≤ count1481 b) else (if i < 1488 then decide (7 ≤ count1481 b) else decide (8 ≤ count1481 b)))) else (if i < 1492 then (if i < 1490 then decide (9 ≤ count1481 b) else (if i < 1491 then decide (10 ≤ count1481 b) else decide (11 ≤ count1481 b))) else (if i < 1493 then decide (12 ≤ count1481 b) else (if i < 1494 then decide (13 ≤ count1481 b) else decide (14 ≤ count1481 b))))) else (if i < 1501 then (if i < 1498 then (if i < 1496 then decide (15 ≤ count1481 b) else (if i < 1497 then decide (16 ≤ count1481 b) else decide (1 ≤ count1497 b))) else (if i < 1499 then decide (2 ≤ count1497 b) else (if i < 1500 then decide (1 ≤ count1499 b) else decide (2 ≤ count1499 b)))) else (if i < 1504 then (if i < 1502 then decide (3 ≤ count1499 b) else (if i < 1503 then decide (1 ≤ count1502 b) else decide (2 ≤ count1502 b))) else (if i < 1506 then (if i < 1505 then decide (1 ≤ count1504 b) else decide (2 ≤ count1504 b)) else (if i < 1507 then decide (1 ≤ count1506 b) else decide (2 ≤ count1506 b)))))) else (if i < 1521 then (if i < 1514 then (if i < 1511 then (if i < 1509 then decide (3 ≤ count1506 b) else (if i < 1510 then decide (4 ≤ count1506 b) else decide (1 ≤ count1510 b))) else (if i < 1512 then decide (2 ≤ count1510 b) else (if i < 1513 then decide (3 ≤ count1510 b) else decide (4 ≤ count1510 b)))) else (if i < 1517 then (if i < 1515 then decide (5 ≤ count1510 b) else (if i < 1516 then decide (6 ≤ count1510 b) else decide (7 ≤ count1510 b))) else (if i < 1519 then (if i < 1518 then decide (1 ≤ count1517 b) else decide (2 ≤ count1517 b)) else (if i < 1520 then decide (1 ≤ count1519 b) else decide (2 ≤ count1519 b))))) else (if i < 1527 then (if i < 1524 then (if i < 1522 then decide (3 ≤ count1519 b) else (if i < 1523 then decide (1 ≤ count1522 b) else decide (2 ≤ count1522 b))) else (if i < 1525 then decide (1 ≤ count1524 b) else (if i < 1526 then decide (2 ≤ count1524 b) else decide (1 ≤ count1526 b)))) else (if i < 1530 then (if i < 1528 then decide (2 ≤ count1526 b) else (if i < 1529 then decide (3 ≤ count1526 b) else decide (4 ≤ count1526 b))) else (if i < 1532 then (if i < 1531 then decide (1 ≤ count1530 b) else decide (2 ≤ count1530 b)) else (if i < 1533 then decide (3 ≤ count1530 b) else decide (4 ≤ count1530 b)))))))) else (if i < 1585 then (if i < 1559 then (if i < 1546 then (if i < 1540 then (if i < 1537 then (if i < 1535 then decide (5 ≤ count1530 b) else (if i < 1536 then decide (6 ≤ count1530 b) else decide (7 ≤ count1530 b))) else (if i < 1538 then decide (1 ≤ count1537 b) else (if i < 1539 then decide (2 ≤ count1537 b) else decide (3 ≤ count1537 b)))) else (if i < 1543 then (if i < 1541 then decide (4 ≤ count1537 b) else (if i < 1542 then decide (5 ≤ count1537 b) else decide (6 ≤ count1537 b))) else (if i < 1544 then decide (7 ≤ count1537 b) else (if i < 1545 then decide (8 ≤ count1537 b) else decide (9 ≤ count1537 b))))) else (if i < 1552 then (if i < 1549 then (if i < 1547 then decide (10 ≤ count1537 b) else (if i < 1548 then decide (11 ≤ count1537 b) else decide (12 ≤ count1537 b))) else (if i < 1550 then decide (13 ≤ count1537 b) else (if i < 1551 then decide (14 ≤ count1537 b) else decide (1 ≤ count1551 b)))) else (if i < 1555 then (if i < 1553 then decide (2 ≤ count1551 b) else (if i < 1554 then decide (1 ≤ count1553 b) else decide (2 ≤ count1553 b))) else (if i < 1557 then (if i < 1556 then decide (3 ≤ count1553 b) else decide (1 ≤ count1556 b)) else (if i < 1558 then decide (2 ≤ count1556 b) else decide (1 ≤ count1558 b)))))) else (if i < 1572 then (if i < 1565 then (if i < 1562 then (if i < 1560 then decide (2 ≤ count1558 b) else (if i < 1561 then decide (1 ≤ count1560 b) else decide (2 ≤ count1560 b))) else (if i < 1563 then decide (3 ≤ count1560 b) else (if i < 1564 then decide (4 ≤ count1560 b) else decide (1 ≤ count1564 b)))) else (if i < 1568 then (if i < 1566 then decide (2 ≤ count1564 b) else (if i < 1567 then decide (3 ≤ count1564 b) else decide (4 ≤ count1564 b))) else (if i < 1570 then (if i < 1569 then decide (5 ≤ count1564 b) else decide (6 ≤ count1564 b)) else (if i < 1571 then decide (7 ≤ count1564 b) else decide (1 ≤ count1571 b))))) else (if i < 1578 then (if i < 1575 then (if i < 1573 then decide (2 ≤ count1571 b) else (if i < 1574 then decide (1 ≤ count1573 b) else decide (2 ≤ count1573 b))) else (if i < 1576 then decide (3 ≤ count1573 b) else (if i < 1577 then decide (1 ≤ count1576 b) else decide (2 ≤ count1576 b)))) else (if i < 1581 then (if i < 1579 then decide (1 ≤ count1578 b) else (if i < 1580 then decide (2 ≤ count1578 b) else decide (1 ≤ count1580 b))) else (if i < 1583 then (if i < 1582 then decide (2 ≤ count1580 b) else decide (3 ≤ count1580 b)) else (if i < 1584 then decide (4 ≤ count1580 b) else decide (1 ≤ count1584 b))))))) else (if i < 1611 then (if i < 1598 then (if i < 1591 then (if i < 1588 then (if i < 1586 then decide (2 ≤ count1584 b) else (if i < 1587 then decide (3 ≤ count1584 b) else decide (4 ≤ count1584 b))) else (if i < 1589 then decide (5 ≤ count1584 b) else (if i < 1590 then decide (6 ≤ count1584 b) else decide (7 ≤ count1584 b)))) else (if i < 1594 then (if i < 1592 then decide (1 ≤ count1591 b) else (if i < 1593 then decide (2 ≤ count1591 b) else decide (3 ≤ count1591 b))) else (if i < 1596 then (if i < 1595 then decide (4 ≤ count1591 b) else decide (5 ≤ count1591 b)) else (if i < 1597 then decide (6 ≤ count1591 b) else decide (7 ≤ count1591 b))))) else (if i < 1604 then (if i < 1601 then (if i < 1599 then decide (8 ≤ count1591 b) else (if i < 1600 then decide (9 ≤ count1591 b) else decide (10 ≤ count1591 b))) else (if i < 1602 then decide (11 ≤ count1591 b) else (if i < 1603 then decide (12 ≤ count1591 b) else decide (13 ≤ count1591 b)))) else (if i < 1607 then (if i < 1605 then decide (14 ≤ count1591 b) else (if i < 1606 then decide (1 ≤ count1605 b) else decide (2 ≤ count1605 b))) else (if i < 1609 then (if i < 1608 then decide (3 ≤ count1605 b) else decide (4 ≤ count1605 b)) else (if i < 1610 then decide (5 ≤ count1605 b) else decide (6 ≤ count1605 b)))))) else (if i < 1624 then (if i < 1617 then (if i < 1614 then (if i < 1612 then decide (7 ≤ count1605 b) else (if i < 1613 then decide (8 ≤ count1605 b) else decide (9 ≤ count1605 b))) else (if i < 1615 then decide (10 ≤ count1605 b) else (if i < 1616 then decide (11 ≤ count1605 b) else decide (12 ≤ count1605 b)))) else (if i < 1620 then (if i < 1618 then decide (13 ≤ count1605 b) else (if i < 1619 then decide (14 ≤ count1605 b) else decide (15 ≤ count1605 b))) else (if i < 1622 then (if i < 1621 then decide (16 ≤ count1605 b) else decide (1 ≤ count1621 b)) else (if i < 1623 then decide (2 ≤ count1621 b) else decide (3 ≤ count1621 b))))) else (if i < 1630 then (if i < 1627 then (if i < 1625 then decide (4 ≤ count1621 b) else (if i < 1626 then decide (5 ≤ count1621 b) else decide (6 ≤ count1621 b))) else (if i < 1628 then decide (7 ≤ count1621 b) else (if i < 1629 then decide (8 ≤ count1621 b) else decide (9 ≤ count1621 b)))) else (if i < 1633 then (if i < 1631 then decide (10 ≤ count1621 b) else (if i < 1632 then decide (11 ≤ count1621 b) else decide (12 ≤ count1621 b))) else (if i < 1635 then (if i < 1634 then decide (13 ≤ count1621 b) else decide (14 ≤ count1621 b)) else (if i < 1636 then decide (15 ≤ count1621 b) else decide (16 ≤ count1621 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (18 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (19 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (22 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (24 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (28 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (30 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (66 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (67 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (68 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (73 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (74 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (76 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (78 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (80 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (84 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (85 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (87 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (88 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (89 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (90 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (91 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (95 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (130 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (131 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (132 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (134 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (135 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (136 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (137 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (138 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (140 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (142 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (144 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (148 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (149 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (151 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (153 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (154 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (155 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (157 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (159 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (192 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (193 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (194 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (195 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (197 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (199 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (201 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (202 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (204 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (205 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (206 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (207 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (208 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (209 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (210 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (211 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (214 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (216 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (217 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (218 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (220 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (221 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (222 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (264 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (268 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (320 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (321 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (327 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (328 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (329 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (333 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (335 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (337 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (338 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (339 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (346 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (348 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (349 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (350 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (384 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (385 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (389 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (391 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (392 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (393 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (397 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (399 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (401 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (402 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (403 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (406 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (410 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (412 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (413 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (414 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (450 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (451 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (452 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (453 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (457 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (458 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (459 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (460 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (462 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (468 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (469 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (470 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (471 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (472 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (473 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (475 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (24 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (30 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (66 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (67 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (68 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (74 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (78 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (85 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (87 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (89 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (90 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (91 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (95 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (153 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (154 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (157 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (194 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (195 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (197 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (202 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (208 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (209 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (210 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (216 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (217 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (329 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (389 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (392 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (402 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (450 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (452 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (459 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (468 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (469 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (470 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (471 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (473 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (479 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (1 ≤ count231 (baseVal q)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (1 ≤ count233 (baseVal q)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (2 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (2 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
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
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
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
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value448 (q : Snake 81) : valuation q 448 = decide (2 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value450 (q : Snake 81) : valuation q 450 = decide (2 ≤ count449 (baseVal q)) := rfl
theorem value452 (q : Snake 81) : valuation q 452 = decide (2 ≤ count451 (baseVal q)) := rfl
theorem value1373 (q : Snake 81) : valuation q 1373 = decide (1 ≤ count1373 (baseVal q)) := rfl
theorem value1374 (q : Snake 81) : valuation q 1374 = decide (2 ≤ count1373 (baseVal q)) := rfl
theorem value1375 (q : Snake 81) : valuation q 1375 = decide (1 ≤ count1375 (baseVal q)) := rfl
theorem value1376 (q : Snake 81) : valuation q 1376 = decide (2 ≤ count1375 (baseVal q)) := rfl
theorem value1377 (q : Snake 81) : valuation q 1377 = decide (3 ≤ count1375 (baseVal q)) := rfl
theorem value1378 (q : Snake 81) : valuation q 1378 = decide (1 ≤ count1378 (baseVal q)) := rfl
theorem value1379 (q : Snake 81) : valuation q 1379 = decide (2 ≤ count1378 (baseVal q)) := rfl
theorem value1380 (q : Snake 81) : valuation q 1380 = decide (1 ≤ count1380 (baseVal q)) := rfl
theorem value1381 (q : Snake 81) : valuation q 1381 = decide (2 ≤ count1380 (baseVal q)) := rfl
theorem value1382 (q : Snake 81) : valuation q 1382 = decide (1 ≤ count1382 (baseVal q)) := rfl
theorem value1383 (q : Snake 81) : valuation q 1383 = decide (2 ≤ count1382 (baseVal q)) := rfl
theorem value1384 (q : Snake 81) : valuation q 1384 = decide (3 ≤ count1382 (baseVal q)) := rfl
theorem value1385 (q : Snake 81) : valuation q 1385 = decide (4 ≤ count1382 (baseVal q)) := rfl
theorem value1386 (q : Snake 81) : valuation q 1386 = decide (1 ≤ count1386 (baseVal q)) := rfl
theorem value1387 (q : Snake 81) : valuation q 1387 = decide (2 ≤ count1386 (baseVal q)) := rfl
theorem value1388 (q : Snake 81) : valuation q 1388 = decide (3 ≤ count1386 (baseVal q)) := rfl
theorem value1389 (q : Snake 81) : valuation q 1389 = decide (4 ≤ count1386 (baseVal q)) := rfl
theorem value1390 (q : Snake 81) : valuation q 1390 = decide (5 ≤ count1386 (baseVal q)) := rfl
theorem value1391 (q : Snake 81) : valuation q 1391 = decide (6 ≤ count1386 (baseVal q)) := rfl
theorem value1393 (q : Snake 81) : valuation q 1393 = decide (1 ≤ count1393 (baseVal q)) := rfl
theorem value1394 (q : Snake 81) : valuation q 1394 = decide (2 ≤ count1393 (baseVal q)) := rfl
theorem value1395 (q : Snake 81) : valuation q 1395 = decide (1 ≤ count1395 (baseVal q)) := rfl
theorem value1396 (q : Snake 81) : valuation q 1396 = decide (2 ≤ count1395 (baseVal q)) := rfl
theorem value1398 (q : Snake 81) : valuation q 1398 = decide (1 ≤ count1398 (baseVal q)) := rfl
theorem value1399 (q : Snake 81) : valuation q 1399 = decide (2 ≤ count1398 (baseVal q)) := rfl
theorem value1400 (q : Snake 81) : valuation q 1400 = decide (1 ≤ count1400 (baseVal q)) := rfl
theorem value1401 (q : Snake 81) : valuation q 1401 = decide (2 ≤ count1400 (baseVal q)) := rfl
theorem value1402 (q : Snake 81) : valuation q 1402 = decide (1 ≤ count1402 (baseVal q)) := rfl
theorem value1403 (q : Snake 81) : valuation q 1403 = decide (2 ≤ count1402 (baseVal q)) := rfl
theorem value1404 (q : Snake 81) : valuation q 1404 = decide (3 ≤ count1402 (baseVal q)) := rfl
theorem value1405 (q : Snake 81) : valuation q 1405 = decide (4 ≤ count1402 (baseVal q)) := rfl
theorem value1406 (q : Snake 81) : valuation q 1406 = decide (1 ≤ count1406 (baseVal q)) := rfl
theorem value1407 (q : Snake 81) : valuation q 1407 = decide (2 ≤ count1406 (baseVal q)) := rfl
theorem value1408 (q : Snake 81) : valuation q 1408 = decide (3 ≤ count1406 (baseVal q)) := rfl
theorem value1409 (q : Snake 81) : valuation q 1409 = decide (4 ≤ count1406 (baseVal q)) := rfl
theorem value1410 (q : Snake 81) : valuation q 1410 = decide (5 ≤ count1406 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (1 ≤ count1413 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (2 ≤ count1413 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (3 ≤ count1413 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (4 ≤ count1413 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (5 ≤ count1413 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (6 ≤ count1413 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (7 ≤ count1413 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (8 ≤ count1413 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (9 ≤ count1413 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (10 ≤ count1413 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (1 ≤ count1427 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (2 ≤ count1427 (baseVal q)) := rfl
theorem value1429 (q : Snake 81) : valuation q 1429 = decide (1 ≤ count1429 (baseVal q)) := rfl
theorem value1430 (q : Snake 81) : valuation q 1430 = decide (2 ≤ count1429 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (3 ≤ count1429 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (1 ≤ count1432 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (2 ≤ count1432 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (1 ≤ count1434 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (2 ≤ count1434 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (1 ≤ count1436 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (2 ≤ count1436 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (3 ≤ count1436 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (4 ≤ count1436 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (1 ≤ count1440 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (2 ≤ count1440 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (3 ≤ count1440 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (4 ≤ count1440 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (1 ≤ count1447 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (2 ≤ count1447 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (1 ≤ count1449 (baseVal q)) := rfl
theorem value1450 (q : Snake 81) : valuation q 1450 = decide (2 ≤ count1449 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (3 ≤ count1449 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (1 ≤ count1452 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (2 ≤ count1452 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (1 ≤ count1454 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (2 ≤ count1454 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (1 ≤ count1456 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (2 ≤ count1456 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (3 ≤ count1456 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (4 ≤ count1456 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (1 ≤ count1460 (baseVal q)) := rfl
theorem value1461 (q : Snake 81) : valuation q 1461 = decide (2 ≤ count1460 (baseVal q)) := rfl
theorem value1462 (q : Snake 81) : valuation q 1462 = decide (3 ≤ count1460 (baseVal q)) := rfl
theorem value1463 (q : Snake 81) : valuation q 1463 = decide (4 ≤ count1460 (baseVal q)) := rfl
theorem value1464 (q : Snake 81) : valuation q 1464 = decide (5 ≤ count1460 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (6 ≤ count1460 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (2 ≤ count1467 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (3 ≤ count1467 (baseVal q)) := rfl
theorem value1470 (q : Snake 81) : valuation q 1470 = decide (4 ≤ count1467 (baseVal q)) := rfl
theorem value1471 (q : Snake 81) : valuation q 1471 = decide (5 ≤ count1467 (baseVal q)) := rfl
theorem value1472 (q : Snake 81) : valuation q 1472 = decide (6 ≤ count1467 (baseVal q)) := rfl
theorem value1473 (q : Snake 81) : valuation q 1473 = decide (7 ≤ count1467 (baseVal q)) := rfl
theorem value1474 (q : Snake 81) : valuation q 1474 = decide (8 ≤ count1467 (baseVal q)) := rfl
theorem value1475 (q : Snake 81) : valuation q 1475 = decide (9 ≤ count1467 (baseVal q)) := rfl
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (5 ≤ count1481 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (6 ≤ count1481 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (7 ≤ count1481 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (8 ≤ count1481 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (9 ≤ count1481 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (10 ≤ count1481 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (11 ≤ count1481 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (12 ≤ count1481 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (13 ≤ count1481 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (1 ≤ count1497 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (2 ≤ count1497 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (1 ≤ count1499 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (2 ≤ count1499 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (3 ≤ count1499 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (1 ≤ count1502 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (2 ≤ count1502 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (1 ≤ count1504 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (1 ≤ count1506 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (2 ≤ count1506 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (3 ≤ count1506 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (1 ≤ count1510 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (2 ≤ count1510 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (3 ≤ count1510 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (4 ≤ count1510 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (5 ≤ count1510 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (6 ≤ count1510 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (1 ≤ count1517 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (2 ≤ count1517 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (1 ≤ count1519 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (2 ≤ count1519 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (1 ≤ count1522 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (2 ≤ count1522 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (1 ≤ count1524 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (2 ≤ count1524 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (1 ≤ count1526 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (2 ≤ count1526 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (1 ≤ count1530 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (2 ≤ count1530 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (3 ≤ count1530 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (4 ≤ count1530 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (1 ≤ count1537 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (2 ≤ count1537 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (3 ≤ count1537 (baseVal q)) := rfl
theorem value1540 (q : Snake 81) : valuation q 1540 = decide (4 ≤ count1537 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (5 ≤ count1537 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (6 ≤ count1537 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (7 ≤ count1537 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (8 ≤ count1537 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (9 ≤ count1537 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (2 ≤ count1551 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (1 ≤ count1553 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (2 ≤ count1553 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (3 ≤ count1553 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (1 ≤ count1556 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (2 ≤ count1556 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (1 ≤ count1558 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (2 ≤ count1558 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (1 ≤ count1560 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (2 ≤ count1560 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (3 ≤ count1560 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (3 ≤ count1564 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (4 ≤ count1564 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (1 ≤ count1571 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (2 ≤ count1571 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (1 ≤ count1573 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (2 ≤ count1573 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (3 ≤ count1573 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (1 ≤ count1576 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (1 ≤ count1578 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (2 ≤ count1578 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (1 ≤ count1580 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (2 ≤ count1580 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (1 ≤ count1584 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (2 ≤ count1584 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (3 ≤ count1584 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (1 ≤ count1591 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (2 ≤ count1591 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (3 ≤ count1591 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (4 ≤ count1591 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (5 ≤ count1591 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (3 ≤ count1605 (baseVal q)) := rfl
theorem value1608 (q : Snake 81) : valuation q 1608 = decide (4 ≤ count1605 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (5 ≤ count1605 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (6 ≤ count1605 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (7 ≤ count1605 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (8 ≤ count1605 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (9 ≤ count1605 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (10 ≤ count1605 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (11 ≤ count1605 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (16 ≤ count1621 (baseVal q)) := rfl
theorem meaningNeg113 (b : Nat → Bool) : literal (valuationOf b) (-113) = decide (1 ≤ countLit b [-113]) := by
  change literal b (-113) = decide (1 ≤ countLit b [-113])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-113) <;> decide
theorem meaningNeg111 (b : Nat → Bool) : literal (valuationOf b) (-111) = decide (1 ≤ countLit b [-111]) := by
  change literal b (-111) = decide (1 ≤ countLit b [-111])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-111) <;> decide
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
theorem meaningNeg76 (b : Nat → Bool) : literal (valuationOf b) (-76) = decide (1 ≤ countLit b [-76]) := by
  change literal b (-76) = decide (1 ≤ countLit b [-76])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-76) <;> decide
theorem meaningNeg72 (b : Nat → Bool) : literal (valuationOf b) (-72) = decide (1 ≤ countLit b [-72]) := by
  change literal b (-72) = decide (1 ≤ countLit b [-72])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-72) <;> decide
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
theorem meaningNeg60 (b : Nat → Bool) : literal (valuationOf b) (-60) = decide (1 ≤ countLit b [-60]) := by
  change literal b (-60) = decide (1 ≤ countLit b [-60])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-60) <;> decide
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
theorem meaningNeg47 (b : Nat → Bool) : literal (valuationOf b) (-47) = decide (1 ≤ countLit b [-47]) := by
  change literal b (-47) = decide (1 ≤ countLit b [-47])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-47) <;> decide
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
theorem meaningNeg34 (b : Nat → Bool) : literal (valuationOf b) (-34) = decide (1 ≤ countLit b [-34]) := by
  change literal b (-34) = decide (1 ≤ countLit b [-34])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-34) <;> decide
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
theorem meaning123 (b : Nat → Bool) : literal (valuationOf b) (123) = decide (1 ≤ countLit b [123]) := by
  change literal b (123) = decide (1 ≤ countLit b [123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (123) <;> decide
theorem meaning127 (b : Nat → Bool) : literal (valuationOf b) (127) = decide (1 ≤ countLit b [127]) := by
  change literal b (127) = decide (1 ≤ countLit b [127])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (127) <;> decide
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
theorem meaning133 (b : Nat → Bool) : literal (valuationOf b) (133) = decide (1 ≤ countLit b [133]) := by
  change literal b (133) = decide (1 ≤ countLit b [133])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (133) <;> decide
theorem meaning136 (b : Nat → Bool) : literal (valuationOf b) (136) = decide (1 ≤ countLit b [136]) := by
  change literal b (136) = decide (1 ≤ countLit b [136])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (136) <;> decide
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
theorem meaning141 (b : Nat → Bool) : literal (valuationOf b) (141) = decide (1 ≤ countLit b [141]) := by
  change literal b (141) = decide (1 ≤ countLit b [141])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (141) <;> decide
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
theorem meaning149 (b : Nat → Bool) : literal (valuationOf b) (149) = decide (1 ≤ countLit b [149]) := by
  change literal b (149) = decide (1 ≤ countLit b [149])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (149) <;> decide
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
theorem meaning156 (b : Nat → Bool) : literal (valuationOf b) (156) = decide (1 ≤ countLit b [156]) := by
  change literal b (156) = decide (1 ≤ countLit b [156])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (156) <;> decide
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
theorem meaning162 (b : Nat → Bool) : literal (valuationOf b) (162) = decide (1 ≤ countLit b [162]) := by
  change literal b (162) = decide (1 ≤ countLit b [162])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (162) <;> decide
theorem meaning163 (b : Nat → Bool) : literal (valuationOf b) (163) = decide (1 ≤ countLit b [163]) := by
  change literal b (163) = decide (1 ≤ countLit b [163])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (163) <;> decide
theorem meaning164 (b : Nat → Bool) : literal (valuationOf b) (164) = decide (1 ≤ countLit b [164]) := by
  change literal b (164) = decide (1 ≤ countLit b [164])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (164) <;> decide
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
theorem meaning170 (b : Nat → Bool) : literal (valuationOf b) (170) = decide (1 ≤ countLit b [170]) := by
  change literal b (170) = decide (1 ≤ countLit b [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (170) <;> decide
theorem meaning173 (b : Nat → Bool) : literal (valuationOf b) (173) = decide (1 ≤ countLit b [173]) := by
  change literal b (173) = decide (1 ≤ countLit b [173])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (173) <;> decide
theorem meaning177 (b : Nat → Bool) : literal (valuationOf b) (177) = decide (1 ≤ countLit b [177]) := by
  change literal b (177) = decide (1 ≤ countLit b [177])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (177) <;> decide
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
theorem meaning189 (b : Nat → Bool) : literal (valuationOf b) (189) = decide (1 ≤ countLit b [189]) := by
  change literal b (189) = decide (1 ≤ countLit b [189])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (189) <;> decide
theorem meaning193 (b : Nat → Bool) : literal (valuationOf b) (193) = decide (1 ≤ countLit b [193]) := by
  change literal b (193) = decide (1 ≤ countLit b [193])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (193) <;> decide
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
theorem meaning210 (b : Nat → Bool) : literal (valuationOf b) (210) = decide (1 ≤ countLit b [210]) := by
  change literal b (210) = decide (1 ≤ countLit b [210])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (210) <;> decide
theorem meaning211 (b : Nat → Bool) : literal (valuationOf b) (211) = decide (1 ≤ countLit b [211]) := by
  change literal b (211) = decide (1 ≤ countLit b [211])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (211) <;> decide
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
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
theorem meaning220 (b : Nat → Bool) : literal (valuationOf b) (220) = decide (1 ≤ countLit b [220]) := by
  change literal b (220) = decide (1 ≤ countLit b [220])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (220) <;> decide
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) (222) = decide (1 ≤ countLit b [222]) := by
  change literal b (222) = decide (1 ≤ countLit b [222])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (222) <;> decide
theorem meaning223 (b : Nat → Bool) : literal (valuationOf b) (223) = decide (1 ≤ countLit b [223]) := by
  change literal b (223) = decide (1 ≤ countLit b [223])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (223) <;> decide
theorem meaning226 (b : Nat → Bool) : literal (valuationOf b) (226) = decide (1 ≤ countLit b [226]) := by
  change literal b (226) = decide (1 ≤ countLit b [226])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (226) <;> decide
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) (228) = decide (1 ≤ countLit b [228]) := by
  change literal b (228) = decide (1 ≤ countLit b [228])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (228) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) 231 = decide (1 ≤ count231 b) := rfl
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) 233 = decide (1 ≤ count233 b) := rfl
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning236 (b : Nat → Bool) : literal (valuationOf b) 236 = decide (2 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) 238 = decide (2 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
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
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
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
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning380 (b : Nat → Bool) : literal (valuationOf b) 380 = decide (2 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning448 (b : Nat → Bool) : literal (valuationOf b) 448 = decide (2 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning450 (b : Nat → Bool) : literal (valuationOf b) 450 = decide (2 ≤ count449 b) := rfl
theorem meaning452 (b : Nat → Bool) : literal (valuationOf b) 452 = decide (2 ≤ count451 b) := rfl
theorem meaning1373 (b : Nat → Bool) : literal (valuationOf b) 1373 = decide (1 ≤ count1373 b) := rfl
theorem meaning1374 (b : Nat → Bool) : literal (valuationOf b) 1374 = decide (2 ≤ count1373 b) := rfl
theorem meaning1375 (b : Nat → Bool) : literal (valuationOf b) 1375 = decide (1 ≤ count1375 b) := rfl
theorem meaning1376 (b : Nat → Bool) : literal (valuationOf b) 1376 = decide (2 ≤ count1375 b) := rfl
theorem meaning1377 (b : Nat → Bool) : literal (valuationOf b) 1377 = decide (3 ≤ count1375 b) := rfl
theorem meaning1378 (b : Nat → Bool) : literal (valuationOf b) 1378 = decide (1 ≤ count1378 b) := rfl
theorem meaning1379 (b : Nat → Bool) : literal (valuationOf b) 1379 = decide (2 ≤ count1378 b) := rfl
theorem meaning1380 (b : Nat → Bool) : literal (valuationOf b) 1380 = decide (1 ≤ count1380 b) := rfl
theorem meaning1381 (b : Nat → Bool) : literal (valuationOf b) 1381 = decide (2 ≤ count1380 b) := rfl
theorem meaning1382 (b : Nat → Bool) : literal (valuationOf b) 1382 = decide (1 ≤ count1382 b) := rfl
theorem meaning1383 (b : Nat → Bool) : literal (valuationOf b) 1383 = decide (2 ≤ count1382 b) := rfl
theorem meaning1384 (b : Nat → Bool) : literal (valuationOf b) 1384 = decide (3 ≤ count1382 b) := rfl
theorem meaning1385 (b : Nat → Bool) : literal (valuationOf b) 1385 = decide (4 ≤ count1382 b) := rfl
theorem meaning1386 (b : Nat → Bool) : literal (valuationOf b) 1386 = decide (1 ≤ count1386 b) := rfl
theorem meaning1387 (b : Nat → Bool) : literal (valuationOf b) 1387 = decide (2 ≤ count1386 b) := rfl
theorem meaning1388 (b : Nat → Bool) : literal (valuationOf b) 1388 = decide (3 ≤ count1386 b) := rfl
theorem meaning1389 (b : Nat → Bool) : literal (valuationOf b) 1389 = decide (4 ≤ count1386 b) := rfl
theorem meaning1390 (b : Nat → Bool) : literal (valuationOf b) 1390 = decide (5 ≤ count1386 b) := rfl
theorem meaning1391 (b : Nat → Bool) : literal (valuationOf b) 1391 = decide (6 ≤ count1386 b) := rfl
theorem meaning1393 (b : Nat → Bool) : literal (valuationOf b) 1393 = decide (1 ≤ count1393 b) := rfl
theorem meaning1394 (b : Nat → Bool) : literal (valuationOf b) 1394 = decide (2 ≤ count1393 b) := rfl
theorem meaning1395 (b : Nat → Bool) : literal (valuationOf b) 1395 = decide (1 ≤ count1395 b) := rfl
theorem meaning1396 (b : Nat → Bool) : literal (valuationOf b) 1396 = decide (2 ≤ count1395 b) := rfl
theorem meaning1398 (b : Nat → Bool) : literal (valuationOf b) 1398 = decide (1 ≤ count1398 b) := rfl
theorem meaning1399 (b : Nat → Bool) : literal (valuationOf b) 1399 = decide (2 ≤ count1398 b) := rfl
theorem meaning1400 (b : Nat → Bool) : literal (valuationOf b) 1400 = decide (1 ≤ count1400 b) := rfl
theorem meaning1401 (b : Nat → Bool) : literal (valuationOf b) 1401 = decide (2 ≤ count1400 b) := rfl
theorem meaning1402 (b : Nat → Bool) : literal (valuationOf b) 1402 = decide (1 ≤ count1402 b) := rfl
theorem meaning1403 (b : Nat → Bool) : literal (valuationOf b) 1403 = decide (2 ≤ count1402 b) := rfl
theorem meaning1404 (b : Nat → Bool) : literal (valuationOf b) 1404 = decide (3 ≤ count1402 b) := rfl
theorem meaning1405 (b : Nat → Bool) : literal (valuationOf b) 1405 = decide (4 ≤ count1402 b) := rfl
theorem meaning1406 (b : Nat → Bool) : literal (valuationOf b) 1406 = decide (1 ≤ count1406 b) := rfl
theorem meaning1407 (b : Nat → Bool) : literal (valuationOf b) 1407 = decide (2 ≤ count1406 b) := rfl
theorem meaning1408 (b : Nat → Bool) : literal (valuationOf b) 1408 = decide (3 ≤ count1406 b) := rfl
theorem meaning1409 (b : Nat → Bool) : literal (valuationOf b) 1409 = decide (4 ≤ count1406 b) := rfl
theorem meaning1410 (b : Nat → Bool) : literal (valuationOf b) 1410 = decide (5 ≤ count1406 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (1 ≤ count1413 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (2 ≤ count1413 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (3 ≤ count1413 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (4 ≤ count1413 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (5 ≤ count1413 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (6 ≤ count1413 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (7 ≤ count1413 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (8 ≤ count1413 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (9 ≤ count1413 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (10 ≤ count1413 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (1 ≤ count1427 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (2 ≤ count1427 b) := rfl
theorem meaning1429 (b : Nat → Bool) : literal (valuationOf b) 1429 = decide (1 ≤ count1429 b) := rfl
theorem meaning1430 (b : Nat → Bool) : literal (valuationOf b) 1430 = decide (2 ≤ count1429 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (3 ≤ count1429 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (1 ≤ count1432 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (2 ≤ count1432 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (1 ≤ count1434 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (2 ≤ count1434 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (1 ≤ count1436 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (2 ≤ count1436 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (3 ≤ count1436 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (4 ≤ count1436 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (1 ≤ count1440 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (2 ≤ count1440 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (3 ≤ count1440 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (4 ≤ count1440 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (1 ≤ count1447 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (2 ≤ count1447 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (1 ≤ count1449 b) := rfl
theorem meaning1450 (b : Nat → Bool) : literal (valuationOf b) 1450 = decide (2 ≤ count1449 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (3 ≤ count1449 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (1 ≤ count1452 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (2 ≤ count1452 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (1 ≤ count1454 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (2 ≤ count1454 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (1 ≤ count1456 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (2 ≤ count1456 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (3 ≤ count1456 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (4 ≤ count1456 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (1 ≤ count1460 b) := rfl
theorem meaning1461 (b : Nat → Bool) : literal (valuationOf b) 1461 = decide (2 ≤ count1460 b) := rfl
theorem meaning1462 (b : Nat → Bool) : literal (valuationOf b) 1462 = decide (3 ≤ count1460 b) := rfl
theorem meaning1463 (b : Nat → Bool) : literal (valuationOf b) 1463 = decide (4 ≤ count1460 b) := rfl
theorem meaning1464 (b : Nat → Bool) : literal (valuationOf b) 1464 = decide (5 ≤ count1460 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (6 ≤ count1460 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (2 ≤ count1467 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (3 ≤ count1467 b) := rfl
theorem meaning1470 (b : Nat → Bool) : literal (valuationOf b) 1470 = decide (4 ≤ count1467 b) := rfl
theorem meaning1471 (b : Nat → Bool) : literal (valuationOf b) 1471 = decide (5 ≤ count1467 b) := rfl
theorem meaning1472 (b : Nat → Bool) : literal (valuationOf b) 1472 = decide (6 ≤ count1467 b) := rfl
theorem meaning1473 (b : Nat → Bool) : literal (valuationOf b) 1473 = decide (7 ≤ count1467 b) := rfl
theorem meaning1474 (b : Nat → Bool) : literal (valuationOf b) 1474 = decide (8 ≤ count1467 b) := rfl
theorem meaning1475 (b : Nat → Bool) : literal (valuationOf b) 1475 = decide (9 ≤ count1467 b) := rfl
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (5 ≤ count1481 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (6 ≤ count1481 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (7 ≤ count1481 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (8 ≤ count1481 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (9 ≤ count1481 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (10 ≤ count1481 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (11 ≤ count1481 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (12 ≤ count1481 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (13 ≤ count1481 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (1 ≤ count1497 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (2 ≤ count1497 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (1 ≤ count1499 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (2 ≤ count1499 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (3 ≤ count1499 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (1 ≤ count1502 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (2 ≤ count1502 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (1 ≤ count1504 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (1 ≤ count1506 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (2 ≤ count1506 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (3 ≤ count1506 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (1 ≤ count1510 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (2 ≤ count1510 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (3 ≤ count1510 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (4 ≤ count1510 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (5 ≤ count1510 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (6 ≤ count1510 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (1 ≤ count1517 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (2 ≤ count1517 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (1 ≤ count1519 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (2 ≤ count1519 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (1 ≤ count1522 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (2 ≤ count1522 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (1 ≤ count1524 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (2 ≤ count1524 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (1 ≤ count1526 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (2 ≤ count1526 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (1 ≤ count1530 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (2 ≤ count1530 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (3 ≤ count1530 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (4 ≤ count1530 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (1 ≤ count1537 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (2 ≤ count1537 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (3 ≤ count1537 b) := rfl
theorem meaning1540 (b : Nat → Bool) : literal (valuationOf b) 1540 = decide (4 ≤ count1537 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (5 ≤ count1537 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (6 ≤ count1537 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (7 ≤ count1537 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (8 ≤ count1537 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (9 ≤ count1537 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (2 ≤ count1551 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (1 ≤ count1553 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (2 ≤ count1553 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (3 ≤ count1553 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (1 ≤ count1556 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (2 ≤ count1556 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (1 ≤ count1558 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (2 ≤ count1558 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (1 ≤ count1560 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (2 ≤ count1560 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (3 ≤ count1560 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (3 ≤ count1564 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (4 ≤ count1564 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (1 ≤ count1571 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (2 ≤ count1571 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (1 ≤ count1573 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (2 ≤ count1573 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (3 ≤ count1573 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (1 ≤ count1576 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (1 ≤ count1578 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (2 ≤ count1578 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (1 ≤ count1580 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (2 ≤ count1580 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (1 ≤ count1584 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (2 ≤ count1584 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (3 ≤ count1584 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (1 ≤ count1591 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (2 ≤ count1591 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (3 ≤ count1591 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (4 ≤ count1591 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (5 ≤ count1591 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (3 ≤ count1605 b) := rfl
theorem meaning1608 (b : Nat → Bool) : literal (valuationOf b) 1608 = decide (4 ≤ count1605 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (5 ≤ count1605 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (6 ≤ count1605 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (7 ≤ count1605 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (8 ≤ count1605 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (9 ≤ count1605 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (10 ≤ count1605 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (11 ≤ count1605 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (16 ≤ count1621 b) := rfl
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
end Snake9.Regrowth.E112168
