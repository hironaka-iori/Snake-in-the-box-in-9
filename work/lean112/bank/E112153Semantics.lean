import E112153Data
namespace Snake9.Regrowth.E112153
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 124 then (if i < 62 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (2 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (5 : Vertex)) else decide (InPath q (6 : Vertex))) else (if i < 6 then decide (InPath q (12 : Vertex)) else decide (InPath q (14 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (28 : Vertex)) else decide (InPath q (65 : Vertex))) else (if i < 10 then decide (InPath q (69 : Vertex)) else decide (InPath q (76 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (77 : Vertex)) else decide (InPath q (129 : Vertex))) else (if i < 14 then decide (InPath q (131 : Vertex)) else decide (InPath q (132 : Vertex)))))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then decide (InPath q (133 : Vertex)) else decide (InPath q (134 : Vertex))) else (if i < 18 then decide (InPath q (138 : Vertex)) else decide (InPath q (139 : Vertex)))) else (if i < 21 then (if i < 20 then decide (InPath q (140 : Vertex)) else decide (InPath q (141 : Vertex))) else (if i < 22 then decide (InPath q (144 : Vertex)) else decide (InPath q (148 : Vertex))))) else (if i < 27 then (if i < 25 then (if i < 24 then decide (InPath q (149 : Vertex)) else decide (InPath q (150 : Vertex))) else (if i < 26 then decide (InPath q (151 : Vertex)) else decide (InPath q (152 : Vertex)))) else (if i < 29 then (if i < 28 then decide (InPath q (154 : Vertex)) else decide (InPath q (155 : Vertex))) else (if i < 30 then decide (InPath q (192 : Vertex)) else decide (InPath q (194 : Vertex))))))) else (if i < 46 then (if i < 38 then (if i < 34 then (if i < 32 then decide (InPath q (196 : Vertex)) else (if i < 33 then decide (InPath q (198 : Vertex)) else decide (InPath q (199 : Vertex)))) else (if i < 36 then (if i < 35 then decide (InPath q (200 : Vertex)) else decide (InPath q (201 : Vertex))) else (if i < 37 then decide (InPath q (206 : Vertex)) else decide (InPath q (207 : Vertex))))) else (if i < 42 then (if i < 40 then (if i < 39 then decide (InPath q (209 : Vertex)) else decide (InPath q (210 : Vertex))) else (if i < 41 then decide (InPath q (211 : Vertex)) else decide (InPath q (213 : Vertex)))) else (if i < 44 then (if i < 43 then decide (InPath q (217 : Vertex)) else decide (InPath q (219 : Vertex))) else (if i < 45 then decide (InPath q (220 : Vertex)) else decide (InPath q (221 : Vertex)))))) else (if i < 54 then (if i < 50 then (if i < 48 then (if i < 47 then decide (InPath q (222 : Vertex)) else decide (InPath q (257 : Vertex))) else (if i < 49 then decide (InPath q (259 : Vertex)) else decide (InPath q (261 : Vertex)))) else (if i < 52 then (if i < 51 then decide (InPath q (262 : Vertex)) else decide (InPath q (263 : Vertex))) else (if i < 53 then decide (InPath q (264 : Vertex)) else decide (InPath q (267 : Vertex))))) else (if i < 58 then (if i < 56 then (if i < 55 then decide (InPath q (268 : Vertex)) else decide (InPath q (269 : Vertex))) else (if i < 57 then decide (InPath q (271 : Vertex)) else decide (InPath q (272 : Vertex)))) else (if i < 60 then (if i < 59 then decide (InPath q (274 : Vertex)) else decide (InPath q (276 : Vertex))) else (if i < 61 then decide (InPath q (277 : Vertex)) else decide (InPath q (278 : Vertex)))))))) else (if i < 93 then (if i < 77 then (if i < 69 then (if i < 65 then (if i < 63 then decide (InPath q (280 : Vertex)) else (if i < 64 then decide (InPath q (282 : Vertex)) else decide (InPath q (283 : Vertex)))) else (if i < 67 then (if i < 66 then decide (InPath q (320 : Vertex)) else decide (InPath q (322 : Vertex))) else (if i < 68 then decide (InPath q (324 : Vertex)) else decide (InPath q (326 : Vertex))))) else (if i < 73 then (if i < 71 then (if i < 70 then decide (InPath q (327 : Vertex)) else decide (InPath q (328 : Vertex))) else (if i < 72 then decide (InPath q (329 : Vertex)) else decide (InPath q (334 : Vertex)))) else (if i < 75 then (if i < 74 then decide (InPath q (335 : Vertex)) else decide (InPath q (337 : Vertex))) else (if i < 76 then decide (InPath q (338 : Vertex)) else decide (InPath q (339 : Vertex)))))) else (if i < 85 then (if i < 81 then (if i < 79 then (if i < 78 then decide (InPath q (341 : Vertex)) else decide (InPath q (345 : Vertex))) else (if i < 80 then decide (InPath q (348 : Vertex)) else decide (InPath q (349 : Vertex)))) else (if i < 83 then (if i < 82 then decide (InPath q (350 : Vertex)) else decide (InPath q (384 : Vertex))) else (if i < 84 then decide (InPath q (386 : Vertex)) else decide (InPath q (388 : Vertex))))) else (if i < 89 then (if i < 87 then (if i < 86 then decide (InPath q (391 : Vertex)) else decide (InPath q (393 : Vertex))) else (if i < 88 then decide (InPath q (394 : Vertex)) else decide (InPath q (396 : Vertex)))) else (if i < 91 then (if i < 90 then decide (InPath q (397 : Vertex)) else decide (InPath q (398 : Vertex))) else (if i < 92 then decide (InPath q (399 : Vertex)) else decide (InPath q (400 : Vertex))))))) else (if i < 108 then (if i < 100 then (if i < 96 then (if i < 94 then decide (InPath q (401 : Vertex)) else (if i < 95 then decide (InPath q (402 : Vertex)) else decide (InPath q (403 : Vertex)))) else (if i < 98 then (if i < 97 then decide (InPath q (407 : Vertex)) else decide (InPath q (409 : Vertex))) else (if i < 99 then decide (InPath q (412 : Vertex)) else decide (InPath q (413 : Vertex))))) else (if i < 104 then (if i < 102 then (if i < 101 then decide (InPath q (414 : Vertex)) else decide (InPath q (415 : Vertex))) else (if i < 103 then decide (InPath q (448 : Vertex)) else decide (InPath q (449 : Vertex)))) else (if i < 106 then (if i < 105 then decide (InPath q (451 : Vertex)) else decide (InPath q (452 : Vertex))) else (if i < 107 then decide (InPath q (453 : Vertex)) else decide (InPath q (455 : Vertex)))))) else (if i < 116 then (if i < 112 then (if i < 110 then (if i < 109 then decide (InPath q (456 : Vertex)) else decide (InPath q (457 : Vertex))) else (if i < 111 then decide (InPath q (458 : Vertex)) else decide (InPath q (459 : Vertex)))) else (if i < 114 then (if i < 113 then decide (InPath q (461 : Vertex)) else decide (InPath q (462 : Vertex))) else (if i < 115 then decide (InPath q (463 : Vertex)) else decide (InPath q (464 : Vertex))))) else (if i < 120 then (if i < 118 then (if i < 117 then decide (InPath q (468 : Vertex)) else decide (InPath q (469 : Vertex))) else (if i < 119 then decide (InPath q (470 : Vertex)) else decide (InPath q (471 : Vertex)))) else (if i < 122 then (if i < 121 then decide (InPath q (472 : Vertex)) else decide (InPath q (474 : Vertex))) else (if i < 123 then decide (InPath q (475 : Vertex)) else decide (InPath q (476 : Vertex))))))))) else (if i < 186 then (if i < 155 then (if i < 139 then (if i < 131 then (if i < 127 then (if i < 125 then decide (InPath q (478 : Vertex)) else (if i < 126 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (2 : Vertex)))) else (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (5 : Vertex)) else decide (BallClauseLogic.Endpoint q (6 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (12 : Vertex)) else decide (BallClauseLogic.Endpoint q (14 : Vertex))))) else (if i < 135 then (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (65 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (69 : Vertex)) else decide (BallClauseLogic.Endpoint q (76 : Vertex)))) else (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (77 : Vertex)) else decide (BallClauseLogic.Endpoint q (129 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex)))))) else (if i < 147 then (if i < 143 then (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (138 : Vertex)) else decide (BallClauseLogic.Endpoint q (139 : Vertex)))) else (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (141 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))))) else (if i < 151 then (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else decide (BallClauseLogic.Endpoint q (150 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (152 : Vertex)))) else (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else decide (BallClauseLogic.Endpoint q (155 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (194 : Vertex))))))) else (if i < 170 then (if i < 162 then (if i < 158 then (if i < 156 then decide (BallClauseLogic.Endpoint q (196 : Vertex)) else (if i < 157 then decide (BallClauseLogic.Endpoint q (198 : Vertex)) else decide (BallClauseLogic.Endpoint q (199 : Vertex)))) else (if i < 160 then (if i < 159 then decide (BallClauseLogic.Endpoint q (200 : Vertex)) else decide (BallClauseLogic.Endpoint q (201 : Vertex))) else (if i < 161 then decide (BallClauseLogic.Endpoint q (206 : Vertex)) else decide (BallClauseLogic.Endpoint q (207 : Vertex))))) else (if i < 166 then (if i < 164 then (if i < 163 then decide (BallClauseLogic.Endpoint q (209 : Vertex)) else decide (BallClauseLogic.Endpoint q (210 : Vertex))) else (if i < 165 then decide (BallClauseLogic.Endpoint q (211 : Vertex)) else decide (BallClauseLogic.Endpoint q (213 : Vertex)))) else (if i < 168 then (if i < 167 then decide (BallClauseLogic.Endpoint q (217 : Vertex)) else decide (BallClauseLogic.Endpoint q (219 : Vertex))) else (if i < 169 then decide (BallClauseLogic.Endpoint q (220 : Vertex)) else decide (BallClauseLogic.Endpoint q (221 : Vertex)))))) else (if i < 178 then (if i < 174 then (if i < 172 then (if i < 171 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else decide (BallClauseLogic.Endpoint q (257 : Vertex))) else (if i < 173 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex)))) else (if i < 176 then (if i < 175 then decide (BallClauseLogic.Endpoint q (262 : Vertex)) else decide (BallClauseLogic.Endpoint q (263 : Vertex))) else (if i < 177 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex))))) else (if i < 182 then (if i < 180 then (if i < 179 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (269 : Vertex))) else (if i < 181 then decide (BallClauseLogic.Endpoint q (271 : Vertex)) else decide (BallClauseLogic.Endpoint q (272 : Vertex)))) else (if i < 184 then (if i < 183 then decide (BallClauseLogic.Endpoint q (274 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex))) else (if i < 185 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else decide (BallClauseLogic.Endpoint q (278 : Vertex)))))))) else (if i < 217 then (if i < 201 then (if i < 193 then (if i < 189 then (if i < 187 then decide (BallClauseLogic.Endpoint q (280 : Vertex)) else (if i < 188 then decide (BallClauseLogic.Endpoint q (282 : Vertex)) else decide (BallClauseLogic.Endpoint q (283 : Vertex)))) else (if i < 191 then (if i < 190 then decide (BallClauseLogic.Endpoint q (320 : Vertex)) else decide (BallClauseLogic.Endpoint q (322 : Vertex))) else (if i < 192 then decide (BallClauseLogic.Endpoint q (324 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex))))) else (if i < 197 then (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (328 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else decide (BallClauseLogic.Endpoint q (334 : Vertex)))) else (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (335 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (338 : Vertex)) else decide (BallClauseLogic.Endpoint q (339 : Vertex)))))) else (if i < 209 then (if i < 205 then (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (341 : Vertex)) else decide (BallClauseLogic.Endpoint q (345 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else decide (BallClauseLogic.Endpoint q (349 : Vertex)))) else (if i < 207 then (if i < 206 then decide (BallClauseLogic.Endpoint q (350 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 208 then decide (BallClauseLogic.Endpoint q (386 : Vertex)) else decide (BallClauseLogic.Endpoint q (388 : Vertex))))) else (if i < 213 then (if i < 211 then (if i < 210 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (393 : Vertex))) else (if i < 212 then decide (BallClauseLogic.Endpoint q (394 : Vertex)) else decide (BallClauseLogic.Endpoint q (396 : Vertex)))) else (if i < 215 then (if i < 214 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else decide (BallClauseLogic.Endpoint q (398 : Vertex))) else (if i < 216 then decide (BallClauseLogic.Endpoint q (399 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex))))))) else (if i < 233 then (if i < 225 then (if i < 221 then (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (402 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (403 : Vertex)) else decide (BallClauseLogic.Endpoint q (407 : Vertex)))) else (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (409 : Vertex)) else decide (BallClauseLogic.Endpoint q (412 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex))))) else (if i < 229 then (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (415 : Vertex)) else decide (BallClauseLogic.Endpoint q (448 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (449 : Vertex)) else decide (BallClauseLogic.Endpoint q (451 : Vertex)))) else (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (452 : Vertex)) else decide (BallClauseLogic.Endpoint q (453 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (455 : Vertex)) else decide (BallClauseLogic.Endpoint q (456 : Vertex)))))) else (if i < 241 then (if i < 237 then (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (457 : Vertex)) else decide (BallClauseLogic.Endpoint q (458 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (459 : Vertex)) else decide (BallClauseLogic.Endpoint q (461 : Vertex)))) else (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (462 : Vertex)) else decide (BallClauseLogic.Endpoint q (463 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (464 : Vertex)) else decide (BallClauseLogic.Endpoint q (468 : Vertex))))) else (if i < 245 then (if i < 243 then (if i < 242 then decide (BallClauseLogic.Endpoint q (469 : Vertex)) else decide (BallClauseLogic.Endpoint q (470 : Vertex))) else (if i < 244 then decide (BallClauseLogic.Endpoint q (471 : Vertex)) else decide (BallClauseLogic.Endpoint q (472 : Vertex)))) else (if i < 247 then (if i < 246 then decide (BallClauseLogic.Endpoint q (474 : Vertex)) else decide (BallClauseLogic.Endpoint q (475 : Vertex))) else (if i < 248 then decide (BallClauseLogic.Endpoint q (476 : Vertex)) else decide (BallClauseLogic.Endpoint q (478 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count253 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count265 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count271 (b : Nat → Bool) : Nat := countLit b [137, 138, 139, 140]
def count273 (b : Nat → Bool) : Nat := countLit b [133, 134, 135, 136, 137, 138, 139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140]
def count277 (b : Nat → Bool) : Nat := countLit b [142, 143]
def count279 (b : Nat → Bool) : Nat := countLit b [141, 142, 143]
def count281 (b : Nat → Bool) : Nat := countLit b [144, 145]
def count283 (b : Nat → Bool) : Nat := countLit b [146, 147]
def count285 (b : Nat → Bool) : Nat := countLit b [144, 145, 146, 147]
def count287 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147]
def count289 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count291 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count293 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151]
def count295 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count297 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count299 (b : Nat → Bool) : Nat := countLit b [152, 153, 154, 155]
def count301 (b : Nat → Bool) : Nat := countLit b [148, 149, 150, 151, 152, 153, 154, 155]
def count303 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count313 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count315 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162]
def count317 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count321 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count323 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count327 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count331 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166, 167, 168, 169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count343 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count347 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count351 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count353 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count357 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count359 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186]
def count361 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182, 183, 184, 185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]
def count367 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186]
def count369 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count371 (b : Nat → Bool) : Nat := countLit b [187, 188, 189]
def count373 (b : Nat → Bool) : Nat := countLit b [190, 191]
def count375 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count377 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193]
def count379 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193]
def count381 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count383 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count385 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count389 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count391 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197, 198, 199, 200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208, 209]
def count411 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count419 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count421 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217]
def count423 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213, 214, 215, 216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
def count427 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217]
def count429 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [218, 219, 220]
def count433 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224]
def count441 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count443 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count451 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228, 229, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232]
def count457 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236]
def count463 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236, 237, 238, 239, 240]
def count471 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count473 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count475 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244]
def count477 (b : Nat → Bool) : Nat := countLit b [245, 246]
def count479 (b : Nat → Bool) : Nat := countLit b [247, 248]
def count481 (b : Nat → Bool) : Nat := countLit b [245, 246, 247, 248]
def count483 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244, 245, 246, 247, 248]
def count485 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count487 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count489 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count491 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248]
def count493 (b : Nat → Bool) : Nat := countLit b [3, 4]
def count495 (b : Nat → Bool) : Nat := countLit b [1, 3, 4]
def count498 (b : Nat → Bool) : Nat := countLit b [5, 8]
def count500 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count502 (b : Nat → Bool) : Nat := countLit b [5, 8, 11, 12]
def count506 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 8, 11, 12]
def count513 (b : Nat → Bool) : Nat := countLit b [14, 18]
def count515 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count517 (b : Nat → Bool) : Nat := countLit b [14, 18, 20, 21]
def count521 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count523 (b : Nat → Bool) : Nat := countLit b [27, 29]
def count525 (b : Nat → Bool) : Nat := countLit b [23, 24, 27, 29]
def count529 (b : Nat → Bool) : Nat := countLit b [14, 18, 20, 21, 23, 24, 27, 29]
def count537 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 8, 11, 12, 14, 18, 20, 21, 23, 24, 27, 29]
def count552 (b : Nat → Bool) : Nat := countLit b [32, 35]
def count554 (b : Nat → Bool) : Nat := countLit b [37, 38]
def count556 (b : Nat → Bool) : Nat := countLit b [32, 35, 37, 38]
def count560 (b : Nat → Bool) : Nat := countLit b [39, 43]
def count562 (b : Nat → Bool) : Nat := countLit b [45, 46]
def count564 (b : Nat → Bool) : Nat := countLit b [39, 43, 45, 46]
def count568 (b : Nat → Bool) : Nat := countLit b [32, 35, 37, 38, 39, 43, 45, 46]
def count576 (b : Nat → Bool) : Nat := countLit b [47, 51]
def count578 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count580 (b : Nat → Bool) : Nat := countLit b [47, 51, 52, 53]
def count584 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count586 (b : Nat → Bool) : Nat := countLit b [60, 61]
def count588 (b : Nat → Bool) : Nat := countLit b [55, 57, 60, 61]
def count592 (b : Nat → Bool) : Nat := countLit b [47, 51, 52, 53, 55, 57, 60, 61]
def count600 (b : Nat → Bool) : Nat := countLit b [32, 35, 37, 38, 39, 43, 45, 46, 47, 51, 52, 53, 55, 57, 60, 61]
def count616 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 8, 11, 12, 14, 18, 20, 21, 23, 24, 27, 29, 32, 35, 37, 38, 39, 43, 45, 46, 47, 51, 52, 53, 55, 57, 60, 61]
def count647 (b : Nat → Bool) : Nat := countLit b [65, 68]
def count649 (b : Nat → Bool) : Nat := countLit b [63, 65, 68]
def count652 (b : Nat → Bool) : Nat := countLit b [71, 73]
def count654 (b : Nat → Bool) : Nat := countLit b [74, 75]
def count656 (b : Nat → Bool) : Nat := countLit b [71, 73, 74, 75]
def count660 (b : Nat → Bool) : Nat := countLit b [63, 65, 68, 71, 73, 74, 75]
def count667 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count669 (b : Nat → Bool) : Nat := countLit b [82, 86]
def count671 (b : Nat → Bool) : Nat := countLit b [80, 81, 82, 86]
def count675 (b : Nat → Bool) : Nat := countLit b [87, 88]
def count677 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count679 (b : Nat → Bool) : Nat := countLit b [87, 88, 91, 93]
def count683 (b : Nat → Bool) : Nat := countLit b [80, 81, 82, 86, 87, 88, 91, 93]
def count691 (b : Nat → Bool) : Nat := countLit b [63, 65, 68, 71, 73, 74, 75, 80, 81, 82, 86, 87, 88, 91, 93]
def count706 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count708 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count710 (b : Nat → Bool) : Nat := countLit b [94, 96, 99, 100]
def count714 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count716 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count718 (b : Nat → Bool) : Nat := countLit b [103, 105, 107, 108]
def count722 (b : Nat → Bool) : Nat := countLit b [94, 96, 99, 100, 103, 105, 107, 108]
def count730 (b : Nat → Bool) : Nat := countLit b [111, 112]
def count732 (b : Nat → Bool) : Nat := countLit b [113, 115]
def count734 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 115]
def count738 (b : Nat → Bool) : Nat := countLit b [117, 118]
def count740 (b : Nat → Bool) : Nat := countLit b [121, 123]
def count742 (b : Nat → Bool) : Nat := countLit b [117, 118, 121, 123]
def count746 (b : Nat → Bool) : Nat := countLit b [111, 112, 113, 115, 117, 118, 121, 123]
def count754 (b : Nat → Bool) : Nat := countLit b [94, 96, 99, 100, 103, 105, 107, 108, 111, 112, 113, 115, 117, 118, 121, 123]
def count770 (b : Nat → Bool) : Nat := countLit b [63, 65, 68, 71, 73, 74, 75, 80, 81, 82, 86, 87, 88, 91, 93, 94, 96, 99, 100, 103, 105, 107, 108, 111, 112, 113, 115, 117, 118, 121, 123]
def count801 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 5, 8, 11, 12, 14, 18, 20, 21, 23, 24, 27, 29, 32, 35, 37, 38, 39, 43, 45, 46, 47, 51, 52, 53, 55, 57, 60, 61, 63, 65, 68, 71, 73, 74, 75, 80, 81, 82, 86, 87, 88, 91, 93, 94, 96, 99, 100, 103, 105, 107, 108, 111, 112, 113, 115, 117, 118, 121, 123]
def count843 (b : Nat → Bool) : Nat := countLit b [-3, -4]
def count845 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4]
def count848 (b : Nat → Bool) : Nat := countLit b [-5, -8]
def count850 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count852 (b : Nat → Bool) : Nat := countLit b [-5, -8, -11, -12]
def count856 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -8, -11, -12]
def count863 (b : Nat → Bool) : Nat := countLit b [-14, -18]
def count865 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count867 (b : Nat → Bool) : Nat := countLit b [-14, -18, -20, -21]
def count871 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count873 (b : Nat → Bool) : Nat := countLit b [-27, -29]
def count875 (b : Nat → Bool) : Nat := countLit b [-23, -24, -27, -29]
def count879 (b : Nat → Bool) : Nat := countLit b [-14, -18, -20, -21, -23, -24, -27, -29]
def count887 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]
def count902 (b : Nat → Bool) : Nat := countLit b [-32, -35]
def count904 (b : Nat → Bool) : Nat := countLit b [-37, -38]
def count906 (b : Nat → Bool) : Nat := countLit b [-32, -35, -37, -38]
def count910 (b : Nat → Bool) : Nat := countLit b [-39, -43]
def count912 (b : Nat → Bool) : Nat := countLit b [-45, -46]
def count914 (b : Nat → Bool) : Nat := countLit b [-39, -43, -45, -46]
def count918 (b : Nat → Bool) : Nat := countLit b [-32, -35, -37, -38, -39, -43, -45, -46]
def count926 (b : Nat → Bool) : Nat := countLit b [-47, -51]
def count928 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count930 (b : Nat → Bool) : Nat := countLit b [-47, -51, -52, -53]
def count934 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count936 (b : Nat → Bool) : Nat := countLit b [-60, -61]
def count938 (b : Nat → Bool) : Nat := countLit b [-55, -57, -60, -61]
def count942 (b : Nat → Bool) : Nat := countLit b [-47, -51, -52, -53, -55, -57, -60, -61]
def count950 (b : Nat → Bool) : Nat := countLit b [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]
def count966 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]
def count988 (b : Nat → Bool) : Nat := countLit b [-65, -68]
def count990 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68]
def count993 (b : Nat → Bool) : Nat := countLit b [-71, -73]
def count995 (b : Nat → Bool) : Nat := countLit b [-74, -75]
def count997 (b : Nat → Bool) : Nat := countLit b [-71, -73, -74, -75]
def count1001 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68, -71, -73, -74, -75]
def count1008 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1010 (b : Nat → Bool) : Nat := countLit b [-82, -86]
def count1012 (b : Nat → Bool) : Nat := countLit b [-80, -81, -82, -86]
def count1016 (b : Nat → Bool) : Nat := countLit b [-87, -88]
def count1018 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count1020 (b : Nat → Bool) : Nat := countLit b [-87, -88, -91, -93]
def count1024 (b : Nat → Bool) : Nat := countLit b [-80, -81, -82, -86, -87, -88, -91, -93]
def count1032 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93]
def count1047 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count1049 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1051 (b : Nat → Bool) : Nat := countLit b [-94, -96, -99, -100]
def count1055 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count1057 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1059 (b : Nat → Bool) : Nat := countLit b [-103, -105, -107, -108]
def count1063 (b : Nat → Bool) : Nat := countLit b [-94, -96, -99, -100, -103, -105, -107, -108]
def count1071 (b : Nat → Bool) : Nat := countLit b [-111, -112]
def count1073 (b : Nat → Bool) : Nat := countLit b [-113, -115]
def count1075 (b : Nat → Bool) : Nat := countLit b [-111, -112, -113, -115]
def count1079 (b : Nat → Bool) : Nat := countLit b [-117, -118]
def count1081 (b : Nat → Bool) : Nat := countLit b [-121, -123]
def count1083 (b : Nat → Bool) : Nat := countLit b [-117, -118, -121, -123]
def count1087 (b : Nat → Bool) : Nat := countLit b [-111, -112, -113, -115, -117, -118, -121, -123]
def count1095 (b : Nat → Bool) : Nat := countLit b [-94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]
def count1111 (b : Nat → Bool) : Nat := countLit b [-63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]
def count1133 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29, -32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61, -63, -65, -68, -71, -73, -74, -75, -80, -81, -82, -86, -87, -88, -91, -93, -94, -96, -99, -100, -103, -105, -107, -108, -111, -112, -113, -115, -117, -118, -121, -123]
def count1155 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count1157 (b : Nat → Bool) : Nat := countLit b [2, 6, 7]
def count1160 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count1162 (b : Nat → Bool) : Nat := countLit b [13, 15]
def count1164 (b : Nat → Bool) : Nat := countLit b [9, 10, 13, 15]
def count1168 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 9, 10, 13, 15]
def count1175 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count1177 (b : Nat → Bool) : Nat := countLit b [19, 22]
def count1179 (b : Nat → Bool) : Nat := countLit b [16, 17, 19, 22]
def count1183 (b : Nat → Bool) : Nat := countLit b [25, 26]
def count1185 (b : Nat → Bool) : Nat := countLit b [28, 30]
def count1187 (b : Nat → Bool) : Nat := countLit b [25, 26, 28, 30]
def count1191 (b : Nat → Bool) : Nat := countLit b [16, 17, 19, 22, 25, 26, 28, 30]
def count1199 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 9, 10, 13, 15, 16, 17, 19, 22, 25, 26, 28, 30]
def count1214 (b : Nat → Bool) : Nat := countLit b [31, 33]
def count1216 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count1218 (b : Nat → Bool) : Nat := countLit b [31, 33, 34, 36]
def count1222 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count1224 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count1226 (b : Nat → Bool) : Nat := countLit b [40, 41, 42, 44]
def count1230 (b : Nat → Bool) : Nat := countLit b [31, 33, 34, 36, 40, 41, 42, 44]
def count1238 (b : Nat → Bool) : Nat := countLit b [48, 49]
def count1240 (b : Nat → Bool) : Nat := countLit b [50, 54]
def count1242 (b : Nat → Bool) : Nat := countLit b [48, 49, 50, 54]
def count1246 (b : Nat → Bool) : Nat := countLit b [56, 58]
def count1248 (b : Nat → Bool) : Nat := countLit b [59, 62]
def count1250 (b : Nat → Bool) : Nat := countLit b [56, 58, 59, 62]
def count1254 (b : Nat → Bool) : Nat := countLit b [48, 49, 50, 54, 56, 58, 59, 62]
def count1262 (b : Nat → Bool) : Nat := countLit b [31, 33, 34, 36, 40, 41, 42, 44, 48, 49, 50, 54, 56, 58, 59, 62]
def count1278 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 9, 10, 13, 15, 16, 17, 19, 22, 25, 26, 28, 30, 31, 33, 34, 36, 40, 41, 42, 44, 48, 49, 50, 54, 56, 58, 59, 62]
def count1309 (b : Nat → Bool) : Nat := countLit b [66, 67]
def count1311 (b : Nat → Bool) : Nat := countLit b [64, 66, 67]
def count1314 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count1316 (b : Nat → Bool) : Nat := countLit b [72, 76]
def count1318 (b : Nat → Bool) : Nat := countLit b [69, 70, 72, 76]
def count1322 (b : Nat → Bool) : Nat := countLit b [64, 66, 67, 69, 70, 72, 76]
def count1329 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count1331 (b : Nat → Bool) : Nat := countLit b [79, 83]
def count1333 (b : Nat → Bool) : Nat := countLit b [77, 78, 79, 83]
def count1337 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count1339 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count1341 (b : Nat → Bool) : Nat := countLit b [84, 85, 89, 90]
def count1345 (b : Nat → Bool) : Nat := countLit b [77, 78, 79, 83, 84, 85, 89, 90]
def count1353 (b : Nat → Bool) : Nat := countLit b [64, 66, 67, 69, 70, 72, 76, 77, 78, 79, 83, 84, 85, 89, 90]
def count1368 (b : Nat → Bool) : Nat := countLit b [92, 95]
def count1370 (b : Nat → Bool) : Nat := countLit b [97, 98]
def count1372 (b : Nat → Bool) : Nat := countLit b [92, 95, 97, 98]
def count1376 (b : Nat → Bool) : Nat := countLit b [101, 102]
def count1378 (b : Nat → Bool) : Nat := countLit b [104, 106]
def count1380 (b : Nat → Bool) : Nat := countLit b [101, 102, 104, 106]
def count1384 (b : Nat → Bool) : Nat := countLit b [92, 95, 97, 98, 101, 102, 104, 106]
def count1392 (b : Nat → Bool) : Nat := countLit b [109, 110]
def count1394 (b : Nat → Bool) : Nat := countLit b [114, 116]
def count1396 (b : Nat → Bool) : Nat := countLit b [109, 110, 114, 116]
def count1400 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count1402 (b : Nat → Bool) : Nat := countLit b [122, 124]
def count1404 (b : Nat → Bool) : Nat := countLit b [119, 120, 122, 124]
def count1408 (b : Nat → Bool) : Nat := countLit b [109, 110, 114, 116, 119, 120, 122, 124]
def count1416 (b : Nat → Bool) : Nat := countLit b [92, 95, 97, 98, 101, 102, 104, 106, 109, 110, 114, 116, 119, 120, 122, 124]
def count1432 (b : Nat → Bool) : Nat := countLit b [64, 66, 67, 69, 70, 72, 76, 77, 78, 79, 83, 84, 85, 89, 90, 92, 95, 97, 98, 101, 102, 104, 106, 109, 110, 114, 116, 119, 120, 122, 124]
def count1463 (b : Nat → Bool) : Nat := countLit b [2, 6, 7, 9, 10, 13, 15, 16, 17, 19, 22, 25, 26, 28, 30, 31, 33, 34, 36, 40, 41, 42, 44, 48, 49, 50, 54, 56, 58, 59, 62, 64, 66, 67, 69, 70, 72, 76, 77, 78, 79, 83, 84, 85, 89, 90, 92, 95, 97, 98, 101, 102, 104, 106, 109, 110, 114, 116, 119, 120, 122, 124]
def count1505 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count1507 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7]
def count1510 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count1512 (b : Nat → Bool) : Nat := countLit b [-13, -15]
def count1514 (b : Nat → Bool) : Nat := countLit b [-9, -10, -13, -15]
def count1518 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -9, -10, -13, -15]
def count1525 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count1527 (b : Nat → Bool) : Nat := countLit b [-19, -22]
def count1529 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19, -22]
def count1533 (b : Nat → Bool) : Nat := countLit b [-25, -26]
def count1535 (b : Nat → Bool) : Nat := countLit b [-28, -30]
def count1537 (b : Nat → Bool) : Nat := countLit b [-25, -26, -28, -30]
def count1541 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19, -22, -25, -26, -28, -30]
def count1549 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30]
def count1564 (b : Nat → Bool) : Nat := countLit b [-31, -33]
def count1566 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count1568 (b : Nat → Bool) : Nat := countLit b [-31, -33, -34, -36]
def count1572 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count1574 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count1576 (b : Nat → Bool) : Nat := countLit b [-40, -41, -42, -44]
def count1580 (b : Nat → Bool) : Nat := countLit b [-31, -33, -34, -36, -40, -41, -42, -44]
def count1588 (b : Nat → Bool) : Nat := countLit b [-48, -49]
def count1590 (b : Nat → Bool) : Nat := countLit b [-50, -54]
def count1592 (b : Nat → Bool) : Nat := countLit b [-48, -49, -50, -54]
def count1596 (b : Nat → Bool) : Nat := countLit b [-56, -58]
def count1598 (b : Nat → Bool) : Nat := countLit b [-59, -62]
def count1600 (b : Nat → Bool) : Nat := countLit b [-56, -58, -59, -62]
def count1604 (b : Nat → Bool) : Nat := countLit b [-48, -49, -50, -54, -56, -58, -59, -62]
def count1612 (b : Nat → Bool) : Nat := countLit b [-31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62]
def count1628 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30, -31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62]
def count1650 (b : Nat → Bool) : Nat := countLit b [-66, -67]
def count1652 (b : Nat → Bool) : Nat := countLit b [-64, -66, -67]
def count1655 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count1657 (b : Nat → Bool) : Nat := countLit b [-72, -76]
def count1659 (b : Nat → Bool) : Nat := countLit b [-69, -70, -72, -76]
def count1663 (b : Nat → Bool) : Nat := countLit b [-64, -66, -67, -69, -70, -72, -76]
def count1670 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count1672 (b : Nat → Bool) : Nat := countLit b [-79, -83]
def count1674 (b : Nat → Bool) : Nat := countLit b [-77, -78, -79, -83]
def count1678 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count1680 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count1682 (b : Nat → Bool) : Nat := countLit b [-84, -85, -89, -90]
def count1686 (b : Nat → Bool) : Nat := countLit b [-77, -78, -79, -83, -84, -85, -89, -90]
def count1694 (b : Nat → Bool) : Nat := countLit b [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90]
def count1709 (b : Nat → Bool) : Nat := countLit b [-92, -95]
def count1711 (b : Nat → Bool) : Nat := countLit b [-97, -98]
def count1713 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97, -98]
def count1717 (b : Nat → Bool) : Nat := countLit b [-101, -102]
def count1719 (b : Nat → Bool) : Nat := countLit b [-104, -106]
def count1721 (b : Nat → Bool) : Nat := countLit b [-101, -102, -104, -106]
def count1725 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97, -98, -101, -102, -104, -106]
def count1733 (b : Nat → Bool) : Nat := countLit b [-109, -110]
def count1735 (b : Nat → Bool) : Nat := countLit b [-114, -116]
def count1737 (b : Nat → Bool) : Nat := countLit b [-109, -110, -114, -116]
def count1741 (b : Nat → Bool) : Nat := countLit b [-119, -120]
def count1743 (b : Nat → Bool) : Nat := countLit b [-122, -124]
def count1745 (b : Nat → Bool) : Nat := countLit b [-119, -120, -122, -124]
def count1749 (b : Nat → Bool) : Nat := countLit b [-109, -110, -114, -116, -119, -120, -122, -124]
def count1757 (b : Nat → Bool) : Nat := countLit b [-92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124]
def count1773 (b : Nat → Bool) : Nat := countLit b [-64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90, -92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124]
def count1795 (b : Nat → Bool) : Nat := countLit b [-2, -6, -7, -9, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -30, -31, -33, -34, -36, -40, -41, -42, -44, -48, -49, -50, -54, -56, -58, -59, -62, -64, -66, -67, -69, -70, -72, -76, -77, -78, -79, -83, -84, -85, -89, -90, -92, -95, -97, -98, -101, -102, -104, -106, -109, -110, -114, -116, -119, -120, -122, -124]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 908 then (if i < 454 then (if i < 227 then (if i < 113 then (if i < 56 then (if i < 28 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 24 then (if i < 22 then b 21 else (if i < 23 then b 22 else b 23)) else (if i < 26 then (if i < 25 then b 24 else b 25) else (if i < 27 then b 26 else b 27))))) else (if i < 42 then (if i < 35 then (if i < 31 then (if i < 29 then b 28 else (if i < 30 then b 29 else b 30)) else (if i < 33 then (if i < 32 then b 31 else b 32) else (if i < 34 then b 33 else b 34))) else (if i < 38 then (if i < 36 then b 35 else (if i < 37 then b 36 else b 37)) else (if i < 40 then (if i < 39 then b 38 else b 39) else (if i < 41 then b 40 else b 41)))) else (if i < 49 then (if i < 45 then (if i < 43 then b 42 else (if i < 44 then b 43 else b 44)) else (if i < 47 then (if i < 46 then b 45 else b 46) else (if i < 48 then b 47 else b 48))) else (if i < 52 then (if i < 50 then b 49 else (if i < 51 then b 50 else b 51)) else (if i < 54 then (if i < 53 then b 52 else b 53) else (if i < 55 then b 54 else b 55)))))) else (if i < 84 then (if i < 70 then (if i < 63 then (if i < 59 then (if i < 57 then b 56 else (if i < 58 then b 57 else b 58)) else (if i < 61 then (if i < 60 then b 59 else b 60) else (if i < 62 then b 61 else b 62))) else (if i < 66 then (if i < 64 then b 63 else (if i < 65 then b 64 else b 65)) else (if i < 68 then (if i < 67 then b 66 else b 67) else (if i < 69 then b 68 else b 69)))) else (if i < 77 then (if i < 73 then (if i < 71 then b 70 else (if i < 72 then b 71 else b 72)) else (if i < 75 then (if i < 74 then b 73 else b 74) else (if i < 76 then b 75 else b 76))) else (if i < 80 then (if i < 78 then b 77 else (if i < 79 then b 78 else b 79)) else (if i < 82 then (if i < 81 then b 80 else b 81) else (if i < 83 then b 82 else b 83))))) else (if i < 98 then (if i < 91 then (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90))) else (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else b 97)))) else (if i < 105 then (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else b 104))) else (if i < 109 then (if i < 107 then (if i < 106 then b 105 else b 106) else (if i < 108 then b 107 else b 108)) else (if i < 111 then (if i < 110 then b 109 else b 110) else (if i < 112 then b 111 else b 112))))))) else (if i < 170 then (if i < 141 then (if i < 127 then (if i < 120 then (if i < 116 then (if i < 114 then b 113 else (if i < 115 then b 114 else b 115)) else (if i < 118 then (if i < 117 then b 116 else b 117) else (if i < 119 then b 118 else b 119))) else (if i < 123 then (if i < 121 then b 120 else (if i < 122 then b 121 else b 122)) else (if i < 125 then (if i < 124 then b 123 else b 124) else (if i < 126 then b 125 else b 126)))) else (if i < 134 then (if i < 130 then (if i < 128 then b 127 else (if i < 129 then b 128 else b 129)) else (if i < 132 then (if i < 131 then b 130 else b 131) else (if i < 133 then b 132 else b 133))) else (if i < 137 then (if i < 135 then b 134 else (if i < 136 then b 135 else b 136)) else (if i < 139 then (if i < 138 then b 137 else b 138) else (if i < 140 then b 139 else b 140))))) else (if i < 155 then (if i < 148 then (if i < 144 then (if i < 142 then b 141 else (if i < 143 then b 142 else b 143)) else (if i < 146 then (if i < 145 then b 144 else b 145) else (if i < 147 then b 146 else b 147))) else (if i < 151 then (if i < 149 then b 148 else (if i < 150 then b 149 else b 150)) else (if i < 153 then (if i < 152 then b 151 else b 152) else (if i < 154 then b 153 else b 154)))) else (if i < 162 then (if i < 158 then (if i < 156 then b 155 else (if i < 157 then b 156 else b 157)) else (if i < 160 then (if i < 159 then b 158 else b 159) else (if i < 161 then b 160 else b 161))) else (if i < 166 then (if i < 164 then (if i < 163 then b 162 else b 163) else (if i < 165 then b 164 else b 165)) else (if i < 168 then (if i < 167 then b 166 else b 167) else (if i < 169 then b 168 else b 169)))))) else (if i < 198 then (if i < 184 then (if i < 177 then (if i < 173 then (if i < 171 then b 170 else (if i < 172 then b 171 else b 172)) else (if i < 175 then (if i < 174 then b 173 else b 174) else (if i < 176 then b 175 else b 176))) else (if i < 180 then (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)) else (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else b 183)))) else (if i < 191 then (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 189 then (if i < 188 then b 187 else b 188) else (if i < 190 then b 189 else b 190))) else (if i < 194 then (if i < 192 then b 191 else (if i < 193 then b 192 else b 193)) else (if i < 196 then (if i < 195 then b 194 else b 195) else (if i < 197 then b 196 else b 197))))) else (if i < 212 then (if i < 205 then (if i < 201 then (if i < 199 then b 198 else (if i < 200 then b 199 else b 200)) else (if i < 203 then (if i < 202 then b 201 else b 202) else (if i < 204 then b 203 else b 204))) else (if i < 208 then (if i < 206 then b 205 else (if i < 207 then b 206 else b 207)) else (if i < 210 then (if i < 209 then b 208 else b 209) else (if i < 211 then b 210 else b 211)))) else (if i < 219 then (if i < 215 then (if i < 213 then b 212 else (if i < 214 then b 213 else b 214)) else (if i < 217 then (if i < 216 then b 215 else b 216) else (if i < 218 then b 217 else b 218))) else (if i < 223 then (if i < 221 then (if i < 220 then b 219 else b 220) else (if i < 222 then b 221 else b 222)) else (if i < 225 then (if i < 224 then b 223 else b 224) else (if i < 226 then b 225 else b 226)))))))) else (if i < 340 then (if i < 283 then (if i < 255 then (if i < 241 then (if i < 234 then (if i < 230 then (if i < 228 then b 227 else (if i < 229 then b 228 else b 229)) else (if i < 232 then (if i < 231 then b 230 else b 231) else (if i < 233 then b 232 else b 233))) else (if i < 237 then (if i < 235 then b 234 else (if i < 236 then b 235 else b 236)) else (if i < 239 then (if i < 238 then b 237 else b 238) else (if i < 240 then b 239 else b 240)))) else (if i < 248 then (if i < 244 then (if i < 242 then b 241 else (if i < 243 then b 242 else b 243)) else (if i < 246 then (if i < 245 then b 244 else b 245) else (if i < 247 then b 246 else b 247))) else (if i < 251 then (if i < 249 then b 248 else (if i < 250 then decide (1 ≤ count249 b) else decide (2 ≤ count249 b))) else (if i < 253 then (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b)) else (if i < 254 then decide (1 ≤ count253 b) else decide (2 ≤ count253 b)))))) else (if i < 269 then (if i < 262 then (if i < 258 then (if i < 256 then decide (1 ≤ count255 b) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 260 then (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))) else (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 267 then (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b))))) else (if i < 276 then (if i < 272 then (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))) else (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b)))) else (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 281 then (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b))))))) else (if i < 311 then (if i < 297 then (if i < 290 then (if i < 286 then (if i < 284 then decide (1 ≤ count283 b) else (if i < 285 then decide (2 ≤ count283 b) else decide (1 ≤ count285 b))) else (if i < 288 then (if i < 287 then decide (2 ≤ count285 b) else decide (1 ≤ count287 b)) else (if i < 289 then decide (2 ≤ count287 b) else decide (1 ≤ count289 b)))) else (if i < 293 then (if i < 291 then decide (2 ≤ count289 b) else (if i < 292 then decide (1 ≤ count291 b) else decide (2 ≤ count291 b))) else (if i < 295 then (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)) else (if i < 296 then decide (1 ≤ count295 b) else decide (2 ≤ count295 b))))) else (if i < 304 then (if i < 300 then (if i < 298 then decide (1 ≤ count297 b) else (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b))) else (if i < 302 then (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b)) else (if i < 303 then decide (2 ≤ count301 b) else decide (1 ≤ count303 b)))) else (if i < 307 then (if i < 305 then decide (2 ≤ count303 b) else (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b))) else (if i < 309 then (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)) else (if i < 310 then decide (1 ≤ count309 b) else decide (2 ≤ count309 b)))))) else (if i < 325 then (if i < 318 then (if i < 314 then (if i < 312 then decide (1 ≤ count311 b) else (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b))) else (if i < 316 then (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)) else (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)))) else (if i < 321 then (if i < 319 then decide (2 ≤ count317 b) else (if i < 320 then decide (1 ≤ count319 b) else decide (2 ≤ count319 b))) else (if i < 323 then (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b)) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))))) else (if i < 332 then (if i < 328 then (if i < 326 then decide (1 ≤ count325 b) else (if i < 327 then decide (2 ≤ count325 b) else decide (1 ≤ count327 b))) else (if i < 330 then (if i < 329 then decide (2 ≤ count327 b) else decide (1 ≤ count329 b)) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b)))) else (if i < 336 then (if i < 334 then (if i < 333 then decide (2 ≤ count331 b) else decide (1 ≤ count333 b)) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 338 then (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)))))))) else (if i < 397 then (if i < 368 then (if i < 354 then (if i < 347 then (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b)))) else (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b))))) else (if i < 361 then (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))) else (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)))))) else (if i < 382 then (if i < 375 then (if i < 371 then (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))) else (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 378 then (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))) else (if i < 380 then (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))))) else (if i < 389 then (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 387 then (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b)))) else (if i < 393 then (if i < 391 then (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))) else (if i < 395 then (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)) else (if i < 396 then decide (1 ≤ count395 b) else decide (2 ≤ count395 b))))))) else (if i < 425 then (if i < 411 then (if i < 404 then (if i < 400 then (if i < 398 then decide (1 ≤ count397 b) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b))) else (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b)))) else (if i < 407 then (if i < 405 then decide (2 ≤ count403 b) else (if i < 406 then decide (1 ≤ count405 b) else decide (2 ≤ count405 b))) else (if i < 409 then (if i < 408 then decide (1 ≤ count407 b) else decide (2 ≤ count407 b)) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))))) else (if i < 418 then (if i < 414 then (if i < 412 then decide (1 ≤ count411 b) else (if i < 413 then decide (2 ≤ count411 b) else decide (1 ≤ count413 b))) else (if i < 416 then (if i < 415 then decide (2 ≤ count413 b) else decide (1 ≤ count415 b)) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b)))) else (if i < 421 then (if i < 419 then decide (2 ≤ count417 b) else (if i < 420 then decide (1 ≤ count419 b) else decide (2 ≤ count419 b))) else (if i < 423 then (if i < 422 then decide (1 ≤ count421 b) else decide (2 ≤ count421 b)) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b)))))) else (if i < 439 then (if i < 432 then (if i < 428 then (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b))) else (if i < 430 then (if i < 429 then decide (2 ≤ count427 b) else decide (1 ≤ count429 b)) else (if i < 431 then decide (2 ≤ count429 b) else decide (1 ≤ count431 b)))) else (if i < 435 then (if i < 433 then decide (2 ≤ count431 b) else (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b))) else (if i < 437 then (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)) else (if i < 438 then decide (1 ≤ count437 b) else decide (2 ≤ count437 b))))) else (if i < 446 then (if i < 442 then (if i < 440 then decide (1 ≤ count439 b) else (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b))) else (if i < 444 then (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)) else (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)))) else (if i < 450 then (if i < 448 then (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b)) else (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b))) else (if i < 452 then (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b)) else (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b)))))))))) else (if i < 681 then (if i < 567 then (if i < 510 then (if i < 482 then (if i < 468 then (if i < 461 then (if i < 457 then (if i < 455 then decide (2 ≤ count453 b) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))) else (if i < 459 then (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)))) else (if i < 464 then (if i < 462 then decide (1 ≤ count461 b) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b))) else (if i < 466 then (if i < 465 then decide (2 ≤ count463 b) else decide (1 ≤ count465 b)) else (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b))))) else (if i < 475 then (if i < 471 then (if i < 469 then decide (2 ≤ count467 b) else (if i < 470 then decide (1 ≤ count469 b) else decide (2 ≤ count469 b))) else (if i < 473 then (if i < 472 then decide (1 ≤ count471 b) else decide (2 ≤ count471 b)) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b)))) else (if i < 478 then (if i < 476 then decide (1 ≤ count475 b) else (if i < 477 then decide (2 ≤ count475 b) else decide (1 ≤ count477 b))) else (if i < 480 then (if i < 479 then decide (2 ≤ count477 b) else decide (1 ≤ count479 b)) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b)))))) else (if i < 496 then (if i < 489 then (if i < 485 then (if i < 483 then decide (2 ≤ count481 b) else (if i < 484 then decide (1 ≤ count483 b) else decide (2 ≤ count483 b))) else (if i < 487 then (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b)) else (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b)))) else (if i < 492 then (if i < 490 then decide (1 ≤ count489 b) else (if i < 491 then decide (2 ≤ count489 b) else decide (1 ≤ count491 b))) else (if i < 494 then (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b)) else (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b))))) else (if i < 503 then (if i < 499 then (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (3 ≤ count495 b) else decide (1 ≤ count498 b))) else (if i < 501 then (if i < 500 then decide (2 ≤ count498 b) else decide (1 ≤ count500 b)) else (if i < 502 then decide (2 ≤ count500 b) else decide (1 ≤ count502 b)))) else (if i < 506 then (if i < 504 then decide (2 ≤ count502 b) else (if i < 505 then decide (3 ≤ count502 b) else decide (4 ≤ count502 b))) else (if i < 508 then (if i < 507 then decide (1 ≤ count506 b) else decide (2 ≤ count506 b)) else (if i < 509 then decide (3 ≤ count506 b) else decide (4 ≤ count506 b))))))) else (if i < 538 then (if i < 524 then (if i < 517 then (if i < 513 then (if i < 511 then decide (5 ≤ count506 b) else (if i < 512 then decide (6 ≤ count506 b) else decide (7 ≤ count506 b))) else (if i < 515 then (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b)) else (if i < 516 then decide (1 ≤ count515 b) else decide (2 ≤ count515 b)))) else (if i < 520 then (if i < 518 then decide (1 ≤ count517 b) else (if i < 519 then decide (2 ≤ count517 b) else decide (3 ≤ count517 b))) else (if i < 522 then (if i < 521 then decide (4 ≤ count517 b) else decide (1 ≤ count521 b)) else (if i < 523 then decide (2 ≤ count521 b) else decide (1 ≤ count523 b))))) else (if i < 531 then (if i < 527 then (if i < 525 then decide (2 ≤ count523 b) else (if i < 526 then decide (1 ≤ count525 b) else decide (2 ≤ count525 b))) else (if i < 529 then (if i < 528 then decide (3 ≤ count525 b) else decide (4 ≤ count525 b)) else (if i < 530 then decide (1 ≤ count529 b) else decide (2 ≤ count529 b)))) else (if i < 534 then (if i < 532 then decide (3 ≤ count529 b) else (if i < 533 then decide (4 ≤ count529 b) else decide (5 ≤ count529 b))) else (if i < 536 then (if i < 535 then decide (6 ≤ count529 b) else decide (7 ≤ count529 b)) else (if i < 537 then decide (8 ≤ count529 b) else decide (1 ≤ count537 b)))))) else (if i < 552 then (if i < 545 then (if i < 541 then (if i < 539 then decide (2 ≤ count537 b) else (if i < 540 then decide (3 ≤ count537 b) else decide (4 ≤ count537 b))) else (if i < 543 then (if i < 542 then decide (5 ≤ count537 b) else decide (6 ≤ count537 b)) else (if i < 544 then decide (7 ≤ count537 b) else decide (8 ≤ count537 b)))) else (if i < 548 then (if i < 546 then decide (9 ≤ count537 b) else (if i < 547 then decide (10 ≤ count537 b) else decide (11 ≤ count537 b))) else (if i < 550 then (if i < 549 then decide (12 ≤ count537 b) else decide (13 ≤ count537 b)) else (if i < 551 then decide (14 ≤ count537 b) else decide (15 ≤ count537 b))))) else (if i < 559 then (if i < 555 then (if i < 553 then decide (1 ≤ count552 b) else (if i < 554 then decide (2 ≤ count552 b) else decide (1 ≤ count554 b))) else (if i < 557 then (if i < 556 then decide (2 ≤ count554 b) else decide (1 ≤ count556 b)) else (if i < 558 then decide (2 ≤ count556 b) else decide (3 ≤ count556 b)))) else (if i < 563 then (if i < 561 then (if i < 560 then decide (4 ≤ count556 b) else decide (1 ≤ count560 b)) else (if i < 562 then decide (2 ≤ count560 b) else decide (1 ≤ count562 b))) else (if i < 565 then (if i < 564 then decide (2 ≤ count562 b) else decide (1 ≤ count564 b)) else (if i < 566 then decide (2 ≤ count564 b) else decide (3 ≤ count564 b)))))))) else (if i < 624 then (if i < 595 then (if i < 581 then (if i < 574 then (if i < 570 then (if i < 568 then decide (4 ≤ count564 b) else (if i < 569 then decide (1 ≤ count568 b) else decide (2 ≤ count568 b))) else (if i < 572 then (if i < 571 then decide (3 ≤ count568 b) else decide (4 ≤ count568 b)) else (if i < 573 then decide (5 ≤ count568 b) else decide (6 ≤ count568 b)))) else (if i < 577 then (if i < 575 then decide (7 ≤ count568 b) else (if i < 576 then decide (8 ≤ count568 b) else decide (1 ≤ count576 b))) else (if i < 579 then (if i < 578 then decide (2 ≤ count576 b) else decide (1 ≤ count578 b)) else (if i < 580 then decide (2 ≤ count578 b) else decide (1 ≤ count580 b))))) else (if i < 588 then (if i < 584 then (if i < 582 then decide (2 ≤ count580 b) else (if i < 583 then decide (3 ≤ count580 b) else decide (4 ≤ count580 b))) else (if i < 586 then (if i < 585 then decide (1 ≤ count584 b) else decide (2 ≤ count584 b)) else (if i < 587 then decide (1 ≤ count586 b) else decide (2 ≤ count586 b)))) else (if i < 591 then (if i < 589 then decide (1 ≤ count588 b) else (if i < 590 then decide (2 ≤ count588 b) else decide (3 ≤ count588 b))) else (if i < 593 then (if i < 592 then decide (4 ≤ count588 b) else decide (1 ≤ count592 b)) else (if i < 594 then decide (2 ≤ count592 b) else decide (3 ≤ count592 b)))))) else (if i < 609 then (if i < 602 then (if i < 598 then (if i < 596 then decide (4 ≤ count592 b) else (if i < 597 then decide (5 ≤ count592 b) else decide (6 ≤ count592 b))) else (if i < 600 then (if i < 599 then decide (7 ≤ count592 b) else decide (8 ≤ count592 b)) else (if i < 601 then decide (1 ≤ count600 b) else decide (2 ≤ count600 b)))) else (if i < 605 then (if i < 603 then decide (3 ≤ count600 b) else (if i < 604 then decide (4 ≤ count600 b) else decide (5 ≤ count600 b))) else (if i < 607 then (if i < 606 then decide (6 ≤ count600 b) else decide (7 ≤ count600 b)) else (if i < 608 then decide (8 ≤ count600 b) else decide (9 ≤ count600 b))))) else (if i < 616 then (if i < 612 then (if i < 610 then decide (10 ≤ count600 b) else (if i < 611 then decide (11 ≤ count600 b) else decide (12 ≤ count600 b))) else (if i < 614 then (if i < 613 then decide (13 ≤ count600 b) else decide (14 ≤ count600 b)) else (if i < 615 then decide (15 ≤ count600 b) else decide (16 ≤ count600 b)))) else (if i < 620 then (if i < 618 then (if i < 617 then decide (1 ≤ count616 b) else decide (2 ≤ count616 b)) else (if i < 619 then decide (3 ≤ count616 b) else decide (4 ≤ count616 b))) else (if i < 622 then (if i < 621 then decide (5 ≤ count616 b) else decide (6 ≤ count616 b)) else (if i < 623 then decide (7 ≤ count616 b) else decide (8 ≤ count616 b))))))) else (if i < 652 then (if i < 638 then (if i < 631 then (if i < 627 then (if i < 625 then decide (9 ≤ count616 b) else (if i < 626 then decide (10 ≤ count616 b) else decide (11 ≤ count616 b))) else (if i < 629 then (if i < 628 then decide (12 ≤ count616 b) else decide (13 ≤ count616 b)) else (if i < 630 then decide (14 ≤ count616 b) else decide (15 ≤ count616 b)))) else (if i < 634 then (if i < 632 then decide (16 ≤ count616 b) else (if i < 633 then decide (17 ≤ count616 b) else decide (18 ≤ count616 b))) else (if i < 636 then (if i < 635 then decide (19 ≤ count616 b) else decide (20 ≤ count616 b)) else (if i < 637 then decide (21 ≤ count616 b) else decide (22 ≤ count616 b))))) else (if i < 645 then (if i < 641 then (if i < 639 then decide (23 ≤ count616 b) else (if i < 640 then decide (24 ≤ count616 b) else decide (25 ≤ count616 b))) else (if i < 643 then (if i < 642 then decide (26 ≤ count616 b) else decide (27 ≤ count616 b)) else (if i < 644 then decide (28 ≤ count616 b) else decide (29 ≤ count616 b)))) else (if i < 648 then (if i < 646 then decide (30 ≤ count616 b) else (if i < 647 then decide (31 ≤ count616 b) else decide (1 ≤ count647 b))) else (if i < 650 then (if i < 649 then decide (2 ≤ count647 b) else decide (1 ≤ count649 b)) else (if i < 651 then decide (2 ≤ count649 b) else decide (3 ≤ count649 b)))))) else (if i < 666 then (if i < 659 then (if i < 655 then (if i < 653 then decide (1 ≤ count652 b) else (if i < 654 then decide (2 ≤ count652 b) else decide (1 ≤ count654 b))) else (if i < 657 then (if i < 656 then decide (2 ≤ count654 b) else decide (1 ≤ count656 b)) else (if i < 658 then decide (2 ≤ count656 b) else decide (3 ≤ count656 b)))) else (if i < 662 then (if i < 660 then decide (4 ≤ count656 b) else (if i < 661 then decide (1 ≤ count660 b) else decide (2 ≤ count660 b))) else (if i < 664 then (if i < 663 then decide (3 ≤ count660 b) else decide (4 ≤ count660 b)) else (if i < 665 then decide (5 ≤ count660 b) else decide (6 ≤ count660 b))))) else (if i < 673 then (if i < 669 then (if i < 667 then decide (7 ≤ count660 b) else (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b))) else (if i < 671 then (if i < 670 then decide (1 ≤ count669 b) else decide (2 ≤ count669 b)) else (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b)))) else (if i < 677 then (if i < 675 then (if i < 674 then decide (3 ≤ count671 b) else decide (4 ≤ count671 b)) else (if i < 676 then decide (1 ≤ count675 b) else decide (2 ≤ count675 b))) else (if i < 679 then (if i < 678 then decide (1 ≤ count677 b) else decide (2 ≤ count677 b)) else (if i < 680 then decide (1 ≤ count679 b) else decide (2 ≤ count679 b))))))))) else (if i < 794 then (if i < 737 then (if i < 709 then (if i < 695 then (if i < 688 then (if i < 684 then (if i < 682 then decide (3 ≤ count679 b) else (if i < 683 then decide (4 ≤ count679 b) else decide (1 ≤ count683 b))) else (if i < 686 then (if i < 685 then decide (2 ≤ count683 b) else decide (3 ≤ count683 b)) else (if i < 687 then decide (4 ≤ count683 b) else decide (5 ≤ count683 b)))) else (if i < 691 then (if i < 689 then decide (6 ≤ count683 b) else (if i < 690 then decide (7 ≤ count683 b) else decide (8 ≤ count683 b))) else (if i < 693 then (if i < 692 then decide (1 ≤ count691 b) else decide (2 ≤ count691 b)) else (if i < 694 then decide (3 ≤ count691 b) else decide (4 ≤ count691 b))))) else (if i < 702 then (if i < 698 then (if i < 696 then decide (5 ≤ count691 b) else (if i < 697 then decide (6 ≤ count691 b) else decide (7 ≤ count691 b))) else (if i < 700 then (if i < 699 then decide (8 ≤ count691 b) else decide (9 ≤ count691 b)) else (if i < 701 then decide (10 ≤ count691 b) else decide (11 ≤ count691 b)))) else (if i < 705 then (if i < 703 then decide (12 ≤ count691 b) else (if i < 704 then decide (13 ≤ count691 b) else decide (14 ≤ count691 b))) else (if i < 707 then (if i < 706 then decide (15 ≤ count691 b) else decide (1 ≤ count706 b)) else (if i < 708 then decide (2 ≤ count706 b) else decide (1 ≤ count708 b)))))) else (if i < 723 then (if i < 716 then (if i < 712 then (if i < 710 then decide (2 ≤ count708 b) else (if i < 711 then decide (1 ≤ count710 b) else decide (2 ≤ count710 b))) else (if i < 714 then (if i < 713 then decide (3 ≤ count710 b) else decide (4 ≤ count710 b)) else (if i < 715 then decide (1 ≤ count714 b) else decide (2 ≤ count714 b)))) else (if i < 719 then (if i < 717 then decide (1 ≤ count716 b) else (if i < 718 then decide (2 ≤ count716 b) else decide (1 ≤ count718 b))) else (if i < 721 then (if i < 720 then decide (2 ≤ count718 b) else decide (3 ≤ count718 b)) else (if i < 722 then decide (4 ≤ count718 b) else decide (1 ≤ count722 b))))) else (if i < 730 then (if i < 726 then (if i < 724 then decide (2 ≤ count722 b) else (if i < 725 then decide (3 ≤ count722 b) else decide (4 ≤ count722 b))) else (if i < 728 then (if i < 727 then decide (5 ≤ count722 b) else decide (6 ≤ count722 b)) else (if i < 729 then decide (7 ≤ count722 b) else decide (8 ≤ count722 b)))) else (if i < 733 then (if i < 731 then decide (1 ≤ count730 b) else (if i < 732 then decide (2 ≤ count730 b) else decide (1 ≤ count732 b))) else (if i < 735 then (if i < 734 then decide (2 ≤ count732 b) else decide (1 ≤ count734 b)) else (if i < 736 then decide (2 ≤ count734 b) else decide (3 ≤ count734 b))))))) else (if i < 765 then (if i < 751 then (if i < 744 then (if i < 740 then (if i < 738 then decide (4 ≤ count734 b) else (if i < 739 then decide (1 ≤ count738 b) else decide (2 ≤ count738 b))) else (if i < 742 then (if i < 741 then decide (1 ≤ count740 b) else decide (2 ≤ count740 b)) else (if i < 743 then decide (1 ≤ count742 b) else decide (2 ≤ count742 b)))) else (if i < 747 then (if i < 745 then decide (3 ≤ count742 b) else (if i < 746 then decide (4 ≤ count742 b) else decide (1 ≤ count746 b))) else (if i < 749 then (if i < 748 then decide (2 ≤ count746 b) else decide (3 ≤ count746 b)) else (if i < 750 then decide (4 ≤ count746 b) else decide (5 ≤ count746 b))))) else (if i < 758 then (if i < 754 then (if i < 752 then decide (6 ≤ count746 b) else (if i < 753 then decide (7 ≤ count746 b) else decide (8 ≤ count746 b))) else (if i < 756 then (if i < 755 then decide (1 ≤ count754 b) else decide (2 ≤ count754 b)) else (if i < 757 then decide (3 ≤ count754 b) else decide (4 ≤ count754 b)))) else (if i < 761 then (if i < 759 then decide (5 ≤ count754 b) else (if i < 760 then decide (6 ≤ count754 b) else decide (7 ≤ count754 b))) else (if i < 763 then (if i < 762 then decide (8 ≤ count754 b) else decide (9 ≤ count754 b)) else (if i < 764 then decide (10 ≤ count754 b) else decide (11 ≤ count754 b)))))) else (if i < 779 then (if i < 772 then (if i < 768 then (if i < 766 then decide (12 ≤ count754 b) else (if i < 767 then decide (13 ≤ count754 b) else decide (14 ≤ count754 b))) else (if i < 770 then (if i < 769 then decide (15 ≤ count754 b) else decide (16 ≤ count754 b)) else (if i < 771 then decide (1 ≤ count770 b) else decide (2 ≤ count770 b)))) else (if i < 775 then (if i < 773 then decide (3 ≤ count770 b) else (if i < 774 then decide (4 ≤ count770 b) else decide (5 ≤ count770 b))) else (if i < 777 then (if i < 776 then decide (6 ≤ count770 b) else decide (7 ≤ count770 b)) else (if i < 778 then decide (8 ≤ count770 b) else decide (9 ≤ count770 b))))) else (if i < 786 then (if i < 782 then (if i < 780 then decide (10 ≤ count770 b) else (if i < 781 then decide (11 ≤ count770 b) else decide (12 ≤ count770 b))) else (if i < 784 then (if i < 783 then decide (13 ≤ count770 b) else decide (14 ≤ count770 b)) else (if i < 785 then decide (15 ≤ count770 b) else decide (16 ≤ count770 b)))) else (if i < 790 then (if i < 788 then (if i < 787 then decide (17 ≤ count770 b) else decide (18 ≤ count770 b)) else (if i < 789 then decide (19 ≤ count770 b) else decide (20 ≤ count770 b))) else (if i < 792 then (if i < 791 then decide (21 ≤ count770 b) else decide (22 ≤ count770 b)) else (if i < 793 then decide (23 ≤ count770 b) else decide (24 ≤ count770 b)))))))) else (if i < 851 then (if i < 822 then (if i < 808 then (if i < 801 then (if i < 797 then (if i < 795 then decide (25 ≤ count770 b) else (if i < 796 then decide (26 ≤ count770 b) else decide (27 ≤ count770 b))) else (if i < 799 then (if i < 798 then decide (28 ≤ count770 b) else decide (29 ≤ count770 b)) else (if i < 800 then decide (30 ≤ count770 b) else decide (31 ≤ count770 b)))) else (if i < 804 then (if i < 802 then decide (1 ≤ count801 b) else (if i < 803 then decide (2 ≤ count801 b) else decide (3 ≤ count801 b))) else (if i < 806 then (if i < 805 then decide (4 ≤ count801 b) else decide (5 ≤ count801 b)) else (if i < 807 then decide (6 ≤ count801 b) else decide (7 ≤ count801 b))))) else (if i < 815 then (if i < 811 then (if i < 809 then decide (8 ≤ count801 b) else (if i < 810 then decide (9 ≤ count801 b) else decide (10 ≤ count801 b))) else (if i < 813 then (if i < 812 then decide (11 ≤ count801 b) else decide (12 ≤ count801 b)) else (if i < 814 then decide (13 ≤ count801 b) else decide (14 ≤ count801 b)))) else (if i < 818 then (if i < 816 then decide (15 ≤ count801 b) else (if i < 817 then decide (16 ≤ count801 b) else decide (17 ≤ count801 b))) else (if i < 820 then (if i < 819 then decide (18 ≤ count801 b) else decide (19 ≤ count801 b)) else (if i < 821 then decide (20 ≤ count801 b) else decide (21 ≤ count801 b)))))) else (if i < 836 then (if i < 829 then (if i < 825 then (if i < 823 then decide (22 ≤ count801 b) else (if i < 824 then decide (23 ≤ count801 b) else decide (24 ≤ count801 b))) else (if i < 827 then (if i < 826 then decide (25 ≤ count801 b) else decide (26 ≤ count801 b)) else (if i < 828 then decide (27 ≤ count801 b) else decide (28 ≤ count801 b)))) else (if i < 832 then (if i < 830 then decide (29 ≤ count801 b) else (if i < 831 then decide (30 ≤ count801 b) else decide (31 ≤ count801 b))) else (if i < 834 then (if i < 833 then decide (32 ≤ count801 b) else decide (33 ≤ count801 b)) else (if i < 835 then decide (34 ≤ count801 b) else decide (35 ≤ count801 b))))) else (if i < 843 then (if i < 839 then (if i < 837 then decide (36 ≤ count801 b) else (if i < 838 then decide (37 ≤ count801 b) else decide (38 ≤ count801 b))) else (if i < 841 then (if i < 840 then decide (39 ≤ count801 b) else decide (40 ≤ count801 b)) else (if i < 842 then decide (41 ≤ count801 b) else decide (42 ≤ count801 b)))) else (if i < 847 then (if i < 845 then (if i < 844 then decide (1 ≤ count843 b) else decide (2 ≤ count843 b)) else (if i < 846 then decide (1 ≤ count845 b) else decide (2 ≤ count845 b))) else (if i < 849 then (if i < 848 then decide (3 ≤ count845 b) else decide (1 ≤ count848 b)) else (if i < 850 then decide (2 ≤ count848 b) else decide (1 ≤ count850 b))))))) else (if i < 879 then (if i < 865 then (if i < 858 then (if i < 854 then (if i < 852 then decide (2 ≤ count850 b) else (if i < 853 then decide (1 ≤ count852 b) else decide (2 ≤ count852 b))) else (if i < 856 then (if i < 855 then decide (3 ≤ count852 b) else decide (4 ≤ count852 b)) else (if i < 857 then decide (1 ≤ count856 b) else decide (2 ≤ count856 b)))) else (if i < 861 then (if i < 859 then decide (3 ≤ count856 b) else (if i < 860 then decide (4 ≤ count856 b) else decide (5 ≤ count856 b))) else (if i < 863 then (if i < 862 then decide (6 ≤ count856 b) else decide (7 ≤ count856 b)) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b))))) else (if i < 872 then (if i < 868 then (if i < 866 then decide (1 ≤ count865 b) else (if i < 867 then decide (2 ≤ count865 b) else decide (1 ≤ count867 b))) else (if i < 870 then (if i < 869 then decide (2 ≤ count867 b) else decide (3 ≤ count867 b)) else (if i < 871 then decide (4 ≤ count867 b) else decide (1 ≤ count871 b)))) else (if i < 875 then (if i < 873 then decide (2 ≤ count871 b) else (if i < 874 then decide (1 ≤ count873 b) else decide (2 ≤ count873 b))) else (if i < 877 then (if i < 876 then decide (1 ≤ count875 b) else decide (2 ≤ count875 b)) else (if i < 878 then decide (3 ≤ count875 b) else decide (4 ≤ count875 b)))))) else (if i < 893 then (if i < 886 then (if i < 882 then (if i < 880 then decide (1 ≤ count879 b) else (if i < 881 then decide (2 ≤ count879 b) else decide (3 ≤ count879 b))) else (if i < 884 then (if i < 883 then decide (4 ≤ count879 b) else decide (5 ≤ count879 b)) else (if i < 885 then decide (6 ≤ count879 b) else decide (7 ≤ count879 b)))) else (if i < 889 then (if i < 887 then decide (8 ≤ count879 b) else (if i < 888 then decide (1 ≤ count887 b) else decide (2 ≤ count887 b))) else (if i < 891 then (if i < 890 then decide (3 ≤ count887 b) else decide (4 ≤ count887 b)) else (if i < 892 then decide (5 ≤ count887 b) else decide (6 ≤ count887 b))))) else (if i < 900 then (if i < 896 then (if i < 894 then decide (7 ≤ count887 b) else (if i < 895 then decide (8 ≤ count887 b) else decide (9 ≤ count887 b))) else (if i < 898 then (if i < 897 then decide (10 ≤ count887 b) else decide (11 ≤ count887 b)) else (if i < 899 then decide (12 ≤ count887 b) else decide (13 ≤ count887 b)))) else (if i < 904 then (if i < 902 then (if i < 901 then decide (14 ≤ count887 b) else decide (15 ≤ count887 b)) else (if i < 903 then decide (1 ≤ count902 b) else decide (2 ≤ count902 b))) else (if i < 906 then (if i < 905 then decide (1 ≤ count904 b) else decide (2 ≤ count904 b)) else (if i < 907 then decide (1 ≤ count906 b) else decide (2 ≤ count906 b))))))))))) else (if i < 1362 then (if i < 1135 then (if i < 1021 then (if i < 964 then (if i < 936 then (if i < 922 then (if i < 915 then (if i < 911 then (if i < 909 then decide (3 ≤ count906 b) else (if i < 910 then decide (4 ≤ count906 b) else decide (1 ≤ count910 b))) else (if i < 913 then (if i < 912 then decide (2 ≤ count910 b) else decide (1 ≤ count912 b)) else (if i < 914 then decide (2 ≤ count912 b) else decide (1 ≤ count914 b)))) else (if i < 918 then (if i < 916 then decide (2 ≤ count914 b) else (if i < 917 then decide (3 ≤ count914 b) else decide (4 ≤ count914 b))) else (if i < 920 then (if i < 919 then decide (1 ≤ count918 b) else decide (2 ≤ count918 b)) else (if i < 921 then decide (3 ≤ count918 b) else decide (4 ≤ count918 b))))) else (if i < 929 then (if i < 925 then (if i < 923 then decide (5 ≤ count918 b) else (if i < 924 then decide (6 ≤ count918 b) else decide (7 ≤ count918 b))) else (if i < 927 then (if i < 926 then decide (8 ≤ count918 b) else decide (1 ≤ count926 b)) else (if i < 928 then decide (2 ≤ count926 b) else decide (1 ≤ count928 b)))) else (if i < 932 then (if i < 930 then decide (2 ≤ count928 b) else (if i < 931 then decide (1 ≤ count930 b) else decide (2 ≤ count930 b))) else (if i < 934 then (if i < 933 then decide (3 ≤ count930 b) else decide (4 ≤ count930 b)) else (if i < 935 then decide (1 ≤ count934 b) else decide (2 ≤ count934 b)))))) else (if i < 950 then (if i < 943 then (if i < 939 then (if i < 937 then decide (1 ≤ count936 b) else (if i < 938 then decide (2 ≤ count936 b) else decide (1 ≤ count938 b))) else (if i < 941 then (if i < 940 then decide (2 ≤ count938 b) else decide (3 ≤ count938 b)) else (if i < 942 then decide (4 ≤ count938 b) else decide (1 ≤ count942 b)))) else (if i < 946 then (if i < 944 then decide (2 ≤ count942 b) else (if i < 945 then decide (3 ≤ count942 b) else decide (4 ≤ count942 b))) else (if i < 948 then (if i < 947 then decide (5 ≤ count942 b) else decide (6 ≤ count942 b)) else (if i < 949 then decide (7 ≤ count942 b) else decide (8 ≤ count942 b))))) else (if i < 957 then (if i < 953 then (if i < 951 then decide (1 ≤ count950 b) else (if i < 952 then decide (2 ≤ count950 b) else decide (3 ≤ count950 b))) else (if i < 955 then (if i < 954 then decide (4 ≤ count950 b) else decide (5 ≤ count950 b)) else (if i < 956 then decide (6 ≤ count950 b) else decide (7 ≤ count950 b)))) else (if i < 960 then (if i < 958 then decide (8 ≤ count950 b) else (if i < 959 then decide (9 ≤ count950 b) else decide (10 ≤ count950 b))) else (if i < 962 then (if i < 961 then decide (11 ≤ count950 b) else decide (12 ≤ count950 b)) else (if i < 963 then decide (13 ≤ count950 b) else decide (14 ≤ count950 b))))))) else (if i < 992 then (if i < 978 then (if i < 971 then (if i < 967 then (if i < 965 then decide (15 ≤ count950 b) else (if i < 966 then decide (16 ≤ count950 b) else decide (1 ≤ count966 b))) else (if i < 969 then (if i < 968 then decide (2 ≤ count966 b) else decide (3 ≤ count966 b)) else (if i < 970 then decide (4 ≤ count966 b) else decide (5 ≤ count966 b)))) else (if i < 974 then (if i < 972 then decide (6 ≤ count966 b) else (if i < 973 then decide (7 ≤ count966 b) else decide (8 ≤ count966 b))) else (if i < 976 then (if i < 975 then decide (9 ≤ count966 b) else decide (10 ≤ count966 b)) else (if i < 977 then decide (11 ≤ count966 b) else decide (12 ≤ count966 b))))) else (if i < 985 then (if i < 981 then (if i < 979 then decide (13 ≤ count966 b) else (if i < 980 then decide (14 ≤ count966 b) else decide (15 ≤ count966 b))) else (if i < 983 then (if i < 982 then decide (16 ≤ count966 b) else decide (17 ≤ count966 b)) else (if i < 984 then decide (18 ≤ count966 b) else decide (19 ≤ count966 b)))) else (if i < 988 then (if i < 986 then decide (20 ≤ count966 b) else (if i < 987 then decide (21 ≤ count966 b) else decide (22 ≤ count966 b))) else (if i < 990 then (if i < 989 then decide (1 ≤ count988 b) else decide (2 ≤ count988 b)) else (if i < 991 then decide (1 ≤ count990 b) else decide (2 ≤ count990 b)))))) else (if i < 1006 then (if i < 999 then (if i < 995 then (if i < 993 then decide (3 ≤ count990 b) else (if i < 994 then decide (1 ≤ count993 b) else decide (2 ≤ count993 b))) else (if i < 997 then (if i < 996 then decide (1 ≤ count995 b) else decide (2 ≤ count995 b)) else (if i < 998 then decide (1 ≤ count997 b) else decide (2 ≤ count997 b)))) else (if i < 1002 then (if i < 1000 then decide (3 ≤ count997 b) else (if i < 1001 then decide (4 ≤ count997 b) else decide (1 ≤ count1001 b))) else (if i < 1004 then (if i < 1003 then decide (2 ≤ count1001 b) else decide (3 ≤ count1001 b)) else (if i < 1005 then decide (4 ≤ count1001 b) else decide (5 ≤ count1001 b))))) else (if i < 1013 then (if i < 1009 then (if i < 1007 then decide (6 ≤ count1001 b) else (if i < 1008 then decide (7 ≤ count1001 b) else decide (1 ≤ count1008 b))) else (if i < 1011 then (if i < 1010 then decide (2 ≤ count1008 b) else decide (1 ≤ count1010 b)) else (if i < 1012 then decide (2 ≤ count1010 b) else decide (1 ≤ count1012 b)))) else (if i < 1017 then (if i < 1015 then (if i < 1014 then decide (2 ≤ count1012 b) else decide (3 ≤ count1012 b)) else (if i < 1016 then decide (4 ≤ count1012 b) else decide (1 ≤ count1016 b))) else (if i < 1019 then (if i < 1018 then decide (2 ≤ count1016 b) else decide (1 ≤ count1018 b)) else (if i < 1020 then decide (2 ≤ count1018 b) else decide (1 ≤ count1020 b)))))))) else (if i < 1078 then (if i < 1049 then (if i < 1035 then (if i < 1028 then (if i < 1024 then (if i < 1022 then decide (2 ≤ count1020 b) else (if i < 1023 then decide (3 ≤ count1020 b) else decide (4 ≤ count1020 b))) else (if i < 1026 then (if i < 1025 then decide (1 ≤ count1024 b) else decide (2 ≤ count1024 b)) else (if i < 1027 then decide (3 ≤ count1024 b) else decide (4 ≤ count1024 b)))) else (if i < 1031 then (if i < 1029 then decide (5 ≤ count1024 b) else (if i < 1030 then decide (6 ≤ count1024 b) else decide (7 ≤ count1024 b))) else (if i < 1033 then (if i < 1032 then decide (8 ≤ count1024 b) else decide (1 ≤ count1032 b)) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (3 ≤ count1032 b))))) else (if i < 1042 then (if i < 1038 then (if i < 1036 then decide (4 ≤ count1032 b) else (if i < 1037 then decide (5 ≤ count1032 b) else decide (6 ≤ count1032 b))) else (if i < 1040 then (if i < 1039 then decide (7 ≤ count1032 b) else decide (8 ≤ count1032 b)) else (if i < 1041 then decide (9 ≤ count1032 b) else decide (10 ≤ count1032 b)))) else (if i < 1045 then (if i < 1043 then decide (11 ≤ count1032 b) else (if i < 1044 then decide (12 ≤ count1032 b) else decide (13 ≤ count1032 b))) else (if i < 1047 then (if i < 1046 then decide (14 ≤ count1032 b) else decide (15 ≤ count1032 b)) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b)))))) else (if i < 1063 then (if i < 1056 then (if i < 1052 then (if i < 1050 then decide (1 ≤ count1049 b) else (if i < 1051 then decide (2 ≤ count1049 b) else decide (1 ≤ count1051 b))) else (if i < 1054 then (if i < 1053 then decide (2 ≤ count1051 b) else decide (3 ≤ count1051 b)) else (if i < 1055 then decide (4 ≤ count1051 b) else decide (1 ≤ count1055 b)))) else (if i < 1059 then (if i < 1057 then decide (2 ≤ count1055 b) else (if i < 1058 then decide (1 ≤ count1057 b) else decide (2 ≤ count1057 b))) else (if i < 1061 then (if i < 1060 then decide (1 ≤ count1059 b) else decide (2 ≤ count1059 b)) else (if i < 1062 then decide (3 ≤ count1059 b) else decide (4 ≤ count1059 b))))) else (if i < 1070 then (if i < 1066 then (if i < 1064 then decide (1 ≤ count1063 b) else (if i < 1065 then decide (2 ≤ count1063 b) else decide (3 ≤ count1063 b))) else (if i < 1068 then (if i < 1067 then decide (4 ≤ count1063 b) else decide (5 ≤ count1063 b)) else (if i < 1069 then decide (6 ≤ count1063 b) else decide (7 ≤ count1063 b)))) else (if i < 1074 then (if i < 1072 then (if i < 1071 then decide (8 ≤ count1063 b) else decide (1 ≤ count1071 b)) else (if i < 1073 then decide (2 ≤ count1071 b) else decide (1 ≤ count1073 b))) else (if i < 1076 then (if i < 1075 then decide (2 ≤ count1073 b) else decide (1 ≤ count1075 b)) else (if i < 1077 then decide (2 ≤ count1075 b) else decide (3 ≤ count1075 b))))))) else (if i < 1106 then (if i < 1092 then (if i < 1085 then (if i < 1081 then (if i < 1079 then decide (4 ≤ count1075 b) else (if i < 1080 then decide (1 ≤ count1079 b) else decide (2 ≤ count1079 b))) else (if i < 1083 then (if i < 1082 then decide (1 ≤ count1081 b) else decide (2 ≤ count1081 b)) else (if i < 1084 then decide (1 ≤ count1083 b) else decide (2 ≤ count1083 b)))) else (if i < 1088 then (if i < 1086 then decide (3 ≤ count1083 b) else (if i < 1087 then decide (4 ≤ count1083 b) else decide (1 ≤ count1087 b))) else (if i < 1090 then (if i < 1089 then decide (2 ≤ count1087 b) else decide (3 ≤ count1087 b)) else (if i < 1091 then decide (4 ≤ count1087 b) else decide (5 ≤ count1087 b))))) else (if i < 1099 then (if i < 1095 then (if i < 1093 then decide (6 ≤ count1087 b) else (if i < 1094 then decide (7 ≤ count1087 b) else decide (8 ≤ count1087 b))) else (if i < 1097 then (if i < 1096 then decide (1 ≤ count1095 b) else decide (2 ≤ count1095 b)) else (if i < 1098 then decide (3 ≤ count1095 b) else decide (4 ≤ count1095 b)))) else (if i < 1102 then (if i < 1100 then decide (5 ≤ count1095 b) else (if i < 1101 then decide (6 ≤ count1095 b) else decide (7 ≤ count1095 b))) else (if i < 1104 then (if i < 1103 then decide (8 ≤ count1095 b) else decide (9 ≤ count1095 b)) else (if i < 1105 then decide (10 ≤ count1095 b) else decide (11 ≤ count1095 b)))))) else (if i < 1120 then (if i < 1113 then (if i < 1109 then (if i < 1107 then decide (12 ≤ count1095 b) else (if i < 1108 then decide (13 ≤ count1095 b) else decide (14 ≤ count1095 b))) else (if i < 1111 then (if i < 1110 then decide (15 ≤ count1095 b) else decide (16 ≤ count1095 b)) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b)))) else (if i < 1116 then (if i < 1114 then decide (3 ≤ count1111 b) else (if i < 1115 then decide (4 ≤ count1111 b) else decide (5 ≤ count1111 b))) else (if i < 1118 then (if i < 1117 then decide (6 ≤ count1111 b) else decide (7 ≤ count1111 b)) else (if i < 1119 then decide (8 ≤ count1111 b) else decide (9 ≤ count1111 b))))) else (if i < 1127 then (if i < 1123 then (if i < 1121 then decide (10 ≤ count1111 b) else (if i < 1122 then decide (11 ≤ count1111 b) else decide (12 ≤ count1111 b))) else (if i < 1125 then (if i < 1124 then decide (13 ≤ count1111 b) else decide (14 ≤ count1111 b)) else (if i < 1126 then decide (15 ≤ count1111 b) else decide (16 ≤ count1111 b)))) else (if i < 1131 then (if i < 1129 then (if i < 1128 then decide (17 ≤ count1111 b) else decide (18 ≤ count1111 b)) else (if i < 1130 then decide (19 ≤ count1111 b) else decide (20 ≤ count1111 b))) else (if i < 1133 then (if i < 1132 then decide (21 ≤ count1111 b) else decide (22 ≤ count1111 b)) else (if i < 1134 then decide (1 ≤ count1133 b) else decide (2 ≤ count1133 b))))))))) else (if i < 1248 then (if i < 1191 then (if i < 1163 then (if i < 1149 then (if i < 1142 then (if i < 1138 then (if i < 1136 then decide (3 ≤ count1133 b) else (if i < 1137 then decide (4 ≤ count1133 b) else decide (5 ≤ count1133 b))) else (if i < 1140 then (if i < 1139 then decide (6 ≤ count1133 b) else decide (7 ≤ count1133 b)) else (if i < 1141 then decide (8 ≤ count1133 b) else decide (9 ≤ count1133 b)))) else (if i < 1145 then (if i < 1143 then decide (10 ≤ count1133 b) else (if i < 1144 then decide (11 ≤ count1133 b) else decide (12 ≤ count1133 b))) else (if i < 1147 then (if i < 1146 then decide (13 ≤ count1133 b) else decide (14 ≤ count1133 b)) else (if i < 1148 then decide (15 ≤ count1133 b) else decide (16 ≤ count1133 b))))) else (if i < 1156 then (if i < 1152 then (if i < 1150 then decide (17 ≤ count1133 b) else (if i < 1151 then decide (18 ≤ count1133 b) else decide (19 ≤ count1133 b))) else (if i < 1154 then (if i < 1153 then decide (20 ≤ count1133 b) else decide (21 ≤ count1133 b)) else (if i < 1155 then decide (22 ≤ count1133 b) else decide (1 ≤ count1155 b)))) else (if i < 1159 then (if i < 1157 then decide (2 ≤ count1155 b) else (if i < 1158 then decide (1 ≤ count1157 b) else decide (2 ≤ count1157 b))) else (if i < 1161 then (if i < 1160 then decide (3 ≤ count1157 b) else decide (1 ≤ count1160 b)) else (if i < 1162 then decide (2 ≤ count1160 b) else decide (1 ≤ count1162 b)))))) else (if i < 1177 then (if i < 1170 then (if i < 1166 then (if i < 1164 then decide (2 ≤ count1162 b) else (if i < 1165 then decide (1 ≤ count1164 b) else decide (2 ≤ count1164 b))) else (if i < 1168 then (if i < 1167 then decide (3 ≤ count1164 b) else decide (4 ≤ count1164 b)) else (if i < 1169 then decide (1 ≤ count1168 b) else decide (2 ≤ count1168 b)))) else (if i < 1173 then (if i < 1171 then decide (3 ≤ count1168 b) else (if i < 1172 then decide (4 ≤ count1168 b) else decide (5 ≤ count1168 b))) else (if i < 1175 then (if i < 1174 then decide (6 ≤ count1168 b) else decide (7 ≤ count1168 b)) else (if i < 1176 then decide (1 ≤ count1175 b) else decide (2 ≤ count1175 b))))) else (if i < 1184 then (if i < 1180 then (if i < 1178 then decide (1 ≤ count1177 b) else (if i < 1179 then decide (2 ≤ count1177 b) else decide (1 ≤ count1179 b))) else (if i < 1182 then (if i < 1181 then decide (2 ≤ count1179 b) else decide (3 ≤ count1179 b)) else (if i < 1183 then decide (4 ≤ count1179 b) else decide (1 ≤ count1183 b)))) else (if i < 1187 then (if i < 1185 then decide (2 ≤ count1183 b) else (if i < 1186 then decide (1 ≤ count1185 b) else decide (2 ≤ count1185 b))) else (if i < 1189 then (if i < 1188 then decide (1 ≤ count1187 b) else decide (2 ≤ count1187 b)) else (if i < 1190 then decide (3 ≤ count1187 b) else decide (4 ≤ count1187 b))))))) else (if i < 1219 then (if i < 1205 then (if i < 1198 then (if i < 1194 then (if i < 1192 then decide (1 ≤ count1191 b) else (if i < 1193 then decide (2 ≤ count1191 b) else decide (3 ≤ count1191 b))) else (if i < 1196 then (if i < 1195 then decide (4 ≤ count1191 b) else decide (5 ≤ count1191 b)) else (if i < 1197 then decide (6 ≤ count1191 b) else decide (7 ≤ count1191 b)))) else (if i < 1201 then (if i < 1199 then decide (8 ≤ count1191 b) else (if i < 1200 then decide (1 ≤ count1199 b) else decide (2 ≤ count1199 b))) else (if i < 1203 then (if i < 1202 then decide (3 ≤ count1199 b) else decide (4 ≤ count1199 b)) else (if i < 1204 then decide (5 ≤ count1199 b) else decide (6 ≤ count1199 b))))) else (if i < 1212 then (if i < 1208 then (if i < 1206 then decide (7 ≤ count1199 b) else (if i < 1207 then decide (8 ≤ count1199 b) else decide (9 ≤ count1199 b))) else (if i < 1210 then (if i < 1209 then decide (10 ≤ count1199 b) else decide (11 ≤ count1199 b)) else (if i < 1211 then decide (12 ≤ count1199 b) else decide (13 ≤ count1199 b)))) else (if i < 1215 then (if i < 1213 then decide (14 ≤ count1199 b) else (if i < 1214 then decide (15 ≤ count1199 b) else decide (1 ≤ count1214 b))) else (if i < 1217 then (if i < 1216 then decide (2 ≤ count1214 b) else decide (1 ≤ count1216 b)) else (if i < 1218 then decide (2 ≤ count1216 b) else decide (1 ≤ count1218 b)))))) else (if i < 1233 then (if i < 1226 then (if i < 1222 then (if i < 1220 then decide (2 ≤ count1218 b) else (if i < 1221 then decide (3 ≤ count1218 b) else decide (4 ≤ count1218 b))) else (if i < 1224 then (if i < 1223 then decide (1 ≤ count1222 b) else decide (2 ≤ count1222 b)) else (if i < 1225 then decide (1 ≤ count1224 b) else decide (2 ≤ count1224 b)))) else (if i < 1229 then (if i < 1227 then decide (1 ≤ count1226 b) else (if i < 1228 then decide (2 ≤ count1226 b) else decide (3 ≤ count1226 b))) else (if i < 1231 then (if i < 1230 then decide (4 ≤ count1226 b) else decide (1 ≤ count1230 b)) else (if i < 1232 then decide (2 ≤ count1230 b) else decide (3 ≤ count1230 b))))) else (if i < 1240 then (if i < 1236 then (if i < 1234 then decide (4 ≤ count1230 b) else (if i < 1235 then decide (5 ≤ count1230 b) else decide (6 ≤ count1230 b))) else (if i < 1238 then (if i < 1237 then decide (7 ≤ count1230 b) else decide (8 ≤ count1230 b)) else (if i < 1239 then decide (1 ≤ count1238 b) else decide (2 ≤ count1238 b)))) else (if i < 1244 then (if i < 1242 then (if i < 1241 then decide (1 ≤ count1240 b) else decide (2 ≤ count1240 b)) else (if i < 1243 then decide (1 ≤ count1242 b) else decide (2 ≤ count1242 b))) else (if i < 1246 then (if i < 1245 then decide (3 ≤ count1242 b) else decide (4 ≤ count1242 b)) else (if i < 1247 then decide (1 ≤ count1246 b) else decide (2 ≤ count1246 b)))))))) else (if i < 1305 then (if i < 1276 then (if i < 1262 then (if i < 1255 then (if i < 1251 then (if i < 1249 then decide (1 ≤ count1248 b) else (if i < 1250 then decide (2 ≤ count1248 b) else decide (1 ≤ count1250 b))) else (if i < 1253 then (if i < 1252 then decide (2 ≤ count1250 b) else decide (3 ≤ count1250 b)) else (if i < 1254 then decide (4 ≤ count1250 b) else decide (1 ≤ count1254 b)))) else (if i < 1258 then (if i < 1256 then decide (2 ≤ count1254 b) else (if i < 1257 then decide (3 ≤ count1254 b) else decide (4 ≤ count1254 b))) else (if i < 1260 then (if i < 1259 then decide (5 ≤ count1254 b) else decide (6 ≤ count1254 b)) else (if i < 1261 then decide (7 ≤ count1254 b) else decide (8 ≤ count1254 b))))) else (if i < 1269 then (if i < 1265 then (if i < 1263 then decide (1 ≤ count1262 b) else (if i < 1264 then decide (2 ≤ count1262 b) else decide (3 ≤ count1262 b))) else (if i < 1267 then (if i < 1266 then decide (4 ≤ count1262 b) else decide (5 ≤ count1262 b)) else (if i < 1268 then decide (6 ≤ count1262 b) else decide (7 ≤ count1262 b)))) else (if i < 1272 then (if i < 1270 then decide (8 ≤ count1262 b) else (if i < 1271 then decide (9 ≤ count1262 b) else decide (10 ≤ count1262 b))) else (if i < 1274 then (if i < 1273 then decide (11 ≤ count1262 b) else decide (12 ≤ count1262 b)) else (if i < 1275 then decide (13 ≤ count1262 b) else decide (14 ≤ count1262 b)))))) else (if i < 1290 then (if i < 1283 then (if i < 1279 then (if i < 1277 then decide (15 ≤ count1262 b) else (if i < 1278 then decide (16 ≤ count1262 b) else decide (1 ≤ count1278 b))) else (if i < 1281 then (if i < 1280 then decide (2 ≤ count1278 b) else decide (3 ≤ count1278 b)) else (if i < 1282 then decide (4 ≤ count1278 b) else decide (5 ≤ count1278 b)))) else (if i < 1286 then (if i < 1284 then decide (6 ≤ count1278 b) else (if i < 1285 then decide (7 ≤ count1278 b) else decide (8 ≤ count1278 b))) else (if i < 1288 then (if i < 1287 then decide (9 ≤ count1278 b) else decide (10 ≤ count1278 b)) else (if i < 1289 then decide (11 ≤ count1278 b) else decide (12 ≤ count1278 b))))) else (if i < 1297 then (if i < 1293 then (if i < 1291 then decide (13 ≤ count1278 b) else (if i < 1292 then decide (14 ≤ count1278 b) else decide (15 ≤ count1278 b))) else (if i < 1295 then (if i < 1294 then decide (16 ≤ count1278 b) else decide (17 ≤ count1278 b)) else (if i < 1296 then decide (18 ≤ count1278 b) else decide (19 ≤ count1278 b)))) else (if i < 1301 then (if i < 1299 then (if i < 1298 then decide (20 ≤ count1278 b) else decide (21 ≤ count1278 b)) else (if i < 1300 then decide (22 ≤ count1278 b) else decide (23 ≤ count1278 b))) else (if i < 1303 then (if i < 1302 then decide (24 ≤ count1278 b) else decide (25 ≤ count1278 b)) else (if i < 1304 then decide (26 ≤ count1278 b) else decide (27 ≤ count1278 b))))))) else (if i < 1333 then (if i < 1319 then (if i < 1312 then (if i < 1308 then (if i < 1306 then decide (28 ≤ count1278 b) else (if i < 1307 then decide (29 ≤ count1278 b) else decide (30 ≤ count1278 b))) else (if i < 1310 then (if i < 1309 then decide (31 ≤ count1278 b) else decide (1 ≤ count1309 b)) else (if i < 1311 then decide (2 ≤ count1309 b) else decide (1 ≤ count1311 b)))) else (if i < 1315 then (if i < 1313 then decide (2 ≤ count1311 b) else (if i < 1314 then decide (3 ≤ count1311 b) else decide (1 ≤ count1314 b))) else (if i < 1317 then (if i < 1316 then decide (2 ≤ count1314 b) else decide (1 ≤ count1316 b)) else (if i < 1318 then decide (2 ≤ count1316 b) else decide (1 ≤ count1318 b))))) else (if i < 1326 then (if i < 1322 then (if i < 1320 then decide (2 ≤ count1318 b) else (if i < 1321 then decide (3 ≤ count1318 b) else decide (4 ≤ count1318 b))) else (if i < 1324 then (if i < 1323 then decide (1 ≤ count1322 b) else decide (2 ≤ count1322 b)) else (if i < 1325 then decide (3 ≤ count1322 b) else decide (4 ≤ count1322 b)))) else (if i < 1329 then (if i < 1327 then decide (5 ≤ count1322 b) else (if i < 1328 then decide (6 ≤ count1322 b) else decide (7 ≤ count1322 b))) else (if i < 1331 then (if i < 1330 then decide (1 ≤ count1329 b) else decide (2 ≤ count1329 b)) else (if i < 1332 then decide (1 ≤ count1331 b) else decide (2 ≤ count1331 b)))))) else (if i < 1347 then (if i < 1340 then (if i < 1336 then (if i < 1334 then decide (1 ≤ count1333 b) else (if i < 1335 then decide (2 ≤ count1333 b) else decide (3 ≤ count1333 b))) else (if i < 1338 then (if i < 1337 then decide (4 ≤ count1333 b) else decide (1 ≤ count1337 b)) else (if i < 1339 then decide (2 ≤ count1337 b) else decide (1 ≤ count1339 b)))) else (if i < 1343 then (if i < 1341 then decide (2 ≤ count1339 b) else (if i < 1342 then decide (1 ≤ count1341 b) else decide (2 ≤ count1341 b))) else (if i < 1345 then (if i < 1344 then decide (3 ≤ count1341 b) else decide (4 ≤ count1341 b)) else (if i < 1346 then decide (1 ≤ count1345 b) else decide (2 ≤ count1345 b))))) else (if i < 1354 then (if i < 1350 then (if i < 1348 then decide (3 ≤ count1345 b) else (if i < 1349 then decide (4 ≤ count1345 b) else decide (5 ≤ count1345 b))) else (if i < 1352 then (if i < 1351 then decide (6 ≤ count1345 b) else decide (7 ≤ count1345 b)) else (if i < 1353 then decide (8 ≤ count1345 b) else decide (1 ≤ count1353 b)))) else (if i < 1358 then (if i < 1356 then (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b)) else (if i < 1357 then decide (4 ≤ count1353 b) else decide (5 ≤ count1353 b))) else (if i < 1360 then (if i < 1359 then decide (6 ≤ count1353 b) else decide (7 ≤ count1353 b)) else (if i < 1361 then decide (8 ≤ count1353 b) else decide (9 ≤ count1353 b)))))))))) else (if i < 1589 then (if i < 1475 then (if i < 1418 then (if i < 1390 then (if i < 1376 then (if i < 1369 then (if i < 1365 then (if i < 1363 then decide (10 ≤ count1353 b) else (if i < 1364 then decide (11 ≤ count1353 b) else decide (12 ≤ count1353 b))) else (if i < 1367 then (if i < 1366 then decide (13 ≤ count1353 b) else decide (14 ≤ count1353 b)) else (if i < 1368 then decide (15 ≤ count1353 b) else decide (1 ≤ count1368 b)))) else (if i < 1372 then (if i < 1370 then decide (2 ≤ count1368 b) else (if i < 1371 then decide (1 ≤ count1370 b) else decide (2 ≤ count1370 b))) else (if i < 1374 then (if i < 1373 then decide (1 ≤ count1372 b) else decide (2 ≤ count1372 b)) else (if i < 1375 then decide (3 ≤ count1372 b) else decide (4 ≤ count1372 b))))) else (if i < 1383 then (if i < 1379 then (if i < 1377 then decide (1 ≤ count1376 b) else (if i < 1378 then decide (2 ≤ count1376 b) else decide (1 ≤ count1378 b))) else (if i < 1381 then (if i < 1380 then decide (2 ≤ count1378 b) else decide (1 ≤ count1380 b)) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (3 ≤ count1380 b)))) else (if i < 1386 then (if i < 1384 then decide (4 ≤ count1380 b) else (if i < 1385 then decide (1 ≤ count1384 b) else decide (2 ≤ count1384 b))) else (if i < 1388 then (if i < 1387 then decide (3 ≤ count1384 b) else decide (4 ≤ count1384 b)) else (if i < 1389 then decide (5 ≤ count1384 b) else decide (6 ≤ count1384 b)))))) else (if i < 1404 then (if i < 1397 then (if i < 1393 then (if i < 1391 then decide (7 ≤ count1384 b) else (if i < 1392 then decide (8 ≤ count1384 b) else decide (1 ≤ count1392 b))) else (if i < 1395 then (if i < 1394 then decide (2 ≤ count1392 b) else decide (1 ≤ count1394 b)) else (if i < 1396 then decide (2 ≤ count1394 b) else decide (1 ≤ count1396 b)))) else (if i < 1400 then (if i < 1398 then decide (2 ≤ count1396 b) else (if i < 1399 then decide (3 ≤ count1396 b) else decide (4 ≤ count1396 b))) else (if i < 1402 then (if i < 1401 then decide (1 ≤ count1400 b) else decide (2 ≤ count1400 b)) else (if i < 1403 then decide (1 ≤ count1402 b) else decide (2 ≤ count1402 b))))) else (if i < 1411 then (if i < 1407 then (if i < 1405 then decide (1 ≤ count1404 b) else (if i < 1406 then decide (2 ≤ count1404 b) else decide (3 ≤ count1404 b))) else (if i < 1409 then (if i < 1408 then decide (4 ≤ count1404 b) else decide (1 ≤ count1408 b)) else (if i < 1410 then decide (2 ≤ count1408 b) else decide (3 ≤ count1408 b)))) else (if i < 1414 then (if i < 1412 then decide (4 ≤ count1408 b) else (if i < 1413 then decide (5 ≤ count1408 b) else decide (6 ≤ count1408 b))) else (if i < 1416 then (if i < 1415 then decide (7 ≤ count1408 b) else decide (8 ≤ count1408 b)) else (if i < 1417 then decide (1 ≤ count1416 b) else decide (2 ≤ count1416 b))))))) else (if i < 1446 then (if i < 1432 then (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (3 ≤ count1416 b) else (if i < 1420 then decide (4 ≤ count1416 b) else decide (5 ≤ count1416 b))) else (if i < 1423 then (if i < 1422 then decide (6 ≤ count1416 b) else decide (7 ≤ count1416 b)) else (if i < 1424 then decide (8 ≤ count1416 b) else decide (9 ≤ count1416 b)))) else (if i < 1428 then (if i < 1426 then decide (10 ≤ count1416 b) else (if i < 1427 then decide (11 ≤ count1416 b) else decide (12 ≤ count1416 b))) else (if i < 1430 then (if i < 1429 then decide (13 ≤ count1416 b) else decide (14 ≤ count1416 b)) else (if i < 1431 then decide (15 ≤ count1416 b) else decide (16 ≤ count1416 b))))) else (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (1 ≤ count1432 b) else (if i < 1434 then decide (2 ≤ count1432 b) else decide (3 ≤ count1432 b))) else (if i < 1437 then (if i < 1436 then decide (4 ≤ count1432 b) else decide (5 ≤ count1432 b)) else (if i < 1438 then decide (6 ≤ count1432 b) else decide (7 ≤ count1432 b)))) else (if i < 1442 then (if i < 1440 then decide (8 ≤ count1432 b) else (if i < 1441 then decide (9 ≤ count1432 b) else decide (10 ≤ count1432 b))) else (if i < 1444 then (if i < 1443 then decide (11 ≤ count1432 b) else decide (12 ≤ count1432 b)) else (if i < 1445 then decide (13 ≤ count1432 b) else decide (14 ≤ count1432 b)))))) else (if i < 1460 then (if i < 1453 then (if i < 1449 then (if i < 1447 then decide (15 ≤ count1432 b) else (if i < 1448 then decide (16 ≤ count1432 b) else decide (17 ≤ count1432 b))) else (if i < 1451 then (if i < 1450 then decide (18 ≤ count1432 b) else decide (19 ≤ count1432 b)) else (if i < 1452 then decide (20 ≤ count1432 b) else decide (21 ≤ count1432 b)))) else (if i < 1456 then (if i < 1454 then decide (22 ≤ count1432 b) else (if i < 1455 then decide (23 ≤ count1432 b) else decide (24 ≤ count1432 b))) else (if i < 1458 then (if i < 1457 then decide (25 ≤ count1432 b) else decide (26 ≤ count1432 b)) else (if i < 1459 then decide (27 ≤ count1432 b) else decide (28 ≤ count1432 b))))) else (if i < 1467 then (if i < 1463 then (if i < 1461 then decide (29 ≤ count1432 b) else (if i < 1462 then decide (30 ≤ count1432 b) else decide (31 ≤ count1432 b))) else (if i < 1465 then (if i < 1464 then decide (1 ≤ count1463 b) else decide (2 ≤ count1463 b)) else (if i < 1466 then decide (3 ≤ count1463 b) else decide (4 ≤ count1463 b)))) else (if i < 1471 then (if i < 1469 then (if i < 1468 then decide (5 ≤ count1463 b) else decide (6 ≤ count1463 b)) else (if i < 1470 then decide (7 ≤ count1463 b) else decide (8 ≤ count1463 b))) else (if i < 1473 then (if i < 1472 then decide (9 ≤ count1463 b) else decide (10 ≤ count1463 b)) else (if i < 1474 then decide (11 ≤ count1463 b) else decide (12 ≤ count1463 b)))))))) else (if i < 1532 then (if i < 1503 then (if i < 1489 then (if i < 1482 then (if i < 1478 then (if i < 1476 then decide (13 ≤ count1463 b) else (if i < 1477 then decide (14 ≤ count1463 b) else decide (15 ≤ count1463 b))) else (if i < 1480 then (if i < 1479 then decide (16 ≤ count1463 b) else decide (17 ≤ count1463 b)) else (if i < 1481 then decide (18 ≤ count1463 b) else decide (19 ≤ count1463 b)))) else (if i < 1485 then (if i < 1483 then decide (20 ≤ count1463 b) else (if i < 1484 then decide (21 ≤ count1463 b) else decide (22 ≤ count1463 b))) else (if i < 1487 then (if i < 1486 then decide (23 ≤ count1463 b) else decide (24 ≤ count1463 b)) else (if i < 1488 then decide (25 ≤ count1463 b) else decide (26 ≤ count1463 b))))) else (if i < 1496 then (if i < 1492 then (if i < 1490 then decide (27 ≤ count1463 b) else (if i < 1491 then decide (28 ≤ count1463 b) else decide (29 ≤ count1463 b))) else (if i < 1494 then (if i < 1493 then decide (30 ≤ count1463 b) else decide (31 ≤ count1463 b)) else (if i < 1495 then decide (32 ≤ count1463 b) else decide (33 ≤ count1463 b)))) else (if i < 1499 then (if i < 1497 then decide (34 ≤ count1463 b) else (if i < 1498 then decide (35 ≤ count1463 b) else decide (36 ≤ count1463 b))) else (if i < 1501 then (if i < 1500 then decide (37 ≤ count1463 b) else decide (38 ≤ count1463 b)) else (if i < 1502 then decide (39 ≤ count1463 b) else decide (40 ≤ count1463 b)))))) else (if i < 1517 then (if i < 1510 then (if i < 1506 then (if i < 1504 then decide (41 ≤ count1463 b) else (if i < 1505 then decide (42 ≤ count1463 b) else decide (1 ≤ count1505 b))) else (if i < 1508 then (if i < 1507 then decide (2 ≤ count1505 b) else decide (1 ≤ count1507 b)) else (if i < 1509 then decide (2 ≤ count1507 b) else decide (3 ≤ count1507 b)))) else (if i < 1513 then (if i < 1511 then decide (1 ≤ count1510 b) else (if i < 1512 then decide (2 ≤ count1510 b) else decide (1 ≤ count1512 b))) else (if i < 1515 then (if i < 1514 then decide (2 ≤ count1512 b) else decide (1 ≤ count1514 b)) else (if i < 1516 then decide (2 ≤ count1514 b) else decide (3 ≤ count1514 b))))) else (if i < 1524 then (if i < 1520 then (if i < 1518 then decide (4 ≤ count1514 b) else (if i < 1519 then decide (1 ≤ count1518 b) else decide (2 ≤ count1518 b))) else (if i < 1522 then (if i < 1521 then decide (3 ≤ count1518 b) else decide (4 ≤ count1518 b)) else (if i < 1523 then decide (5 ≤ count1518 b) else decide (6 ≤ count1518 b)))) else (if i < 1528 then (if i < 1526 then (if i < 1525 then decide (7 ≤ count1518 b) else decide (1 ≤ count1525 b)) else (if i < 1527 then decide (2 ≤ count1525 b) else decide (1 ≤ count1527 b))) else (if i < 1530 then (if i < 1529 then decide (2 ≤ count1527 b) else decide (1 ≤ count1529 b)) else (if i < 1531 then decide (2 ≤ count1529 b) else decide (3 ≤ count1529 b))))))) else (if i < 1560 then (if i < 1546 then (if i < 1539 then (if i < 1535 then (if i < 1533 then decide (4 ≤ count1529 b) else (if i < 1534 then decide (1 ≤ count1533 b) else decide (2 ≤ count1533 b))) else (if i < 1537 then (if i < 1536 then decide (1 ≤ count1535 b) else decide (2 ≤ count1535 b)) else (if i < 1538 then decide (1 ≤ count1537 b) else decide (2 ≤ count1537 b)))) else (if i < 1542 then (if i < 1540 then decide (3 ≤ count1537 b) else (if i < 1541 then decide (4 ≤ count1537 b) else decide (1 ≤ count1541 b))) else (if i < 1544 then (if i < 1543 then decide (2 ≤ count1541 b) else decide (3 ≤ count1541 b)) else (if i < 1545 then decide (4 ≤ count1541 b) else decide (5 ≤ count1541 b))))) else (if i < 1553 then (if i < 1549 then (if i < 1547 then decide (6 ≤ count1541 b) else (if i < 1548 then decide (7 ≤ count1541 b) else decide (8 ≤ count1541 b))) else (if i < 1551 then (if i < 1550 then decide (1 ≤ count1549 b) else decide (2 ≤ count1549 b)) else (if i < 1552 then decide (3 ≤ count1549 b) else decide (4 ≤ count1549 b)))) else (if i < 1556 then (if i < 1554 then decide (5 ≤ count1549 b) else (if i < 1555 then decide (6 ≤ count1549 b) else decide (7 ≤ count1549 b))) else (if i < 1558 then (if i < 1557 then decide (8 ≤ count1549 b) else decide (9 ≤ count1549 b)) else (if i < 1559 then decide (10 ≤ count1549 b) else decide (11 ≤ count1549 b)))))) else (if i < 1574 then (if i < 1567 then (if i < 1563 then (if i < 1561 then decide (12 ≤ count1549 b) else (if i < 1562 then decide (13 ≤ count1549 b) else decide (14 ≤ count1549 b))) else (if i < 1565 then (if i < 1564 then decide (15 ≤ count1549 b) else decide (1 ≤ count1564 b)) else (if i < 1566 then decide (2 ≤ count1564 b) else decide (1 ≤ count1566 b)))) else (if i < 1570 then (if i < 1568 then decide (2 ≤ count1566 b) else (if i < 1569 then decide (1 ≤ count1568 b) else decide (2 ≤ count1568 b))) else (if i < 1572 then (if i < 1571 then decide (3 ≤ count1568 b) else decide (4 ≤ count1568 b)) else (if i < 1573 then decide (1 ≤ count1572 b) else decide (2 ≤ count1572 b))))) else (if i < 1581 then (if i < 1577 then (if i < 1575 then decide (1 ≤ count1574 b) else (if i < 1576 then decide (2 ≤ count1574 b) else decide (1 ≤ count1576 b))) else (if i < 1579 then (if i < 1578 then decide (2 ≤ count1576 b) else decide (3 ≤ count1576 b)) else (if i < 1580 then decide (4 ≤ count1576 b) else decide (1 ≤ count1580 b)))) else (if i < 1585 then (if i < 1583 then (if i < 1582 then decide (2 ≤ count1580 b) else decide (3 ≤ count1580 b)) else (if i < 1584 then decide (4 ≤ count1580 b) else decide (5 ≤ count1580 b))) else (if i < 1587 then (if i < 1586 then decide (6 ≤ count1580 b) else decide (7 ≤ count1580 b)) else (if i < 1588 then decide (8 ≤ count1580 b) else decide (1 ≤ count1588 b))))))))) else (if i < 1703 then (if i < 1646 then (if i < 1617 then (if i < 1603 then (if i < 1596 then (if i < 1592 then (if i < 1590 then decide (2 ≤ count1588 b) else (if i < 1591 then decide (1 ≤ count1590 b) else decide (2 ≤ count1590 b))) else (if i < 1594 then (if i < 1593 then decide (1 ≤ count1592 b) else decide (2 ≤ count1592 b)) else (if i < 1595 then decide (3 ≤ count1592 b) else decide (4 ≤ count1592 b)))) else (if i < 1599 then (if i < 1597 then decide (1 ≤ count1596 b) else (if i < 1598 then decide (2 ≤ count1596 b) else decide (1 ≤ count1598 b))) else (if i < 1601 then (if i < 1600 then decide (2 ≤ count1598 b) else decide (1 ≤ count1600 b)) else (if i < 1602 then decide (2 ≤ count1600 b) else decide (3 ≤ count1600 b))))) else (if i < 1610 then (if i < 1606 then (if i < 1604 then decide (4 ≤ count1600 b) else (if i < 1605 then decide (1 ≤ count1604 b) else decide (2 ≤ count1604 b))) else (if i < 1608 then (if i < 1607 then decide (3 ≤ count1604 b) else decide (4 ≤ count1604 b)) else (if i < 1609 then decide (5 ≤ count1604 b) else decide (6 ≤ count1604 b)))) else (if i < 1613 then (if i < 1611 then decide (7 ≤ count1604 b) else (if i < 1612 then decide (8 ≤ count1604 b) else decide (1 ≤ count1612 b))) else (if i < 1615 then (if i < 1614 then decide (2 ≤ count1612 b) else decide (3 ≤ count1612 b)) else (if i < 1616 then decide (4 ≤ count1612 b) else decide (5 ≤ count1612 b)))))) else (if i < 1631 then (if i < 1624 then (if i < 1620 then (if i < 1618 then decide (6 ≤ count1612 b) else (if i < 1619 then decide (7 ≤ count1612 b) else decide (8 ≤ count1612 b))) else (if i < 1622 then (if i < 1621 then decide (9 ≤ count1612 b) else decide (10 ≤ count1612 b)) else (if i < 1623 then decide (11 ≤ count1612 b) else decide (12 ≤ count1612 b)))) else (if i < 1627 then (if i < 1625 then decide (13 ≤ count1612 b) else (if i < 1626 then decide (14 ≤ count1612 b) else decide (15 ≤ count1612 b))) else (if i < 1629 then (if i < 1628 then decide (16 ≤ count1612 b) else decide (1 ≤ count1628 b)) else (if i < 1630 then decide (2 ≤ count1628 b) else decide (3 ≤ count1628 b))))) else (if i < 1638 then (if i < 1634 then (if i < 1632 then decide (4 ≤ count1628 b) else (if i < 1633 then decide (5 ≤ count1628 b) else decide (6 ≤ count1628 b))) else (if i < 1636 then (if i < 1635 then decide (7 ≤ count1628 b) else decide (8 ≤ count1628 b)) else (if i < 1637 then decide (9 ≤ count1628 b) else decide (10 ≤ count1628 b)))) else (if i < 1642 then (if i < 1640 then (if i < 1639 then decide (11 ≤ count1628 b) else decide (12 ≤ count1628 b)) else (if i < 1641 then decide (13 ≤ count1628 b) else decide (14 ≤ count1628 b))) else (if i < 1644 then (if i < 1643 then decide (15 ≤ count1628 b) else decide (16 ≤ count1628 b)) else (if i < 1645 then decide (17 ≤ count1628 b) else decide (18 ≤ count1628 b))))))) else (if i < 1674 then (if i < 1660 then (if i < 1653 then (if i < 1649 then (if i < 1647 then decide (19 ≤ count1628 b) else (if i < 1648 then decide (20 ≤ count1628 b) else decide (21 ≤ count1628 b))) else (if i < 1651 then (if i < 1650 then decide (22 ≤ count1628 b) else decide (1 ≤ count1650 b)) else (if i < 1652 then decide (2 ≤ count1650 b) else decide (1 ≤ count1652 b)))) else (if i < 1656 then (if i < 1654 then decide (2 ≤ count1652 b) else (if i < 1655 then decide (3 ≤ count1652 b) else decide (1 ≤ count1655 b))) else (if i < 1658 then (if i < 1657 then decide (2 ≤ count1655 b) else decide (1 ≤ count1657 b)) else (if i < 1659 then decide (2 ≤ count1657 b) else decide (1 ≤ count1659 b))))) else (if i < 1667 then (if i < 1663 then (if i < 1661 then decide (2 ≤ count1659 b) else (if i < 1662 then decide (3 ≤ count1659 b) else decide (4 ≤ count1659 b))) else (if i < 1665 then (if i < 1664 then decide (1 ≤ count1663 b) else decide (2 ≤ count1663 b)) else (if i < 1666 then decide (3 ≤ count1663 b) else decide (4 ≤ count1663 b)))) else (if i < 1670 then (if i < 1668 then decide (5 ≤ count1663 b) else (if i < 1669 then decide (6 ≤ count1663 b) else decide (7 ≤ count1663 b))) else (if i < 1672 then (if i < 1671 then decide (1 ≤ count1670 b) else decide (2 ≤ count1670 b)) else (if i < 1673 then decide (1 ≤ count1672 b) else decide (2 ≤ count1672 b)))))) else (if i < 1688 then (if i < 1681 then (if i < 1677 then (if i < 1675 then decide (1 ≤ count1674 b) else (if i < 1676 then decide (2 ≤ count1674 b) else decide (3 ≤ count1674 b))) else (if i < 1679 then (if i < 1678 then decide (4 ≤ count1674 b) else decide (1 ≤ count1678 b)) else (if i < 1680 then decide (2 ≤ count1678 b) else decide (1 ≤ count1680 b)))) else (if i < 1684 then (if i < 1682 then decide (2 ≤ count1680 b) else (if i < 1683 then decide (1 ≤ count1682 b) else decide (2 ≤ count1682 b))) else (if i < 1686 then (if i < 1685 then decide (3 ≤ count1682 b) else decide (4 ≤ count1682 b)) else (if i < 1687 then decide (1 ≤ count1686 b) else decide (2 ≤ count1686 b))))) else (if i < 1695 then (if i < 1691 then (if i < 1689 then decide (3 ≤ count1686 b) else (if i < 1690 then decide (4 ≤ count1686 b) else decide (5 ≤ count1686 b))) else (if i < 1693 then (if i < 1692 then decide (6 ≤ count1686 b) else decide (7 ≤ count1686 b)) else (if i < 1694 then decide (8 ≤ count1686 b) else decide (1 ≤ count1694 b)))) else (if i < 1699 then (if i < 1697 then (if i < 1696 then decide (2 ≤ count1694 b) else decide (3 ≤ count1694 b)) else (if i < 1698 then decide (4 ≤ count1694 b) else decide (5 ≤ count1694 b))) else (if i < 1701 then (if i < 1700 then decide (6 ≤ count1694 b) else decide (7 ≤ count1694 b)) else (if i < 1702 then decide (8 ≤ count1694 b) else decide (9 ≤ count1694 b)))))))) else (if i < 1760 then (if i < 1731 then (if i < 1717 then (if i < 1710 then (if i < 1706 then (if i < 1704 then decide (10 ≤ count1694 b) else (if i < 1705 then decide (11 ≤ count1694 b) else decide (12 ≤ count1694 b))) else (if i < 1708 then (if i < 1707 then decide (13 ≤ count1694 b) else decide (14 ≤ count1694 b)) else (if i < 1709 then decide (15 ≤ count1694 b) else decide (1 ≤ count1709 b)))) else (if i < 1713 then (if i < 1711 then decide (2 ≤ count1709 b) else (if i < 1712 then decide (1 ≤ count1711 b) else decide (2 ≤ count1711 b))) else (if i < 1715 then (if i < 1714 then decide (1 ≤ count1713 b) else decide (2 ≤ count1713 b)) else (if i < 1716 then decide (3 ≤ count1713 b) else decide (4 ≤ count1713 b))))) else (if i < 1724 then (if i < 1720 then (if i < 1718 then decide (1 ≤ count1717 b) else (if i < 1719 then decide (2 ≤ count1717 b) else decide (1 ≤ count1719 b))) else (if i < 1722 then (if i < 1721 then decide (2 ≤ count1719 b) else decide (1 ≤ count1721 b)) else (if i < 1723 then decide (2 ≤ count1721 b) else decide (3 ≤ count1721 b)))) else (if i < 1727 then (if i < 1725 then decide (4 ≤ count1721 b) else (if i < 1726 then decide (1 ≤ count1725 b) else decide (2 ≤ count1725 b))) else (if i < 1729 then (if i < 1728 then decide (3 ≤ count1725 b) else decide (4 ≤ count1725 b)) else (if i < 1730 then decide (5 ≤ count1725 b) else decide (6 ≤ count1725 b)))))) else (if i < 1745 then (if i < 1738 then (if i < 1734 then (if i < 1732 then decide (7 ≤ count1725 b) else (if i < 1733 then decide (8 ≤ count1725 b) else decide (1 ≤ count1733 b))) else (if i < 1736 then (if i < 1735 then decide (2 ≤ count1733 b) else decide (1 ≤ count1735 b)) else (if i < 1737 then decide (2 ≤ count1735 b) else decide (1 ≤ count1737 b)))) else (if i < 1741 then (if i < 1739 then decide (2 ≤ count1737 b) else (if i < 1740 then decide (3 ≤ count1737 b) else decide (4 ≤ count1737 b))) else (if i < 1743 then (if i < 1742 then decide (1 ≤ count1741 b) else decide (2 ≤ count1741 b)) else (if i < 1744 then decide (1 ≤ count1743 b) else decide (2 ≤ count1743 b))))) else (if i < 1752 then (if i < 1748 then (if i < 1746 then decide (1 ≤ count1745 b) else (if i < 1747 then decide (2 ≤ count1745 b) else decide (3 ≤ count1745 b))) else (if i < 1750 then (if i < 1749 then decide (4 ≤ count1745 b) else decide (1 ≤ count1749 b)) else (if i < 1751 then decide (2 ≤ count1749 b) else decide (3 ≤ count1749 b)))) else (if i < 1756 then (if i < 1754 then (if i < 1753 then decide (4 ≤ count1749 b) else decide (5 ≤ count1749 b)) else (if i < 1755 then decide (6 ≤ count1749 b) else decide (7 ≤ count1749 b))) else (if i < 1758 then (if i < 1757 then decide (8 ≤ count1749 b) else decide (1 ≤ count1757 b)) else (if i < 1759 then decide (2 ≤ count1757 b) else decide (3 ≤ count1757 b))))))) else (if i < 1788 then (if i < 1774 then (if i < 1767 then (if i < 1763 then (if i < 1761 then decide (4 ≤ count1757 b) else (if i < 1762 then decide (5 ≤ count1757 b) else decide (6 ≤ count1757 b))) else (if i < 1765 then (if i < 1764 then decide (7 ≤ count1757 b) else decide (8 ≤ count1757 b)) else (if i < 1766 then decide (9 ≤ count1757 b) else decide (10 ≤ count1757 b)))) else (if i < 1770 then (if i < 1768 then decide (11 ≤ count1757 b) else (if i < 1769 then decide (12 ≤ count1757 b) else decide (13 ≤ count1757 b))) else (if i < 1772 then (if i < 1771 then decide (14 ≤ count1757 b) else decide (15 ≤ count1757 b)) else (if i < 1773 then decide (16 ≤ count1757 b) else decide (1 ≤ count1773 b))))) else (if i < 1781 then (if i < 1777 then (if i < 1775 then decide (2 ≤ count1773 b) else (if i < 1776 then decide (3 ≤ count1773 b) else decide (4 ≤ count1773 b))) else (if i < 1779 then (if i < 1778 then decide (5 ≤ count1773 b) else decide (6 ≤ count1773 b)) else (if i < 1780 then decide (7 ≤ count1773 b) else decide (8 ≤ count1773 b)))) else (if i < 1784 then (if i < 1782 then decide (9 ≤ count1773 b) else (if i < 1783 then decide (10 ≤ count1773 b) else decide (11 ≤ count1773 b))) else (if i < 1786 then (if i < 1785 then decide (12 ≤ count1773 b) else decide (13 ≤ count1773 b)) else (if i < 1787 then decide (14 ≤ count1773 b) else decide (15 ≤ count1773 b)))))) else (if i < 1802 then (if i < 1795 then (if i < 1791 then (if i < 1789 then decide (16 ≤ count1773 b) else (if i < 1790 then decide (17 ≤ count1773 b) else decide (18 ≤ count1773 b))) else (if i < 1793 then (if i < 1792 then decide (19 ≤ count1773 b) else decide (20 ≤ count1773 b)) else (if i < 1794 then decide (21 ≤ count1773 b) else decide (22 ≤ count1773 b)))) else (if i < 1798 then (if i < 1796 then decide (1 ≤ count1795 b) else (if i < 1797 then decide (2 ≤ count1795 b) else decide (3 ≤ count1795 b))) else (if i < 1800 then (if i < 1799 then decide (4 ≤ count1795 b) else decide (5 ≤ count1795 b)) else (if i < 1801 then decide (6 ≤ count1795 b) else decide (7 ≤ count1795 b))))) else (if i < 1809 then (if i < 1805 then (if i < 1803 then decide (8 ≤ count1795 b) else (if i < 1804 then decide (9 ≤ count1795 b) else decide (10 ≤ count1795 b))) else (if i < 1807 then (if i < 1806 then decide (11 ≤ count1795 b) else decide (12 ≤ count1795 b)) else (if i < 1808 then decide (13 ≤ count1795 b) else decide (14 ≤ count1795 b)))) else (if i < 1813 then (if i < 1811 then (if i < 1810 then decide (15 ≤ count1795 b) else decide (16 ≤ count1795 b)) else (if i < 1812 then decide (17 ≤ count1795 b) else decide (18 ≤ count1795 b))) else (if i < 1815 then (if i < 1814 then decide (19 ≤ count1795 b) else decide (20 ≤ count1795 b)) else (if i < 1816 then decide (21 ≤ count1795 b) else decide (22 ≤ count1795 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (2 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (5 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (6 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (12 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (14 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (28 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (65 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (69 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (76 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (77 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (129 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (131 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (132 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (133 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (134 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (138 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (139 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (140 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (141 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (144 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (148 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (149 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (150 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (151 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (152 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (154 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (155 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (192 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (194 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (196 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (198 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (199 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (200 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (201 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (206 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (207 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (209 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (210 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (211 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (213 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (217 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (219 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (220 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (221 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (222 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (257 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (259 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (261 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (262 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (263 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (264 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (267 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (268 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (269 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (271 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (272 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (274 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (276 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (277 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (278 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (280 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (282 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (283 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (320 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (322 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (324 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (326 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (327 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (328 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (329 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (334 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (335 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (337 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (338 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (339 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (341 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (345 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (348 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (349 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (350 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (384 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (386 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (388 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (391 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (393 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (394 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (396 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (397 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (398 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (399 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (400 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (401 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (402 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (403 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (407 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (409 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (412 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (413 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (414 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (415 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (448 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (449 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (451 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (452 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (453 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (455 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (456 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (457 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (458 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (459 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (461 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (462 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (463 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (464 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (468 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (469 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (470 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (471 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (472 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (474 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (475 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (476 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (478 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (2 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (76 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (77 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (129 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (141 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (150 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (154 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (196 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (198 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (199 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (200 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (209 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (210 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (211 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (219 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (263 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (269 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (278 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (322 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (324 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (329 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (334 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (341 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (388 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (394 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (402 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (449 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (451 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (453 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (457 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (458 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (459 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (461 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (462 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (464 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (469 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (470 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (BallClauseLogic.Endpoint q (474 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (475 : Vertex)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value274 (q : Snake 81) : valuation q 274 = decide (2 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value276 (q : Snake 81) : valuation q 276 = decide (2 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value366 (q : Snake 81) : valuation q 366 = decide (2 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value380 (q : Snake 81) : valuation q 380 = decide (2 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value394 (q : Snake 81) : valuation q 394 = decide (2 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value396 (q : Snake 81) : valuation q 396 = decide (2 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value410 (q : Snake 81) : valuation q 410 = decide (2 ≤ count409 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value426 (q : Snake 81) : valuation q 426 = decide (2 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value434 (q : Snake 81) : valuation q 434 = decide (2 ≤ count433 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value440 (q : Snake 81) : valuation q 440 = decide (2 ≤ count439 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value456 (q : Snake 81) : valuation q 456 = decide (2 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value484 (q : Snake 81) : valuation q 484 = decide (2 ≤ count483 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value486 (q : Snake 81) : valuation q 486 = decide (2 ≤ count485 (baseVal q)) := rfl
theorem value487 (q : Snake 81) : valuation q 487 = decide (1 ≤ count487 (baseVal q)) := rfl
theorem value488 (q : Snake 81) : valuation q 488 = decide (2 ≤ count487 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value490 (q : Snake 81) : valuation q 490 = decide (2 ≤ count489 (baseVal q)) := rfl
theorem value492 (q : Snake 81) : valuation q 492 = decide (2 ≤ count491 (baseVal q)) := rfl
theorem value843 (q : Snake 81) : valuation q 843 = decide (1 ≤ count843 (baseVal q)) := rfl
theorem value844 (q : Snake 81) : valuation q 844 = decide (2 ≤ count843 (baseVal q)) := rfl
theorem value845 (q : Snake 81) : valuation q 845 = decide (1 ≤ count845 (baseVal q)) := rfl
theorem value846 (q : Snake 81) : valuation q 846 = decide (2 ≤ count845 (baseVal q)) := rfl
theorem value847 (q : Snake 81) : valuation q 847 = decide (3 ≤ count845 (baseVal q)) := rfl
theorem value848 (q : Snake 81) : valuation q 848 = decide (1 ≤ count848 (baseVal q)) := rfl
theorem value850 (q : Snake 81) : valuation q 850 = decide (1 ≤ count850 (baseVal q)) := rfl
theorem value851 (q : Snake 81) : valuation q 851 = decide (2 ≤ count850 (baseVal q)) := rfl
theorem value852 (q : Snake 81) : valuation q 852 = decide (1 ≤ count852 (baseVal q)) := rfl
theorem value853 (q : Snake 81) : valuation q 853 = decide (2 ≤ count852 (baseVal q)) := rfl
theorem value854 (q : Snake 81) : valuation q 854 = decide (3 ≤ count852 (baseVal q)) := rfl
theorem value857 (q : Snake 81) : valuation q 857 = decide (2 ≤ count856 (baseVal q)) := rfl
theorem value858 (q : Snake 81) : valuation q 858 = decide (3 ≤ count856 (baseVal q)) := rfl
theorem value859 (q : Snake 81) : valuation q 859 = decide (4 ≤ count856 (baseVal q)) := rfl
theorem value860 (q : Snake 81) : valuation q 860 = decide (5 ≤ count856 (baseVal q)) := rfl
theorem value863 (q : Snake 81) : valuation q 863 = decide (1 ≤ count863 (baseVal q)) := rfl
theorem value864 (q : Snake 81) : valuation q 864 = decide (2 ≤ count863 (baseVal q)) := rfl
theorem value865 (q : Snake 81) : valuation q 865 = decide (1 ≤ count865 (baseVal q)) := rfl
theorem value866 (q : Snake 81) : valuation q 866 = decide (2 ≤ count865 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (1 ≤ count867 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (2 ≤ count867 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (3 ≤ count867 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (1 ≤ count871 (baseVal q)) := rfl
theorem value872 (q : Snake 81) : valuation q 872 = decide (2 ≤ count871 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (1 ≤ count873 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (2 ≤ count873 (baseVal q)) := rfl
theorem value875 (q : Snake 81) : valuation q 875 = decide (1 ≤ count875 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (2 ≤ count875 (baseVal q)) := rfl
theorem value877 (q : Snake 81) : valuation q 877 = decide (3 ≤ count875 (baseVal q)) := rfl
theorem value879 (q : Snake 81) : valuation q 879 = decide (1 ≤ count879 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (2 ≤ count879 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (3 ≤ count879 (baseVal q)) := rfl
theorem value882 (q : Snake 81) : valuation q 882 = decide (4 ≤ count879 (baseVal q)) := rfl
theorem value889 (q : Snake 81) : valuation q 889 = decide (3 ≤ count887 (baseVal q)) := rfl
theorem value890 (q : Snake 81) : valuation q 890 = decide (4 ≤ count887 (baseVal q)) := rfl
theorem value891 (q : Snake 81) : valuation q 891 = decide (5 ≤ count887 (baseVal q)) := rfl
theorem value892 (q : Snake 81) : valuation q 892 = decide (6 ≤ count887 (baseVal q)) := rfl
theorem value902 (q : Snake 81) : valuation q 902 = decide (1 ≤ count902 (baseVal q)) := rfl
theorem value903 (q : Snake 81) : valuation q 903 = decide (2 ≤ count902 (baseVal q)) := rfl
theorem value904 (q : Snake 81) : valuation q 904 = decide (1 ≤ count904 (baseVal q)) := rfl
theorem value905 (q : Snake 81) : valuation q 905 = decide (2 ≤ count904 (baseVal q)) := rfl
theorem value906 (q : Snake 81) : valuation q 906 = decide (1 ≤ count906 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (2 ≤ count906 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (3 ≤ count906 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (4 ≤ count906 (baseVal q)) := rfl
theorem value910 (q : Snake 81) : valuation q 910 = decide (1 ≤ count910 (baseVal q)) := rfl
theorem value911 (q : Snake 81) : valuation q 911 = decide (2 ≤ count910 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (1 ≤ count912 (baseVal q)) := rfl
theorem value913 (q : Snake 81) : valuation q 913 = decide (2 ≤ count912 (baseVal q)) := rfl
theorem value914 (q : Snake 81) : valuation q 914 = decide (1 ≤ count914 (baseVal q)) := rfl
theorem value915 (q : Snake 81) : valuation q 915 = decide (2 ≤ count914 (baseVal q)) := rfl
theorem value916 (q : Snake 81) : valuation q 916 = decide (3 ≤ count914 (baseVal q)) := rfl
theorem value918 (q : Snake 81) : valuation q 918 = decide (1 ≤ count918 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (2 ≤ count918 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (3 ≤ count918 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (4 ≤ count918 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (5 ≤ count918 (baseVal q)) := rfl
theorem value926 (q : Snake 81) : valuation q 926 = decide (1 ≤ count926 (baseVal q)) := rfl
theorem value927 (q : Snake 81) : valuation q 927 = decide (2 ≤ count926 (baseVal q)) := rfl
theorem value928 (q : Snake 81) : valuation q 928 = decide (1 ≤ count928 (baseVal q)) := rfl
theorem value929 (q : Snake 81) : valuation q 929 = decide (2 ≤ count928 (baseVal q)) := rfl
theorem value930 (q : Snake 81) : valuation q 930 = decide (1 ≤ count930 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (2 ≤ count930 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (3 ≤ count930 (baseVal q)) := rfl
theorem value934 (q : Snake 81) : valuation q 934 = decide (1 ≤ count934 (baseVal q)) := rfl
theorem value935 (q : Snake 81) : valuation q 935 = decide (2 ≤ count934 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (1 ≤ count936 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (2 ≤ count936 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (1 ≤ count938 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (2 ≤ count938 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (3 ≤ count938 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (4 ≤ count938 (baseVal q)) := rfl
theorem value942 (q : Snake 81) : valuation q 942 = decide (1 ≤ count942 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (2 ≤ count942 (baseVal q)) := rfl
theorem value944 (q : Snake 81) : valuation q 944 = decide (3 ≤ count942 (baseVal q)) := rfl
theorem value945 (q : Snake 81) : valuation q 945 = decide (4 ≤ count942 (baseVal q)) := rfl
theorem value946 (q : Snake 81) : valuation q 946 = decide (5 ≤ count942 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (6 ≤ count942 (baseVal q)) := rfl
theorem value951 (q : Snake 81) : valuation q 951 = decide (2 ≤ count950 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (3 ≤ count950 (baseVal q)) := rfl
theorem value953 (q : Snake 81) : valuation q 953 = decide (4 ≤ count950 (baseVal q)) := rfl
theorem value954 (q : Snake 81) : valuation q 954 = decide (5 ≤ count950 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (6 ≤ count950 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (7 ≤ count950 (baseVal q)) := rfl
theorem value957 (q : Snake 81) : valuation q 957 = decide (8 ≤ count950 (baseVal q)) := rfl
theorem value958 (q : Snake 81) : valuation q 958 = decide (9 ≤ count950 (baseVal q)) := rfl
theorem value971 (q : Snake 81) : valuation q 971 = decide (6 ≤ count966 (baseVal q)) := rfl
theorem value972 (q : Snake 81) : valuation q 972 = decide (7 ≤ count966 (baseVal q)) := rfl
theorem value973 (q : Snake 81) : valuation q 973 = decide (8 ≤ count966 (baseVal q)) := rfl
theorem value974 (q : Snake 81) : valuation q 974 = decide (9 ≤ count966 (baseVal q)) := rfl
theorem value975 (q : Snake 81) : valuation q 975 = decide (10 ≤ count966 (baseVal q)) := rfl
theorem value976 (q : Snake 81) : valuation q 976 = decide (11 ≤ count966 (baseVal q)) := rfl
theorem value977 (q : Snake 81) : valuation q 977 = decide (12 ≤ count966 (baseVal q)) := rfl
theorem value978 (q : Snake 81) : valuation q 978 = decide (13 ≤ count966 (baseVal q)) := rfl
theorem value988 (q : Snake 81) : valuation q 988 = decide (1 ≤ count988 (baseVal q)) := rfl
theorem value989 (q : Snake 81) : valuation q 989 = decide (2 ≤ count988 (baseVal q)) := rfl
theorem value990 (q : Snake 81) : valuation q 990 = decide (1 ≤ count990 (baseVal q)) := rfl
theorem value991 (q : Snake 81) : valuation q 991 = decide (2 ≤ count990 (baseVal q)) := rfl
theorem value992 (q : Snake 81) : valuation q 992 = decide (3 ≤ count990 (baseVal q)) := rfl
theorem value993 (q : Snake 81) : valuation q 993 = decide (1 ≤ count993 (baseVal q)) := rfl
theorem value994 (q : Snake 81) : valuation q 994 = decide (2 ≤ count993 (baseVal q)) := rfl
theorem value995 (q : Snake 81) : valuation q 995 = decide (1 ≤ count995 (baseVal q)) := rfl
theorem value996 (q : Snake 81) : valuation q 996 = decide (2 ≤ count995 (baseVal q)) := rfl
theorem value997 (q : Snake 81) : valuation q 997 = decide (1 ≤ count997 (baseVal q)) := rfl
theorem value998 (q : Snake 81) : valuation q 998 = decide (2 ≤ count997 (baseVal q)) := rfl
theorem value999 (q : Snake 81) : valuation q 999 = decide (3 ≤ count997 (baseVal q)) := rfl
theorem value1000 (q : Snake 81) : valuation q 1000 = decide (4 ≤ count997 (baseVal q)) := rfl
theorem value1001 (q : Snake 81) : valuation q 1001 = decide (1 ≤ count1001 (baseVal q)) := rfl
theorem value1002 (q : Snake 81) : valuation q 1002 = decide (2 ≤ count1001 (baseVal q)) := rfl
theorem value1003 (q : Snake 81) : valuation q 1003 = decide (3 ≤ count1001 (baseVal q)) := rfl
theorem value1004 (q : Snake 81) : valuation q 1004 = decide (4 ≤ count1001 (baseVal q)) := rfl
theorem value1005 (q : Snake 81) : valuation q 1005 = decide (5 ≤ count1001 (baseVal q)) := rfl
theorem value1006 (q : Snake 81) : valuation q 1006 = decide (6 ≤ count1001 (baseVal q)) := rfl
theorem value1008 (q : Snake 81) : valuation q 1008 = decide (1 ≤ count1008 (baseVal q)) := rfl
theorem value1009 (q : Snake 81) : valuation q 1009 = decide (2 ≤ count1008 (baseVal q)) := rfl
theorem value1010 (q : Snake 81) : valuation q 1010 = decide (1 ≤ count1010 (baseVal q)) := rfl
theorem value1011 (q : Snake 81) : valuation q 1011 = decide (2 ≤ count1010 (baseVal q)) := rfl
theorem value1012 (q : Snake 81) : valuation q 1012 = decide (1 ≤ count1012 (baseVal q)) := rfl
theorem value1013 (q : Snake 81) : valuation q 1013 = decide (2 ≤ count1012 (baseVal q)) := rfl
theorem value1014 (q : Snake 81) : valuation q 1014 = decide (3 ≤ count1012 (baseVal q)) := rfl
theorem value1015 (q : Snake 81) : valuation q 1015 = decide (4 ≤ count1012 (baseVal q)) := rfl
theorem value1016 (q : Snake 81) : valuation q 1016 = decide (1 ≤ count1016 (baseVal q)) := rfl
theorem value1017 (q : Snake 81) : valuation q 1017 = decide (2 ≤ count1016 (baseVal q)) := rfl
theorem value1018 (q : Snake 81) : valuation q 1018 = decide (1 ≤ count1018 (baseVal q)) := rfl
theorem value1019 (q : Snake 81) : valuation q 1019 = decide (2 ≤ count1018 (baseVal q)) := rfl
theorem value1020 (q : Snake 81) : valuation q 1020 = decide (1 ≤ count1020 (baseVal q)) := rfl
theorem value1021 (q : Snake 81) : valuation q 1021 = decide (2 ≤ count1020 (baseVal q)) := rfl
theorem value1022 (q : Snake 81) : valuation q 1022 = decide (3 ≤ count1020 (baseVal q)) := rfl
theorem value1023 (q : Snake 81) : valuation q 1023 = decide (4 ≤ count1020 (baseVal q)) := rfl
theorem value1024 (q : Snake 81) : valuation q 1024 = decide (1 ≤ count1024 (baseVal q)) := rfl
theorem value1025 (q : Snake 81) : valuation q 1025 = decide (2 ≤ count1024 (baseVal q)) := rfl
theorem value1026 (q : Snake 81) : valuation q 1026 = decide (3 ≤ count1024 (baseVal q)) := rfl
theorem value1027 (q : Snake 81) : valuation q 1027 = decide (4 ≤ count1024 (baseVal q)) := rfl
theorem value1028 (q : Snake 81) : valuation q 1028 = decide (5 ≤ count1024 (baseVal q)) := rfl
theorem value1029 (q : Snake 81) : valuation q 1029 = decide (6 ≤ count1024 (baseVal q)) := rfl
theorem value1030 (q : Snake 81) : valuation q 1030 = decide (7 ≤ count1024 (baseVal q)) := rfl
theorem value1032 (q : Snake 81) : valuation q 1032 = decide (1 ≤ count1032 (baseVal q)) := rfl
theorem value1033 (q : Snake 81) : valuation q 1033 = decide (2 ≤ count1032 (baseVal q)) := rfl
theorem value1034 (q : Snake 81) : valuation q 1034 = decide (3 ≤ count1032 (baseVal q)) := rfl
theorem value1035 (q : Snake 81) : valuation q 1035 = decide (4 ≤ count1032 (baseVal q)) := rfl
theorem value1036 (q : Snake 81) : valuation q 1036 = decide (5 ≤ count1032 (baseVal q)) := rfl
theorem value1037 (q : Snake 81) : valuation q 1037 = decide (6 ≤ count1032 (baseVal q)) := rfl
theorem value1038 (q : Snake 81) : valuation q 1038 = decide (7 ≤ count1032 (baseVal q)) := rfl
theorem value1039 (q : Snake 81) : valuation q 1039 = decide (8 ≤ count1032 (baseVal q)) := rfl
theorem value1040 (q : Snake 81) : valuation q 1040 = decide (9 ≤ count1032 (baseVal q)) := rfl
theorem value1047 (q : Snake 81) : valuation q 1047 = decide (1 ≤ count1047 (baseVal q)) := rfl
theorem value1048 (q : Snake 81) : valuation q 1048 = decide (2 ≤ count1047 (baseVal q)) := rfl
theorem value1049 (q : Snake 81) : valuation q 1049 = decide (1 ≤ count1049 (baseVal q)) := rfl
theorem value1050 (q : Snake 81) : valuation q 1050 = decide (2 ≤ count1049 (baseVal q)) := rfl
theorem value1051 (q : Snake 81) : valuation q 1051 = decide (1 ≤ count1051 (baseVal q)) := rfl
theorem value1052 (q : Snake 81) : valuation q 1052 = decide (2 ≤ count1051 (baseVal q)) := rfl
theorem value1053 (q : Snake 81) : valuation q 1053 = decide (3 ≤ count1051 (baseVal q)) := rfl
theorem value1054 (q : Snake 81) : valuation q 1054 = decide (4 ≤ count1051 (baseVal q)) := rfl
theorem value1055 (q : Snake 81) : valuation q 1055 = decide (1 ≤ count1055 (baseVal q)) := rfl
theorem value1056 (q : Snake 81) : valuation q 1056 = decide (2 ≤ count1055 (baseVal q)) := rfl
theorem value1057 (q : Snake 81) : valuation q 1057 = decide (1 ≤ count1057 (baseVal q)) := rfl
theorem value1058 (q : Snake 81) : valuation q 1058 = decide (2 ≤ count1057 (baseVal q)) := rfl
theorem value1059 (q : Snake 81) : valuation q 1059 = decide (1 ≤ count1059 (baseVal q)) := rfl
theorem value1060 (q : Snake 81) : valuation q 1060 = decide (2 ≤ count1059 (baseVal q)) := rfl
theorem value1061 (q : Snake 81) : valuation q 1061 = decide (3 ≤ count1059 (baseVal q)) := rfl
theorem value1062 (q : Snake 81) : valuation q 1062 = decide (4 ≤ count1059 (baseVal q)) := rfl
theorem value1063 (q : Snake 81) : valuation q 1063 = decide (1 ≤ count1063 (baseVal q)) := rfl
theorem value1064 (q : Snake 81) : valuation q 1064 = decide (2 ≤ count1063 (baseVal q)) := rfl
theorem value1065 (q : Snake 81) : valuation q 1065 = decide (3 ≤ count1063 (baseVal q)) := rfl
theorem value1066 (q : Snake 81) : valuation q 1066 = decide (4 ≤ count1063 (baseVal q)) := rfl
theorem value1067 (q : Snake 81) : valuation q 1067 = decide (5 ≤ count1063 (baseVal q)) := rfl
theorem value1068 (q : Snake 81) : valuation q 1068 = decide (6 ≤ count1063 (baseVal q)) := rfl
theorem value1069 (q : Snake 81) : valuation q 1069 = decide (7 ≤ count1063 (baseVal q)) := rfl
theorem value1071 (q : Snake 81) : valuation q 1071 = decide (1 ≤ count1071 (baseVal q)) := rfl
theorem value1072 (q : Snake 81) : valuation q 1072 = decide (2 ≤ count1071 (baseVal q)) := rfl
theorem value1073 (q : Snake 81) : valuation q 1073 = decide (1 ≤ count1073 (baseVal q)) := rfl
theorem value1074 (q : Snake 81) : valuation q 1074 = decide (2 ≤ count1073 (baseVal q)) := rfl
theorem value1075 (q : Snake 81) : valuation q 1075 = decide (1 ≤ count1075 (baseVal q)) := rfl
theorem value1076 (q : Snake 81) : valuation q 1076 = decide (2 ≤ count1075 (baseVal q)) := rfl
theorem value1077 (q : Snake 81) : valuation q 1077 = decide (3 ≤ count1075 (baseVal q)) := rfl
theorem value1078 (q : Snake 81) : valuation q 1078 = decide (4 ≤ count1075 (baseVal q)) := rfl
theorem value1079 (q : Snake 81) : valuation q 1079 = decide (1 ≤ count1079 (baseVal q)) := rfl
theorem value1080 (q : Snake 81) : valuation q 1080 = decide (2 ≤ count1079 (baseVal q)) := rfl
theorem value1081 (q : Snake 81) : valuation q 1081 = decide (1 ≤ count1081 (baseVal q)) := rfl
theorem value1082 (q : Snake 81) : valuation q 1082 = decide (2 ≤ count1081 (baseVal q)) := rfl
theorem value1083 (q : Snake 81) : valuation q 1083 = decide (1 ≤ count1083 (baseVal q)) := rfl
theorem value1084 (q : Snake 81) : valuation q 1084 = decide (2 ≤ count1083 (baseVal q)) := rfl
theorem value1085 (q : Snake 81) : valuation q 1085 = decide (3 ≤ count1083 (baseVal q)) := rfl
theorem value1086 (q : Snake 81) : valuation q 1086 = decide (4 ≤ count1083 (baseVal q)) := rfl
theorem value1087 (q : Snake 81) : valuation q 1087 = decide (1 ≤ count1087 (baseVal q)) := rfl
theorem value1088 (q : Snake 81) : valuation q 1088 = decide (2 ≤ count1087 (baseVal q)) := rfl
theorem value1089 (q : Snake 81) : valuation q 1089 = decide (3 ≤ count1087 (baseVal q)) := rfl
theorem value1090 (q : Snake 81) : valuation q 1090 = decide (4 ≤ count1087 (baseVal q)) := rfl
theorem value1091 (q : Snake 81) : valuation q 1091 = decide (5 ≤ count1087 (baseVal q)) := rfl
theorem value1092 (q : Snake 81) : valuation q 1092 = decide (6 ≤ count1087 (baseVal q)) := rfl
theorem value1093 (q : Snake 81) : valuation q 1093 = decide (7 ≤ count1087 (baseVal q)) := rfl
theorem value1094 (q : Snake 81) : valuation q 1094 = decide (8 ≤ count1087 (baseVal q)) := rfl
theorem value1097 (q : Snake 81) : valuation q 1097 = decide (3 ≤ count1095 (baseVal q)) := rfl
theorem value1098 (q : Snake 81) : valuation q 1098 = decide (4 ≤ count1095 (baseVal q)) := rfl
theorem value1099 (q : Snake 81) : valuation q 1099 = decide (5 ≤ count1095 (baseVal q)) := rfl
theorem value1100 (q : Snake 81) : valuation q 1100 = decide (6 ≤ count1095 (baseVal q)) := rfl
theorem value1101 (q : Snake 81) : valuation q 1101 = decide (7 ≤ count1095 (baseVal q)) := rfl
theorem value1102 (q : Snake 81) : valuation q 1102 = decide (8 ≤ count1095 (baseVal q)) := rfl
theorem value1103 (q : Snake 81) : valuation q 1103 = decide (9 ≤ count1095 (baseVal q)) := rfl
theorem value1104 (q : Snake 81) : valuation q 1104 = decide (10 ≤ count1095 (baseVal q)) := rfl
theorem value1105 (q : Snake 81) : valuation q 1105 = decide (11 ≤ count1095 (baseVal q)) := rfl
theorem value1106 (q : Snake 81) : valuation q 1106 = decide (12 ≤ count1095 (baseVal q)) := rfl
theorem value1119 (q : Snake 81) : valuation q 1119 = decide (9 ≤ count1111 (baseVal q)) := rfl
theorem value1120 (q : Snake 81) : valuation q 1120 = decide (10 ≤ count1111 (baseVal q)) := rfl
theorem value1121 (q : Snake 81) : valuation q 1121 = decide (11 ≤ count1111 (baseVal q)) := rfl
theorem value1122 (q : Snake 81) : valuation q 1122 = decide (12 ≤ count1111 (baseVal q)) := rfl
theorem value1123 (q : Snake 81) : valuation q 1123 = decide (13 ≤ count1111 (baseVal q)) := rfl
theorem value1124 (q : Snake 81) : valuation q 1124 = decide (14 ≤ count1111 (baseVal q)) := rfl
theorem value1125 (q : Snake 81) : valuation q 1125 = decide (15 ≤ count1111 (baseVal q)) := rfl
theorem value1126 (q : Snake 81) : valuation q 1126 = decide (16 ≤ count1111 (baseVal q)) := rfl
theorem value1154 (q : Snake 81) : valuation q 1154 = decide (22 ≤ count1133 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (2 ≤ count1505 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (3 ≤ count1507 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (2 ≤ count1512 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (2 ≤ count1514 (baseVal q)) := rfl
theorem value1520 (q : Snake 81) : valuation q 1520 = decide (3 ≤ count1518 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (5 ≤ count1518 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (2 ≤ count1527 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (2 ≤ count1529 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (1 ≤ count1533 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (1 ≤ count1535 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (2 ≤ count1537 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (2 ≤ count1541 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (4 ≤ count1541 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (7 ≤ count1549 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (1 ≤ count1566 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (2 ≤ count1568 (baseVal q)) := rfl
theorem value1574 (q : Snake 81) : valuation q 1574 = decide (1 ≤ count1574 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (1 ≤ count1576 (baseVal q)) := rfl
theorem value1582 (q : Snake 81) : valuation q 1582 = decide (3 ≤ count1580 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (1 ≤ count1596 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (1 ≤ count1598 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (1 ≤ count1600 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (1 ≤ count1604 (baseVal q)) := rfl
theorem value1615 (q : Snake 81) : valuation q 1615 = decide (4 ≤ count1612 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (11 ≤ count1628 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (1 ≤ count1650 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (1 ≤ count1652 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (1 ≤ count1655 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (1 ≤ count1657 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (2 ≤ count1657 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (1 ≤ count1659 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (2 ≤ count1659 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (1 ≤ count1663 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (2 ≤ count1663 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (1 ≤ count1670 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (1 ≤ count1672 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (1 ≤ count1674 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (2 ≤ count1674 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (1 ≤ count1678 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (1 ≤ count1682 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (2 ≤ count1686 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (3 ≤ count1686 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (4 ≤ count1694 (baseVal q)) := rfl
theorem value1709 (q : Snake 81) : valuation q 1709 = decide (1 ≤ count1709 (baseVal q)) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (1 ≤ count1711 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (2 ≤ count1713 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (1 ≤ count1717 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (1 ≤ count1719 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (2 ≤ count1721 (baseVal q)) := rfl
theorem value1728 (q : Snake 81) : valuation q 1728 = decide (4 ≤ count1725 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (1 ≤ count1733 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (1 ≤ count1735 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (2 ≤ count1735 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (1 ≤ count1737 (baseVal q)) := rfl
theorem value1738 (q : Snake 81) : valuation q 1738 = decide (2 ≤ count1737 (baseVal q)) := rfl
theorem value1739 (q : Snake 81) : valuation q 1739 = decide (3 ≤ count1737 (baseVal q)) := rfl
theorem value1741 (q : Snake 81) : valuation q 1741 = decide (1 ≤ count1741 (baseVal q)) := rfl
theorem value1743 (q : Snake 81) : valuation q 1743 = decide (1 ≤ count1743 (baseVal q)) := rfl
theorem value1745 (q : Snake 81) : valuation q 1745 = decide (1 ≤ count1745 (baseVal q)) := rfl
theorem value1746 (q : Snake 81) : valuation q 1746 = decide (2 ≤ count1745 (baseVal q)) := rfl
theorem value1751 (q : Snake 81) : valuation q 1751 = decide (3 ≤ count1749 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (7 ≤ count1757 (baseVal q)) := rfl
theorem value1783 (q : Snake 81) : valuation q 1783 = decide (11 ≤ count1773 (baseVal q)) := rfl
theorem value1816 (q : Snake 81) : valuation q 1816 = decide (22 ≤ count1795 (baseVal q)) := rfl
theorem meaningNeg124 (b : Nat → Bool) : literal (valuationOf b) (-124) = decide (1 ≤ countLit b [-124]) := by
  change literal b (-124) = decide (1 ≤ countLit b [-124])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-124) <;> decide
theorem meaningNeg123 (b : Nat → Bool) : literal (valuationOf b) (-123) = decide (1 ≤ countLit b [-123]) := by
  change literal b (-123) = decide (1 ≤ countLit b [-123])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-123) <;> decide
theorem meaningNeg122 (b : Nat → Bool) : literal (valuationOf b) (-122) = decide (1 ≤ countLit b [-122]) := by
  change literal b (-122) = decide (1 ≤ countLit b [-122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-122) <;> decide
theorem meaningNeg121 (b : Nat → Bool) : literal (valuationOf b) (-121) = decide (1 ≤ countLit b [-121]) := by
  change literal b (-121) = decide (1 ≤ countLit b [-121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-121) <;> decide
theorem meaningNeg120 (b : Nat → Bool) : literal (valuationOf b) (-120) = decide (1 ≤ countLit b [-120]) := by
  change literal b (-120) = decide (1 ≤ countLit b [-120])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-120) <;> decide
theorem meaningNeg119 (b : Nat → Bool) : literal (valuationOf b) (-119) = decide (1 ≤ countLit b [-119]) := by
  change literal b (-119) = decide (1 ≤ countLit b [-119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-119) <;> decide
theorem meaningNeg118 (b : Nat → Bool) : literal (valuationOf b) (-118) = decide (1 ≤ countLit b [-118]) := by
  change literal b (-118) = decide (1 ≤ countLit b [-118])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-118) <;> decide
theorem meaningNeg117 (b : Nat → Bool) : literal (valuationOf b) (-117) = decide (1 ≤ countLit b [-117]) := by
  change literal b (-117) = decide (1 ≤ countLit b [-117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-117) <;> decide
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
theorem meaningNeg114 (b : Nat → Bool) : literal (valuationOf b) (-114) = decide (1 ≤ countLit b [-114]) := by
  change literal b (-114) = decide (1 ≤ countLit b [-114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-114) <;> decide
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
theorem meaningNeg109 (b : Nat → Bool) : literal (valuationOf b) (-109) = decide (1 ≤ countLit b [-109]) := by
  change literal b (-109) = decide (1 ≤ countLit b [-109])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-109) <;> decide
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
theorem meaningNeg83 (b : Nat → Bool) : literal (valuationOf b) (-83) = decide (1 ≤ countLit b [-83]) := by
  change literal b (-83) = decide (1 ≤ countLit b [-83])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-83) <;> decide
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
theorem meaningNeg57 (b : Nat → Bool) : literal (valuationOf b) (-57) = decide (1 ≤ countLit b [-57]) := by
  change literal b (-57) = decide (1 ≤ countLit b [-57])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-57) <;> decide
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
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
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
theorem meaningNeg15 (b : Nat → Bool) : literal (valuationOf b) (-15) = decide (1 ≤ countLit b [-15]) := by
  change literal b (-15) = decide (1 ≤ countLit b [-15])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-15) <;> decide
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
theorem meaningNeg1 (b : Nat → Bool) : literal (valuationOf b) (-1) = decide (1 ≤ countLit b [-1]) := by
  change literal b (-1) = decide (1 ≤ countLit b [-1])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-1) <;> decide
theorem meaning126 (b : Nat → Bool) : literal (valuationOf b) (126) = decide (1 ≤ countLit b [126]) := by
  change literal b (126) = decide (1 ≤ countLit b [126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (126) <;> decide
theorem meaning130 (b : Nat → Bool) : literal (valuationOf b) (130) = decide (1 ≤ countLit b [130]) := by
  change literal b (130) = decide (1 ≤ countLit b [130])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (130) <;> decide
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
theorem meaning155 (b : Nat → Bool) : literal (valuationOf b) (155) = decide (1 ≤ countLit b [155]) := by
  change literal b (155) = decide (1 ≤ countLit b [155])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (155) <;> decide
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
theorem meaning164 (b : Nat → Bool) : literal (valuationOf b) (164) = decide (1 ≤ countLit b [164]) := by
  change literal b (164) = decide (1 ≤ countLit b [164])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (164) <;> decide
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
theorem meaning194 (b : Nat → Bool) : literal (valuationOf b) (194) = decide (1 ≤ countLit b [194]) := by
  change literal b (194) = decide (1 ≤ countLit b [194])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (194) <;> decide
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
theorem meaning203 (b : Nat → Bool) : literal (valuationOf b) (203) = decide (1 ≤ countLit b [203]) := by
  change literal b (203) = decide (1 ≤ countLit b [203])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (203) <;> decide
theorem meaning207 (b : Nat → Bool) : literal (valuationOf b) (207) = decide (1 ≤ countLit b [207]) := by
  change literal b (207) = decide (1 ≤ countLit b [207])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (207) <;> decide
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
theorem meaning213 (b : Nat → Bool) : literal (valuationOf b) (213) = decide (1 ≤ countLit b [213]) := by
  change literal b (213) = decide (1 ≤ countLit b [213])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (213) <;> decide
theorem meaning219 (b : Nat → Bool) : literal (valuationOf b) (219) = decide (1 ≤ countLit b [219]) := by
  change literal b (219) = decide (1 ≤ countLit b [219])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (219) <;> decide
theorem meaning221 (b : Nat → Bool) : literal (valuationOf b) (221) = decide (1 ≤ countLit b [221]) := by
  change literal b (221) = decide (1 ≤ countLit b [221])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (221) <;> decide
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) (222) = decide (1 ≤ countLit b [222]) := by
  change literal b (222) = decide (1 ≤ countLit b [222])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (222) <;> decide
theorem meaning228 (b : Nat → Bool) : literal (valuationOf b) (228) = decide (1 ≤ countLit b [228]) := by
  change literal b (228) = decide (1 ≤ countLit b [228])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (228) <;> decide
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) (230) = decide (1 ≤ countLit b [230]) := by
  change literal b (230) = decide (1 ≤ countLit b [230])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (230) <;> decide
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
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) (244) = decide (1 ≤ countLit b [244]) := by
  change literal b (244) = decide (1 ≤ countLit b [244])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (244) <;> decide
theorem meaning246 (b : Nat → Bool) : literal (valuationOf b) (246) = decide (1 ≤ countLit b [246]) := by
  change literal b (246) = decide (1 ≤ countLit b [246])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (246) <;> decide
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning274 (b : Nat → Bool) : literal (valuationOf b) 274 = decide (2 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning276 (b : Nat → Bool) : literal (valuationOf b) 276 = decide (2 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning366 (b : Nat → Bool) : literal (valuationOf b) 366 = decide (2 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning380 (b : Nat → Bool) : literal (valuationOf b) 380 = decide (2 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning394 (b : Nat → Bool) : literal (valuationOf b) 394 = decide (2 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning396 (b : Nat → Bool) : literal (valuationOf b) 396 = decide (2 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning410 (b : Nat → Bool) : literal (valuationOf b) 410 = decide (2 ≤ count409 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning426 (b : Nat → Bool) : literal (valuationOf b) 426 = decide (2 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning434 (b : Nat → Bool) : literal (valuationOf b) 434 = decide (2 ≤ count433 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning440 (b : Nat → Bool) : literal (valuationOf b) 440 = decide (2 ≤ count439 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning456 (b : Nat → Bool) : literal (valuationOf b) 456 = decide (2 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning484 (b : Nat → Bool) : literal (valuationOf b) 484 = decide (2 ≤ count483 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning486 (b : Nat → Bool) : literal (valuationOf b) 486 = decide (2 ≤ count485 b) := rfl
theorem meaning487 (b : Nat → Bool) : literal (valuationOf b) 487 = decide (1 ≤ count487 b) := rfl
theorem meaning488 (b : Nat → Bool) : literal (valuationOf b) 488 = decide (2 ≤ count487 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning490 (b : Nat → Bool) : literal (valuationOf b) 490 = decide (2 ≤ count489 b) := rfl
theorem meaning492 (b : Nat → Bool) : literal (valuationOf b) 492 = decide (2 ≤ count491 b) := rfl
theorem meaning843 (b : Nat → Bool) : literal (valuationOf b) 843 = decide (1 ≤ count843 b) := rfl
theorem meaning844 (b : Nat → Bool) : literal (valuationOf b) 844 = decide (2 ≤ count843 b) := rfl
theorem meaning845 (b : Nat → Bool) : literal (valuationOf b) 845 = decide (1 ≤ count845 b) := rfl
theorem meaning846 (b : Nat → Bool) : literal (valuationOf b) 846 = decide (2 ≤ count845 b) := rfl
theorem meaning847 (b : Nat → Bool) : literal (valuationOf b) 847 = decide (3 ≤ count845 b) := rfl
theorem meaning848 (b : Nat → Bool) : literal (valuationOf b) 848 = decide (1 ≤ count848 b) := rfl
theorem meaning850 (b : Nat → Bool) : literal (valuationOf b) 850 = decide (1 ≤ count850 b) := rfl
theorem meaning851 (b : Nat → Bool) : literal (valuationOf b) 851 = decide (2 ≤ count850 b) := rfl
theorem meaning852 (b : Nat → Bool) : literal (valuationOf b) 852 = decide (1 ≤ count852 b) := rfl
theorem meaning853 (b : Nat → Bool) : literal (valuationOf b) 853 = decide (2 ≤ count852 b) := rfl
theorem meaning854 (b : Nat → Bool) : literal (valuationOf b) 854 = decide (3 ≤ count852 b) := rfl
theorem meaning857 (b : Nat → Bool) : literal (valuationOf b) 857 = decide (2 ≤ count856 b) := rfl
theorem meaning858 (b : Nat → Bool) : literal (valuationOf b) 858 = decide (3 ≤ count856 b) := rfl
theorem meaning859 (b : Nat → Bool) : literal (valuationOf b) 859 = decide (4 ≤ count856 b) := rfl
theorem meaning860 (b : Nat → Bool) : literal (valuationOf b) 860 = decide (5 ≤ count856 b) := rfl
theorem meaning863 (b : Nat → Bool) : literal (valuationOf b) 863 = decide (1 ≤ count863 b) := rfl
theorem meaning864 (b : Nat → Bool) : literal (valuationOf b) 864 = decide (2 ≤ count863 b) := rfl
theorem meaning865 (b : Nat → Bool) : literal (valuationOf b) 865 = decide (1 ≤ count865 b) := rfl
theorem meaning866 (b : Nat → Bool) : literal (valuationOf b) 866 = decide (2 ≤ count865 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (1 ≤ count867 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (2 ≤ count867 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (3 ≤ count867 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (1 ≤ count871 b) := rfl
theorem meaning872 (b : Nat → Bool) : literal (valuationOf b) 872 = decide (2 ≤ count871 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (1 ≤ count873 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (2 ≤ count873 b) := rfl
theorem meaning875 (b : Nat → Bool) : literal (valuationOf b) 875 = decide (1 ≤ count875 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (2 ≤ count875 b) := rfl
theorem meaning877 (b : Nat → Bool) : literal (valuationOf b) 877 = decide (3 ≤ count875 b) := rfl
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (1 ≤ count879 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (2 ≤ count879 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (3 ≤ count879 b) := rfl
theorem meaning882 (b : Nat → Bool) : literal (valuationOf b) 882 = decide (4 ≤ count879 b) := rfl
theorem meaning889 (b : Nat → Bool) : literal (valuationOf b) 889 = decide (3 ≤ count887 b) := rfl
theorem meaning890 (b : Nat → Bool) : literal (valuationOf b) 890 = decide (4 ≤ count887 b) := rfl
theorem meaning891 (b : Nat → Bool) : literal (valuationOf b) 891 = decide (5 ≤ count887 b) := rfl
theorem meaning892 (b : Nat → Bool) : literal (valuationOf b) 892 = decide (6 ≤ count887 b) := rfl
theorem meaning902 (b : Nat → Bool) : literal (valuationOf b) 902 = decide (1 ≤ count902 b) := rfl
theorem meaning903 (b : Nat → Bool) : literal (valuationOf b) 903 = decide (2 ≤ count902 b) := rfl
theorem meaning904 (b : Nat → Bool) : literal (valuationOf b) 904 = decide (1 ≤ count904 b) := rfl
theorem meaning905 (b : Nat → Bool) : literal (valuationOf b) 905 = decide (2 ≤ count904 b) := rfl
theorem meaning906 (b : Nat → Bool) : literal (valuationOf b) 906 = decide (1 ≤ count906 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (2 ≤ count906 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (3 ≤ count906 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (4 ≤ count906 b) := rfl
theorem meaning910 (b : Nat → Bool) : literal (valuationOf b) 910 = decide (1 ≤ count910 b) := rfl
theorem meaning911 (b : Nat → Bool) : literal (valuationOf b) 911 = decide (2 ≤ count910 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (1 ≤ count912 b) := rfl
theorem meaning913 (b : Nat → Bool) : literal (valuationOf b) 913 = decide (2 ≤ count912 b) := rfl
theorem meaning914 (b : Nat → Bool) : literal (valuationOf b) 914 = decide (1 ≤ count914 b) := rfl
theorem meaning915 (b : Nat → Bool) : literal (valuationOf b) 915 = decide (2 ≤ count914 b) := rfl
theorem meaning916 (b : Nat → Bool) : literal (valuationOf b) 916 = decide (3 ≤ count914 b) := rfl
theorem meaning918 (b : Nat → Bool) : literal (valuationOf b) 918 = decide (1 ≤ count918 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (2 ≤ count918 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (3 ≤ count918 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (4 ≤ count918 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (5 ≤ count918 b) := rfl
theorem meaning926 (b : Nat → Bool) : literal (valuationOf b) 926 = decide (1 ≤ count926 b) := rfl
theorem meaning927 (b : Nat → Bool) : literal (valuationOf b) 927 = decide (2 ≤ count926 b) := rfl
theorem meaning928 (b : Nat → Bool) : literal (valuationOf b) 928 = decide (1 ≤ count928 b) := rfl
theorem meaning929 (b : Nat → Bool) : literal (valuationOf b) 929 = decide (2 ≤ count928 b) := rfl
theorem meaning930 (b : Nat → Bool) : literal (valuationOf b) 930 = decide (1 ≤ count930 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (2 ≤ count930 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (3 ≤ count930 b) := rfl
theorem meaning934 (b : Nat → Bool) : literal (valuationOf b) 934 = decide (1 ≤ count934 b) := rfl
theorem meaning935 (b : Nat → Bool) : literal (valuationOf b) 935 = decide (2 ≤ count934 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (1 ≤ count936 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (2 ≤ count936 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (1 ≤ count938 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (2 ≤ count938 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (3 ≤ count938 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (4 ≤ count938 b) := rfl
theorem meaning942 (b : Nat → Bool) : literal (valuationOf b) 942 = decide (1 ≤ count942 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (2 ≤ count942 b) := rfl
theorem meaning944 (b : Nat → Bool) : literal (valuationOf b) 944 = decide (3 ≤ count942 b) := rfl
theorem meaning945 (b : Nat → Bool) : literal (valuationOf b) 945 = decide (4 ≤ count942 b) := rfl
theorem meaning946 (b : Nat → Bool) : literal (valuationOf b) 946 = decide (5 ≤ count942 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (6 ≤ count942 b) := rfl
theorem meaning951 (b : Nat → Bool) : literal (valuationOf b) 951 = decide (2 ≤ count950 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (3 ≤ count950 b) := rfl
theorem meaning953 (b : Nat → Bool) : literal (valuationOf b) 953 = decide (4 ≤ count950 b) := rfl
theorem meaning954 (b : Nat → Bool) : literal (valuationOf b) 954 = decide (5 ≤ count950 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (6 ≤ count950 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (7 ≤ count950 b) := rfl
theorem meaning957 (b : Nat → Bool) : literal (valuationOf b) 957 = decide (8 ≤ count950 b) := rfl
theorem meaning958 (b : Nat → Bool) : literal (valuationOf b) 958 = decide (9 ≤ count950 b) := rfl
theorem meaning971 (b : Nat → Bool) : literal (valuationOf b) 971 = decide (6 ≤ count966 b) := rfl
theorem meaning972 (b : Nat → Bool) : literal (valuationOf b) 972 = decide (7 ≤ count966 b) := rfl
theorem meaning973 (b : Nat → Bool) : literal (valuationOf b) 973 = decide (8 ≤ count966 b) := rfl
theorem meaning974 (b : Nat → Bool) : literal (valuationOf b) 974 = decide (9 ≤ count966 b) := rfl
theorem meaning975 (b : Nat → Bool) : literal (valuationOf b) 975 = decide (10 ≤ count966 b) := rfl
theorem meaning976 (b : Nat → Bool) : literal (valuationOf b) 976 = decide (11 ≤ count966 b) := rfl
theorem meaning977 (b : Nat → Bool) : literal (valuationOf b) 977 = decide (12 ≤ count966 b) := rfl
theorem meaning978 (b : Nat → Bool) : literal (valuationOf b) 978 = decide (13 ≤ count966 b) := rfl
theorem meaning988 (b : Nat → Bool) : literal (valuationOf b) 988 = decide (1 ≤ count988 b) := rfl
theorem meaning989 (b : Nat → Bool) : literal (valuationOf b) 989 = decide (2 ≤ count988 b) := rfl
theorem meaning990 (b : Nat → Bool) : literal (valuationOf b) 990 = decide (1 ≤ count990 b) := rfl
theorem meaning991 (b : Nat → Bool) : literal (valuationOf b) 991 = decide (2 ≤ count990 b) := rfl
theorem meaning992 (b : Nat → Bool) : literal (valuationOf b) 992 = decide (3 ≤ count990 b) := rfl
theorem meaning993 (b : Nat → Bool) : literal (valuationOf b) 993 = decide (1 ≤ count993 b) := rfl
theorem meaning994 (b : Nat → Bool) : literal (valuationOf b) 994 = decide (2 ≤ count993 b) := rfl
theorem meaning995 (b : Nat → Bool) : literal (valuationOf b) 995 = decide (1 ≤ count995 b) := rfl
theorem meaning996 (b : Nat → Bool) : literal (valuationOf b) 996 = decide (2 ≤ count995 b) := rfl
theorem meaning997 (b : Nat → Bool) : literal (valuationOf b) 997 = decide (1 ≤ count997 b) := rfl
theorem meaning998 (b : Nat → Bool) : literal (valuationOf b) 998 = decide (2 ≤ count997 b) := rfl
theorem meaning999 (b : Nat → Bool) : literal (valuationOf b) 999 = decide (3 ≤ count997 b) := rfl
theorem meaning1000 (b : Nat → Bool) : literal (valuationOf b) 1000 = decide (4 ≤ count997 b) := rfl
theorem meaning1001 (b : Nat → Bool) : literal (valuationOf b) 1001 = decide (1 ≤ count1001 b) := rfl
theorem meaning1002 (b : Nat → Bool) : literal (valuationOf b) 1002 = decide (2 ≤ count1001 b) := rfl
theorem meaning1003 (b : Nat → Bool) : literal (valuationOf b) 1003 = decide (3 ≤ count1001 b) := rfl
theorem meaning1004 (b : Nat → Bool) : literal (valuationOf b) 1004 = decide (4 ≤ count1001 b) := rfl
theorem meaning1005 (b : Nat → Bool) : literal (valuationOf b) 1005 = decide (5 ≤ count1001 b) := rfl
theorem meaning1006 (b : Nat → Bool) : literal (valuationOf b) 1006 = decide (6 ≤ count1001 b) := rfl
theorem meaning1008 (b : Nat → Bool) : literal (valuationOf b) 1008 = decide (1 ≤ count1008 b) := rfl
theorem meaning1009 (b : Nat → Bool) : literal (valuationOf b) 1009 = decide (2 ≤ count1008 b) := rfl
theorem meaning1010 (b : Nat → Bool) : literal (valuationOf b) 1010 = decide (1 ≤ count1010 b) := rfl
theorem meaning1011 (b : Nat → Bool) : literal (valuationOf b) 1011 = decide (2 ≤ count1010 b) := rfl
theorem meaning1012 (b : Nat → Bool) : literal (valuationOf b) 1012 = decide (1 ≤ count1012 b) := rfl
theorem meaning1013 (b : Nat → Bool) : literal (valuationOf b) 1013 = decide (2 ≤ count1012 b) := rfl
theorem meaning1014 (b : Nat → Bool) : literal (valuationOf b) 1014 = decide (3 ≤ count1012 b) := rfl
theorem meaning1015 (b : Nat → Bool) : literal (valuationOf b) 1015 = decide (4 ≤ count1012 b) := rfl
theorem meaning1016 (b : Nat → Bool) : literal (valuationOf b) 1016 = decide (1 ≤ count1016 b) := rfl
theorem meaning1017 (b : Nat → Bool) : literal (valuationOf b) 1017 = decide (2 ≤ count1016 b) := rfl
theorem meaning1018 (b : Nat → Bool) : literal (valuationOf b) 1018 = decide (1 ≤ count1018 b) := rfl
theorem meaning1019 (b : Nat → Bool) : literal (valuationOf b) 1019 = decide (2 ≤ count1018 b) := rfl
theorem meaning1020 (b : Nat → Bool) : literal (valuationOf b) 1020 = decide (1 ≤ count1020 b) := rfl
theorem meaning1021 (b : Nat → Bool) : literal (valuationOf b) 1021 = decide (2 ≤ count1020 b) := rfl
theorem meaning1022 (b : Nat → Bool) : literal (valuationOf b) 1022 = decide (3 ≤ count1020 b) := rfl
theorem meaning1023 (b : Nat → Bool) : literal (valuationOf b) 1023 = decide (4 ≤ count1020 b) := rfl
theorem meaning1024 (b : Nat → Bool) : literal (valuationOf b) 1024 = decide (1 ≤ count1024 b) := rfl
theorem meaning1025 (b : Nat → Bool) : literal (valuationOf b) 1025 = decide (2 ≤ count1024 b) := rfl
theorem meaning1026 (b : Nat → Bool) : literal (valuationOf b) 1026 = decide (3 ≤ count1024 b) := rfl
theorem meaning1027 (b : Nat → Bool) : literal (valuationOf b) 1027 = decide (4 ≤ count1024 b) := rfl
theorem meaning1028 (b : Nat → Bool) : literal (valuationOf b) 1028 = decide (5 ≤ count1024 b) := rfl
theorem meaning1029 (b : Nat → Bool) : literal (valuationOf b) 1029 = decide (6 ≤ count1024 b) := rfl
theorem meaning1030 (b : Nat → Bool) : literal (valuationOf b) 1030 = decide (7 ≤ count1024 b) := rfl
theorem meaning1032 (b : Nat → Bool) : literal (valuationOf b) 1032 = decide (1 ≤ count1032 b) := rfl
theorem meaning1033 (b : Nat → Bool) : literal (valuationOf b) 1033 = decide (2 ≤ count1032 b) := rfl
theorem meaning1034 (b : Nat → Bool) : literal (valuationOf b) 1034 = decide (3 ≤ count1032 b) := rfl
theorem meaning1035 (b : Nat → Bool) : literal (valuationOf b) 1035 = decide (4 ≤ count1032 b) := rfl
theorem meaning1036 (b : Nat → Bool) : literal (valuationOf b) 1036 = decide (5 ≤ count1032 b) := rfl
theorem meaning1037 (b : Nat → Bool) : literal (valuationOf b) 1037 = decide (6 ≤ count1032 b) := rfl
theorem meaning1038 (b : Nat → Bool) : literal (valuationOf b) 1038 = decide (7 ≤ count1032 b) := rfl
theorem meaning1039 (b : Nat → Bool) : literal (valuationOf b) 1039 = decide (8 ≤ count1032 b) := rfl
theorem meaning1040 (b : Nat → Bool) : literal (valuationOf b) 1040 = decide (9 ≤ count1032 b) := rfl
theorem meaning1047 (b : Nat → Bool) : literal (valuationOf b) 1047 = decide (1 ≤ count1047 b) := rfl
theorem meaning1048 (b : Nat → Bool) : literal (valuationOf b) 1048 = decide (2 ≤ count1047 b) := rfl
theorem meaning1049 (b : Nat → Bool) : literal (valuationOf b) 1049 = decide (1 ≤ count1049 b) := rfl
theorem meaning1050 (b : Nat → Bool) : literal (valuationOf b) 1050 = decide (2 ≤ count1049 b) := rfl
theorem meaning1051 (b : Nat → Bool) : literal (valuationOf b) 1051 = decide (1 ≤ count1051 b) := rfl
theorem meaning1052 (b : Nat → Bool) : literal (valuationOf b) 1052 = decide (2 ≤ count1051 b) := rfl
theorem meaning1053 (b : Nat → Bool) : literal (valuationOf b) 1053 = decide (3 ≤ count1051 b) := rfl
theorem meaning1054 (b : Nat → Bool) : literal (valuationOf b) 1054 = decide (4 ≤ count1051 b) := rfl
theorem meaning1055 (b : Nat → Bool) : literal (valuationOf b) 1055 = decide (1 ≤ count1055 b) := rfl
theorem meaning1056 (b : Nat → Bool) : literal (valuationOf b) 1056 = decide (2 ≤ count1055 b) := rfl
theorem meaning1057 (b : Nat → Bool) : literal (valuationOf b) 1057 = decide (1 ≤ count1057 b) := rfl
theorem meaning1058 (b : Nat → Bool) : literal (valuationOf b) 1058 = decide (2 ≤ count1057 b) := rfl
theorem meaning1059 (b : Nat → Bool) : literal (valuationOf b) 1059 = decide (1 ≤ count1059 b) := rfl
theorem meaning1060 (b : Nat → Bool) : literal (valuationOf b) 1060 = decide (2 ≤ count1059 b) := rfl
theorem meaning1061 (b : Nat → Bool) : literal (valuationOf b) 1061 = decide (3 ≤ count1059 b) := rfl
theorem meaning1062 (b : Nat → Bool) : literal (valuationOf b) 1062 = decide (4 ≤ count1059 b) := rfl
theorem meaning1063 (b : Nat → Bool) : literal (valuationOf b) 1063 = decide (1 ≤ count1063 b) := rfl
theorem meaning1064 (b : Nat → Bool) : literal (valuationOf b) 1064 = decide (2 ≤ count1063 b) := rfl
theorem meaning1065 (b : Nat → Bool) : literal (valuationOf b) 1065 = decide (3 ≤ count1063 b) := rfl
theorem meaning1066 (b : Nat → Bool) : literal (valuationOf b) 1066 = decide (4 ≤ count1063 b) := rfl
theorem meaning1067 (b : Nat → Bool) : literal (valuationOf b) 1067 = decide (5 ≤ count1063 b) := rfl
theorem meaning1068 (b : Nat → Bool) : literal (valuationOf b) 1068 = decide (6 ≤ count1063 b) := rfl
theorem meaning1069 (b : Nat → Bool) : literal (valuationOf b) 1069 = decide (7 ≤ count1063 b) := rfl
theorem meaning1071 (b : Nat → Bool) : literal (valuationOf b) 1071 = decide (1 ≤ count1071 b) := rfl
theorem meaning1072 (b : Nat → Bool) : literal (valuationOf b) 1072 = decide (2 ≤ count1071 b) := rfl
theorem meaning1073 (b : Nat → Bool) : literal (valuationOf b) 1073 = decide (1 ≤ count1073 b) := rfl
theorem meaning1074 (b : Nat → Bool) : literal (valuationOf b) 1074 = decide (2 ≤ count1073 b) := rfl
theorem meaning1075 (b : Nat → Bool) : literal (valuationOf b) 1075 = decide (1 ≤ count1075 b) := rfl
theorem meaning1076 (b : Nat → Bool) : literal (valuationOf b) 1076 = decide (2 ≤ count1075 b) := rfl
theorem meaning1077 (b : Nat → Bool) : literal (valuationOf b) 1077 = decide (3 ≤ count1075 b) := rfl
theorem meaning1078 (b : Nat → Bool) : literal (valuationOf b) 1078 = decide (4 ≤ count1075 b) := rfl
theorem meaning1079 (b : Nat → Bool) : literal (valuationOf b) 1079 = decide (1 ≤ count1079 b) := rfl
theorem meaning1080 (b : Nat → Bool) : literal (valuationOf b) 1080 = decide (2 ≤ count1079 b) := rfl
theorem meaning1081 (b : Nat → Bool) : literal (valuationOf b) 1081 = decide (1 ≤ count1081 b) := rfl
theorem meaning1082 (b : Nat → Bool) : literal (valuationOf b) 1082 = decide (2 ≤ count1081 b) := rfl
theorem meaning1083 (b : Nat → Bool) : literal (valuationOf b) 1083 = decide (1 ≤ count1083 b) := rfl
theorem meaning1084 (b : Nat → Bool) : literal (valuationOf b) 1084 = decide (2 ≤ count1083 b) := rfl
theorem meaning1085 (b : Nat → Bool) : literal (valuationOf b) 1085 = decide (3 ≤ count1083 b) := rfl
theorem meaning1086 (b : Nat → Bool) : literal (valuationOf b) 1086 = decide (4 ≤ count1083 b) := rfl
theorem meaning1087 (b : Nat → Bool) : literal (valuationOf b) 1087 = decide (1 ≤ count1087 b) := rfl
theorem meaning1088 (b : Nat → Bool) : literal (valuationOf b) 1088 = decide (2 ≤ count1087 b) := rfl
theorem meaning1089 (b : Nat → Bool) : literal (valuationOf b) 1089 = decide (3 ≤ count1087 b) := rfl
theorem meaning1090 (b : Nat → Bool) : literal (valuationOf b) 1090 = decide (4 ≤ count1087 b) := rfl
theorem meaning1091 (b : Nat → Bool) : literal (valuationOf b) 1091 = decide (5 ≤ count1087 b) := rfl
theorem meaning1092 (b : Nat → Bool) : literal (valuationOf b) 1092 = decide (6 ≤ count1087 b) := rfl
theorem meaning1093 (b : Nat → Bool) : literal (valuationOf b) 1093 = decide (7 ≤ count1087 b) := rfl
theorem meaning1094 (b : Nat → Bool) : literal (valuationOf b) 1094 = decide (8 ≤ count1087 b) := rfl
theorem meaning1097 (b : Nat → Bool) : literal (valuationOf b) 1097 = decide (3 ≤ count1095 b) := rfl
theorem meaning1098 (b : Nat → Bool) : literal (valuationOf b) 1098 = decide (4 ≤ count1095 b) := rfl
theorem meaning1099 (b : Nat → Bool) : literal (valuationOf b) 1099 = decide (5 ≤ count1095 b) := rfl
theorem meaning1100 (b : Nat → Bool) : literal (valuationOf b) 1100 = decide (6 ≤ count1095 b) := rfl
theorem meaning1101 (b : Nat → Bool) : literal (valuationOf b) 1101 = decide (7 ≤ count1095 b) := rfl
theorem meaning1102 (b : Nat → Bool) : literal (valuationOf b) 1102 = decide (8 ≤ count1095 b) := rfl
theorem meaning1103 (b : Nat → Bool) : literal (valuationOf b) 1103 = decide (9 ≤ count1095 b) := rfl
theorem meaning1104 (b : Nat → Bool) : literal (valuationOf b) 1104 = decide (10 ≤ count1095 b) := rfl
theorem meaning1105 (b : Nat → Bool) : literal (valuationOf b) 1105 = decide (11 ≤ count1095 b) := rfl
theorem meaning1106 (b : Nat → Bool) : literal (valuationOf b) 1106 = decide (12 ≤ count1095 b) := rfl
theorem meaning1119 (b : Nat → Bool) : literal (valuationOf b) 1119 = decide (9 ≤ count1111 b) := rfl
theorem meaning1120 (b : Nat → Bool) : literal (valuationOf b) 1120 = decide (10 ≤ count1111 b) := rfl
theorem meaning1121 (b : Nat → Bool) : literal (valuationOf b) 1121 = decide (11 ≤ count1111 b) := rfl
theorem meaning1122 (b : Nat → Bool) : literal (valuationOf b) 1122 = decide (12 ≤ count1111 b) := rfl
theorem meaning1123 (b : Nat → Bool) : literal (valuationOf b) 1123 = decide (13 ≤ count1111 b) := rfl
theorem meaning1124 (b : Nat → Bool) : literal (valuationOf b) 1124 = decide (14 ≤ count1111 b) := rfl
theorem meaning1125 (b : Nat → Bool) : literal (valuationOf b) 1125 = decide (15 ≤ count1111 b) := rfl
theorem meaning1126 (b : Nat → Bool) : literal (valuationOf b) 1126 = decide (16 ≤ count1111 b) := rfl
theorem meaning1154 (b : Nat → Bool) : literal (valuationOf b) 1154 = decide (22 ≤ count1133 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (2 ≤ count1505 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (3 ≤ count1507 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (2 ≤ count1512 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (2 ≤ count1514 b) := rfl
theorem meaning1520 (b : Nat → Bool) : literal (valuationOf b) 1520 = decide (3 ≤ count1518 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (5 ≤ count1518 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (2 ≤ count1527 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (2 ≤ count1529 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (1 ≤ count1533 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (1 ≤ count1535 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (2 ≤ count1537 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (2 ≤ count1541 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (4 ≤ count1541 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (7 ≤ count1549 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (1 ≤ count1566 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (2 ≤ count1568 b) := rfl
theorem meaning1574 (b : Nat → Bool) : literal (valuationOf b) 1574 = decide (1 ≤ count1574 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (1 ≤ count1576 b) := rfl
theorem meaning1582 (b : Nat → Bool) : literal (valuationOf b) 1582 = decide (3 ≤ count1580 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (1 ≤ count1596 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (1 ≤ count1598 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (1 ≤ count1600 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (1 ≤ count1604 b) := rfl
theorem meaning1615 (b : Nat → Bool) : literal (valuationOf b) 1615 = decide (4 ≤ count1612 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (11 ≤ count1628 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (1 ≤ count1650 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (1 ≤ count1652 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (1 ≤ count1655 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (1 ≤ count1657 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (2 ≤ count1657 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (1 ≤ count1659 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (2 ≤ count1659 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (1 ≤ count1663 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (2 ≤ count1663 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (1 ≤ count1670 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (1 ≤ count1672 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (1 ≤ count1674 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (2 ≤ count1674 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (1 ≤ count1678 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (1 ≤ count1682 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (2 ≤ count1686 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (3 ≤ count1686 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (4 ≤ count1694 b) := rfl
theorem meaning1709 (b : Nat → Bool) : literal (valuationOf b) 1709 = decide (1 ≤ count1709 b) := rfl
theorem meaning1711 (b : Nat → Bool) : literal (valuationOf b) 1711 = decide (1 ≤ count1711 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (2 ≤ count1713 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (1 ≤ count1717 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (1 ≤ count1719 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (2 ≤ count1721 b) := rfl
theorem meaning1728 (b : Nat → Bool) : literal (valuationOf b) 1728 = decide (4 ≤ count1725 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (1 ≤ count1733 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (1 ≤ count1735 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (2 ≤ count1735 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (1 ≤ count1737 b) := rfl
theorem meaning1738 (b : Nat → Bool) : literal (valuationOf b) 1738 = decide (2 ≤ count1737 b) := rfl
theorem meaning1739 (b : Nat → Bool) : literal (valuationOf b) 1739 = decide (3 ≤ count1737 b) := rfl
theorem meaning1741 (b : Nat → Bool) : literal (valuationOf b) 1741 = decide (1 ≤ count1741 b) := rfl
theorem meaning1743 (b : Nat → Bool) : literal (valuationOf b) 1743 = decide (1 ≤ count1743 b) := rfl
theorem meaning1745 (b : Nat → Bool) : literal (valuationOf b) 1745 = decide (1 ≤ count1745 b) := rfl
theorem meaning1746 (b : Nat → Bool) : literal (valuationOf b) 1746 = decide (2 ≤ count1745 b) := rfl
theorem meaning1751 (b : Nat → Bool) : literal (valuationOf b) 1751 = decide (3 ≤ count1749 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (7 ≤ count1757 b) := rfl
theorem meaning1783 (b : Nat → Bool) : literal (valuationOf b) 1783 = decide (11 ≤ count1773 b) := rfl
theorem meaning1816 (b : Nat → Bool) : literal (valuationOf b) 1816 = decide (22 ≤ count1795 b) := rfl
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
end Snake9.Regrowth.E112153
