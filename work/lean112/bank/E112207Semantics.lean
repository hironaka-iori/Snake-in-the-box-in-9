import E112207Data
namespace Snake9.Regrowth.E112207
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 117 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (6 : Vertex)) else decide (InPath q (8 : Vertex))) else (if i < 6 then decide (InPath q (11 : Vertex)) else decide (InPath q (13 : Vertex))))) else (if i < 10 then (if i < 8 then decide (InPath q (15 : Vertex)) else (if i < 9 then decide (InPath q (17 : Vertex)) else decide (InPath q (18 : Vertex)))) else (if i < 12 then (if i < 11 then decide (InPath q (19 : Vertex)) else decide (InPath q (22 : Vertex))) else (if i < 13 then decide (InPath q (28 : Vertex)) else decide (InPath q (29 : Vertex)))))) else (if i < 21 then (if i < 17 then (if i < 15 then decide (InPath q (30 : Vertex)) else (if i < 16 then decide (InPath q (128 : Vertex)) else decide (InPath q (130 : Vertex)))) else (if i < 19 then (if i < 18 then decide (InPath q (132 : Vertex)) else decide (InPath q (134 : Vertex))) else (if i < 20 then decide (InPath q (135 : Vertex)) else decide (InPath q (136 : Vertex))))) else (if i < 25 then (if i < 23 then (if i < 22 then decide (InPath q (137 : Vertex)) else decide (InPath q (138 : Vertex))) else (if i < 24 then decide (InPath q (140 : Vertex)) else decide (InPath q (142 : Vertex)))) else (if i < 27 then (if i < 26 then decide (InPath q (148 : Vertex)) else decide (InPath q (149 : Vertex))) else (if i < 28 then decide (InPath q (151 : Vertex)) else decide (InPath q (153 : Vertex))))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then decide (InPath q (154 : Vertex)) else (if i < 31 then decide (InPath q (155 : Vertex)) else decide (InPath q (157 : Vertex)))) else (if i < 34 then (if i < 33 then decide (InPath q (159 : Vertex)) else decide (InPath q (198 : Vertex))) else (if i < 35 then decide (InPath q (201 : Vertex)) else decide (InPath q (205 : Vertex))))) else (if i < 39 then (if i < 37 then decide (InPath q (207 : Vertex)) else (if i < 38 then decide (InPath q (214 : Vertex)) else decide (InPath q (218 : Vertex)))) else (if i < 41 then (if i < 40 then decide (InPath q (220 : Vertex)) else decide (InPath q (221 : Vertex))) else (if i < 42 then decide (InPath q (222 : Vertex)) else decide (InPath q (226 : Vertex)))))) else (if i < 50 then (if i < 46 then (if i < 44 then decide (InPath q (230 : Vertex)) else (if i < 45 then decide (InPath q (238 : Vertex)) else decide (InPath q (256 : Vertex)))) else (if i < 48 then (if i < 47 then decide (InPath q (257 : Vertex)) else decide (InPath q (258 : Vertex))) else (if i < 49 then decide (InPath q (260 : Vertex)) else decide (InPath q (261 : Vertex))))) else (if i < 54 then (if i < 52 then (if i < 51 then decide (InPath q (262 : Vertex)) else decide (InPath q (263 : Vertex))) else (if i < 53 then decide (InPath q (264 : Vertex)) else decide (InPath q (266 : Vertex)))) else (if i < 56 then (if i < 55 then decide (InPath q (267 : Vertex)) else decide (InPath q (268 : Vertex))) else (if i < 57 then decide (InPath q (270 : Vertex)) else decide (InPath q (271 : Vertex)))))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then decide (InPath q (273 : Vertex)) else (if i < 60 then decide (InPath q (275 : Vertex)) else decide (InPath q (276 : Vertex)))) else (if i < 63 then (if i < 62 then decide (InPath q (277 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 64 then decide (InPath q (280 : Vertex)) else decide (InPath q (281 : Vertex))))) else (if i < 68 then (if i < 66 then decide (InPath q (282 : Vertex)) else (if i < 67 then decide (InPath q (283 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 70 then (if i < 69 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex))) else (if i < 71 then decide (InPath q (326 : Vertex)) else decide (InPath q (327 : Vertex)))))) else (if i < 79 then (if i < 75 then (if i < 73 then decide (InPath q (328 : Vertex)) else (if i < 74 then decide (InPath q (329 : Vertex)) else decide (InPath q (331 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (333 : Vertex)) else decide (InPath q (335 : Vertex))) else (if i < 78 then decide (InPath q (337 : Vertex)) else decide (InPath q (338 : Vertex))))) else (if i < 83 then (if i < 81 then (if i < 80 then decide (InPath q (339 : Vertex)) else decide (InPath q (342 : Vertex))) else (if i < 82 then decide (InPath q (346 : Vertex)) else decide (InPath q (348 : Vertex)))) else (if i < 85 then (if i < 84 then decide (InPath q (349 : Vertex)) else decide (InPath q (350 : Vertex))) else (if i < 86 then decide (InPath q (384 : Vertex)) else decide (InPath q (385 : Vertex))))))) else (if i < 102 then (if i < 94 then (if i < 90 then (if i < 88 then decide (InPath q (389 : Vertex)) else (if i < 89 then decide (InPath q (390 : Vertex)) else decide (InPath q (391 : Vertex)))) else (if i < 92 then (if i < 91 then decide (InPath q (392 : Vertex)) else decide (InPath q (393 : Vertex))) else (if i < 93 then decide (InPath q (395 : Vertex)) else decide (InPath q (397 : Vertex))))) else (if i < 98 then (if i < 96 then (if i < 95 then decide (InPath q (399 : Vertex)) else decide (InPath q (400 : Vertex))) else (if i < 97 then decide (InPath q (401 : Vertex)) else decide (InPath q (402 : Vertex)))) else (if i < 100 then (if i < 99 then decide (InPath q (403 : Vertex)) else decide (InPath q (406 : Vertex))) else (if i < 101 then decide (InPath q (410 : Vertex)) else decide (InPath q (412 : Vertex)))))) else (if i < 109 then (if i < 105 then (if i < 103 then decide (InPath q (413 : Vertex)) else (if i < 104 then decide (InPath q (414 : Vertex)) else decide (InPath q (480 : Vertex)))) else (if i < 107 then (if i < 106 then decide (InPath q (481 : Vertex)) else decide (InPath q (486 : Vertex))) else (if i < 108 then decide (InPath q (487 : Vertex)) else decide (InPath q (493 : Vertex))))) else (if i < 113 then (if i < 111 then (if i < 110 then decide (InPath q (495 : Vertex)) else decide (InPath q (497 : Vertex))) else (if i < 112 then decide (InPath q (498 : Vertex)) else decide (InPath q (499 : Vertex)))) else (if i < 115 then (if i < 114 then decide (InPath q (502 : Vertex)) else decide (InPath q (506 : Vertex))) else (if i < 116 then decide (InPath q (508 : Vertex)) else decide (InPath q (509 : Vertex))))))))) else (if i < 176 then (if i < 146 then (if i < 131 then (if i < 124 then (if i < 120 then (if i < 118 then decide (InPath q (510 : Vertex)) else (if i < 119 then decide (BallClauseLogic.Endpoint q (0 : Vertex)) else decide (BallClauseLogic.Endpoint q (1 : Vertex)))) else (if i < 122 then (if i < 121 then decide (BallClauseLogic.Endpoint q (6 : Vertex)) else decide (BallClauseLogic.Endpoint q (8 : Vertex))) else (if i < 123 then decide (BallClauseLogic.Endpoint q (11 : Vertex)) else decide (BallClauseLogic.Endpoint q (13 : Vertex))))) else (if i < 127 then (if i < 125 then decide (BallClauseLogic.Endpoint q (15 : Vertex)) else (if i < 126 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex)))) else (if i < 129 then (if i < 128 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (22 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex)))))) else (if i < 138 then (if i < 134 then (if i < 132 then decide (BallClauseLogic.Endpoint q (30 : Vertex)) else (if i < 133 then decide (BallClauseLogic.Endpoint q (128 : Vertex)) else decide (BallClauseLogic.Endpoint q (130 : Vertex)))) else (if i < 136 then (if i < 135 then decide (BallClauseLogic.Endpoint q (132 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex))) else (if i < 137 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex))))) else (if i < 142 then (if i < 140 then (if i < 139 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (138 : Vertex))) else (if i < 141 then decide (BallClauseLogic.Endpoint q (140 : Vertex)) else decide (BallClauseLogic.Endpoint q (142 : Vertex)))) else (if i < 144 then (if i < 143 then decide (BallClauseLogic.Endpoint q (148 : Vertex)) else decide (BallClauseLogic.Endpoint q (149 : Vertex))) else (if i < 145 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (153 : Vertex))))))) else (if i < 161 then (if i < 153 then (if i < 149 then (if i < 147 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else (if i < 148 then decide (BallClauseLogic.Endpoint q (155 : Vertex)) else decide (BallClauseLogic.Endpoint q (157 : Vertex)))) else (if i < 151 then (if i < 150 then decide (BallClauseLogic.Endpoint q (159 : Vertex)) else decide (BallClauseLogic.Endpoint q (198 : Vertex))) else (if i < 152 then decide (BallClauseLogic.Endpoint q (201 : Vertex)) else decide (BallClauseLogic.Endpoint q (205 : Vertex))))) else (if i < 157 then (if i < 155 then (if i < 154 then decide (BallClauseLogic.Endpoint q (207 : Vertex)) else decide (BallClauseLogic.Endpoint q (214 : Vertex))) else (if i < 156 then decide (BallClauseLogic.Endpoint q (218 : Vertex)) else decide (BallClauseLogic.Endpoint q (220 : Vertex)))) else (if i < 159 then (if i < 158 then decide (BallClauseLogic.Endpoint q (221 : Vertex)) else decide (BallClauseLogic.Endpoint q (222 : Vertex))) else (if i < 160 then decide (BallClauseLogic.Endpoint q (226 : Vertex)) else decide (BallClauseLogic.Endpoint q (230 : Vertex)))))) else (if i < 168 then (if i < 164 then (if i < 162 then decide (BallClauseLogic.Endpoint q (238 : Vertex)) else (if i < 163 then decide (BallClauseLogic.Endpoint q (256 : Vertex)) else decide (BallClauseLogic.Endpoint q (257 : Vertex)))) else (if i < 166 then (if i < 165 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex))) else (if i < 167 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (262 : Vertex))))) else (if i < 172 then (if i < 170 then (if i < 169 then decide (BallClauseLogic.Endpoint q (263 : Vertex)) else decide (BallClauseLogic.Endpoint q (264 : Vertex))) else (if i < 171 then decide (BallClauseLogic.Endpoint q (266 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex)))) else (if i < 174 then (if i < 173 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (270 : Vertex))) else (if i < 175 then decide (BallClauseLogic.Endpoint q (271 : Vertex)) else decide (BallClauseLogic.Endpoint q (273 : Vertex)))))))) else (if i < 205 then (if i < 190 then (if i < 183 then (if i < 179 then (if i < 177 then decide (BallClauseLogic.Endpoint q (275 : Vertex)) else (if i < 178 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (277 : Vertex)))) else (if i < 181 then (if i < 180 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (280 : Vertex))) else (if i < 182 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex))))) else (if i < 186 then (if i < 184 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else (if i < 185 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex)))) else (if i < 188 then (if i < 187 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (326 : Vertex))) else (if i < 189 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (328 : Vertex)))))) else (if i < 197 then (if i < 193 then (if i < 191 then decide (BallClauseLogic.Endpoint q (329 : Vertex)) else (if i < 192 then decide (BallClauseLogic.Endpoint q (331 : Vertex)) else decide (BallClauseLogic.Endpoint q (333 : Vertex)))) else (if i < 195 then (if i < 194 then decide (BallClauseLogic.Endpoint q (335 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex))) else (if i < 196 then decide (BallClauseLogic.Endpoint q (338 : Vertex)) else decide (BallClauseLogic.Endpoint q (339 : Vertex))))) else (if i < 201 then (if i < 199 then (if i < 198 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (346 : Vertex))) else (if i < 200 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else decide (BallClauseLogic.Endpoint q (349 : Vertex)))) else (if i < 203 then (if i < 202 then decide (BallClauseLogic.Endpoint q (350 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 204 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (389 : Vertex))))))) else (if i < 220 then (if i < 212 then (if i < 208 then (if i < 206 then decide (BallClauseLogic.Endpoint q (390 : Vertex)) else (if i < 207 then decide (BallClauseLogic.Endpoint q (391 : Vertex)) else decide (BallClauseLogic.Endpoint q (392 : Vertex)))) else (if i < 210 then (if i < 209 then decide (BallClauseLogic.Endpoint q (393 : Vertex)) else decide (BallClauseLogic.Endpoint q (395 : Vertex))) else (if i < 211 then decide (BallClauseLogic.Endpoint q (397 : Vertex)) else decide (BallClauseLogic.Endpoint q (399 : Vertex))))) else (if i < 216 then (if i < 214 then (if i < 213 then decide (BallClauseLogic.Endpoint q (400 : Vertex)) else decide (BallClauseLogic.Endpoint q (401 : Vertex))) else (if i < 215 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else decide (BallClauseLogic.Endpoint q (403 : Vertex)))) else (if i < 218 then (if i < 217 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (410 : Vertex))) else (if i < 219 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (413 : Vertex)))))) else (if i < 227 then (if i < 223 then (if i < 221 then decide (BallClauseLogic.Endpoint q (414 : Vertex)) else (if i < 222 then decide (BallClauseLogic.Endpoint q (480 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))) else (if i < 225 then (if i < 224 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (487 : Vertex))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (493 : Vertex)) else decide (BallClauseLogic.Endpoint q (495 : Vertex))))) else (if i < 231 then (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (497 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (499 : Vertex)) else decide (BallClauseLogic.Endpoint q (502 : Vertex)))) else (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (509 : Vertex)) else decide (BallClauseLogic.Endpoint q (510 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count235 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count237 (b : Nat → Bool) : Nat := countLit b [118, 119, 120]
def count239 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count241 (b : Nat → Bool) : Nat := countLit b [123, 124]
def count243 (b : Nat → Bool) : Nat := countLit b [121, 122, 123, 124]
def count245 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124]
def count247 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count249 (b : Nat → Bool) : Nat := countLit b [125, 126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count255 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131]
def count257 (b : Nat → Bool) : Nat := countLit b [125, 126, 127, 128, 129, 130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count267 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count269 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count283 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146]
def count285 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142, 143, 144, 145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]
def count289 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146]
def count291 (b : Nat → Bool) : Nat := countLit b [148, 149]
def count293 (b : Nat → Bool) : Nat := countLit b [147, 148, 149]
def count295 (b : Nat → Bool) : Nat := countLit b [150, 151]
def count297 (b : Nat → Bool) : Nat := countLit b [152, 153]
def count299 (b : Nat → Bool) : Nat := countLit b [150, 151, 152, 153]
def count301 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150, 151, 152, 153]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [154, 155, 156]
def count307 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count311 (b : Nat → Bool) : Nat := countLit b [157, 158, 159, 160]
def count313 (b : Nat → Bool) : Nat := countLit b [154, 155, 156, 157, 158, 159, 160]
def count315 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164, 165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [168, 169]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [168, 169, 170, 171, 172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]
def count345 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]
def count347 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175]
def count349 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [176, 177, 178]
def count353 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count355 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182]
def count361 (b : Nat → Bool) : Nat := countLit b [184, 185]
def count363 (b : Nat → Bool) : Nat := countLit b [183, 184, 185]
def count365 (b : Nat → Bool) : Nat := countLit b [186, 187]
def count367 (b : Nat → Bool) : Nat := countLit b [188, 189]
def count369 (b : Nat → Bool) : Nat := countLit b [186, 187, 188, 189]
def count371 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189]
def count373 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [190, 191, 192]
def count379 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [193, 194, 195, 196]
def count385 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196]
def count387 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [199, 200]
def count391 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200]
def count393 (b : Nat → Bool) : Nat := countLit b [201, 202]
def count395 (b : Nat → Bool) : Nat := countLit b [203, 204]
def count397 (b : Nat → Bool) : Nat := countLit b [201, 202, 203, 204]
def count399 (b : Nat → Bool) : Nat := countLit b [197, 198, 199, 200, 201, 202, 203, 204]
def count401 (b : Nat → Bool) : Nat := countLit b [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count403 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204]
def count405 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count407 (b : Nat → Bool) : Nat := countLit b [205, 206, 207]
def count409 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count411 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count413 (b : Nat → Bool) : Nat := countLit b [208, 209, 210, 211]
def count415 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211]
def count417 (b : Nat → Bool) : Nat := countLit b [213, 214]
def count419 (b : Nat → Bool) : Nat := countLit b [212, 213, 214]
def count421 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count425 (b : Nat → Bool) : Nat := countLit b [215, 216, 217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [212, 213, 214, 215, 216, 217, 218]
def count429 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218]
def count431 (b : Nat → Bool) : Nat := countLit b [220, 222]
def count433 (b : Nat → Bool) : Nat := countLit b [219, 220, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count439 (b : Nat → Bool) : Nat := countLit b [223, 224, 225, 226]
def count441 (b : Nat → Bool) : Nat := countLit b [219, 220, 222, 223, 224, 225, 226]
def count443 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count447 (b : Nat → Bool) : Nat := countLit b [227, 228, 229, 230]
def count449 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count451 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count453 (b : Nat → Bool) : Nat := countLit b [231, 232, 233, 234]
def count455 (b : Nat → Bool) : Nat := countLit b [227, 228, 229, 230, 231, 232, 233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]
def count459 (b : Nat → Bool) : Nat := countLit b [205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]
def count461 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]
def count463 (b : Nat → Bool) : Nat := countLit b [118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234]
def count465 (b : Nat → Bool) : Nat := countLit b [3, 7]
def count467 (b : Nat → Bool) : Nat := countLit b [1, 3, 7]
def count470 (b : Nat → Bool) : Nat := countLit b [8, 9]
def count472 (b : Nat → Bool) : Nat := countLit b [13, 14]
def count474 (b : Nat → Bool) : Nat := countLit b [8, 9, 13, 14]
def count478 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 8, 9, 13, 14]
def count485 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count487 (b : Nat → Bool) : Nat := countLit b [16, 17, 19]
def count490 (b : Nat → Bool) : Nat := countLit b [20, 24]
def count492 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count494 (b : Nat → Bool) : Nat := countLit b [20, 24, 26, 28]
def count498 (b : Nat → Bool) : Nat := countLit b [16, 17, 19, 20, 24, 26, 28]
def count505 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 8, 9, 13, 14, 16, 17, 19, 20, 24, 26, 28]
def count519 (b : Nat → Bool) : Nat := countLit b [32, 33]
def count521 (b : Nat → Bool) : Nat := countLit b [29, 32, 33]
def count524 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count526 (b : Nat → Bool) : Nat := countLit b [40, 41]
def count528 (b : Nat → Bool) : Nat := countLit b [34, 36, 40, 41]
def count532 (b : Nat → Bool) : Nat := countLit b [29, 32, 33, 34, 36, 40, 41]
def count539 (b : Nat → Bool) : Nat := countLit b [42, 44]
def count541 (b : Nat → Bool) : Nat := countLit b [46, 47]
def count543 (b : Nat → Bool) : Nat := countLit b [42, 44, 46, 47]
def count547 (b : Nat → Bool) : Nat := countLit b [48, 51]
def count549 (b : Nat → Bool) : Nat := countLit b [52, 54]
def count551 (b : Nat → Bool) : Nat := countLit b [48, 51, 52, 54]
def count555 (b : Nat → Bool) : Nat := countLit b [42, 44, 46, 47, 48, 51, 52, 54]
def count563 (b : Nat → Bool) : Nat := countLit b [29, 32, 33, 34, 36, 40, 41, 42, 44, 46, 47, 48, 51, 52, 54]
def count578 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 8, 9, 13, 14, 16, 17, 19, 20, 24, 26, 28, 29, 32, 33, 34, 36, 40, 41, 42, 44, 46, 47, 48, 51, 52, 54]
def count607 (b : Nat → Bool) : Nat := countLit b [59, 61]
def count609 (b : Nat → Bool) : Nat := countLit b [56, 59, 61]
def count612 (b : Nat → Bool) : Nat := countLit b [64, 65]
def count614 (b : Nat → Bool) : Nat := countLit b [67, 68]
def count616 (b : Nat → Bool) : Nat := countLit b [64, 65, 67, 68]
def count620 (b : Nat → Bool) : Nat := countLit b [56, 59, 61, 64, 65, 67, 68]
def count627 (b : Nat → Bool) : Nat := countLit b [70, 73]
def count629 (b : Nat → Bool) : Nat := countLit b [76, 77]
def count631 (b : Nat → Bool) : Nat := countLit b [70, 73, 76, 77]
def count635 (b : Nat → Bool) : Nat := countLit b [78, 83]
def count637 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count639 (b : Nat → Bool) : Nat := countLit b [78, 83, 84, 85]
def count643 (b : Nat → Bool) : Nat := countLit b [70, 73, 76, 77, 78, 83, 84, 85]
def count651 (b : Nat → Bool) : Nat := countLit b [56, 59, 61, 64, 65, 67, 68, 70, 73, 76, 77, 78, 83, 84, 85]
def count666 (b : Nat → Bool) : Nat := countLit b [88, 91]
def count668 (b : Nat → Bool) : Nat := countLit b [87, 88, 91]
def count671 (b : Nat → Bool) : Nat := countLit b [94, 96]
def count673 (b : Nat → Bool) : Nat := countLit b [97, 102]
def count675 (b : Nat → Bool) : Nat := countLit b [94, 96, 97, 102]
def count679 (b : Nat → Bool) : Nat := countLit b [87, 88, 91, 94, 96, 97, 102]
def count686 (b : Nat → Bool) : Nat := countLit b [103, 104]
def count688 (b : Nat → Bool) : Nat := countLit b [106, 109]
def count690 (b : Nat → Bool) : Nat := countLit b [103, 104, 106, 109]
def count694 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count696 (b : Nat → Bool) : Nat := countLit b [116, 117]
def count698 (b : Nat → Bool) : Nat := countLit b [110, 111, 116, 117]
def count702 (b : Nat → Bool) : Nat := countLit b [103, 104, 106, 109, 110, 111, 116, 117]
def count710 (b : Nat → Bool) : Nat := countLit b [87, 88, 91, 94, 96, 97, 102, 103, 104, 106, 109, 110, 111, 116, 117]
def count725 (b : Nat → Bool) : Nat := countLit b [56, 59, 61, 64, 65, 67, 68, 70, 73, 76, 77, 78, 83, 84, 85, 87, 88, 91, 94, 96, 97, 102, 103, 104, 106, 109, 110, 111, 116, 117]
def count755 (b : Nat → Bool) : Nat := countLit b [1, 3, 7, 8, 9, 13, 14, 16, 17, 19, 20, 24, 26, 28, 29, 32, 33, 34, 36, 40, 41, 42, 44, 46, 47, 48, 51, 52, 54, 56, 59, 61, 64, 65, 67, 68, 70, 73, 76, 77, 78, 83, 84, 85, 87, 88, 91, 94, 96, 97, 102, 103, 104, 106, 109, 110, 111, 116, 117]
def count797 (b : Nat → Bool) : Nat := countLit b [-3, -7]
def count799 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7]
def count802 (b : Nat → Bool) : Nat := countLit b [-8, -9]
def count804 (b : Nat → Bool) : Nat := countLit b [-13, -14]
def count806 (b : Nat → Bool) : Nat := countLit b [-8, -9, -13, -14]
def count810 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -8, -9, -13, -14]
def count817 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count819 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19]
def count822 (b : Nat → Bool) : Nat := countLit b [-20, -24]
def count824 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count826 (b : Nat → Bool) : Nat := countLit b [-20, -24, -26, -28]
def count830 (b : Nat → Bool) : Nat := countLit b [-16, -17, -19, -20, -24, -26, -28]
def count837 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28]
def count851 (b : Nat → Bool) : Nat := countLit b [-32, -33]
def count853 (b : Nat → Bool) : Nat := countLit b [-29, -32, -33]
def count856 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count858 (b : Nat → Bool) : Nat := countLit b [-40, -41]
def count860 (b : Nat → Bool) : Nat := countLit b [-34, -36, -40, -41]
def count864 (b : Nat → Bool) : Nat := countLit b [-29, -32, -33, -34, -36, -40, -41]
def count871 (b : Nat → Bool) : Nat := countLit b [-42, -44]
def count873 (b : Nat → Bool) : Nat := countLit b [-46, -47]
def count875 (b : Nat → Bool) : Nat := countLit b [-42, -44, -46, -47]
def count879 (b : Nat → Bool) : Nat := countLit b [-48, -51]
def count881 (b : Nat → Bool) : Nat := countLit b [-52, -54]
def count883 (b : Nat → Bool) : Nat := countLit b [-48, -51, -52, -54]
def count887 (b : Nat → Bool) : Nat := countLit b [-42, -44, -46, -47, -48, -51, -52, -54]
def count895 (b : Nat → Bool) : Nat := countLit b [-29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]
def count910 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54]
def count929 (b : Nat → Bool) : Nat := countLit b [-59, -61]
def count931 (b : Nat → Bool) : Nat := countLit b [-56, -59, -61]
def count934 (b : Nat → Bool) : Nat := countLit b [-64, -65]
def count936 (b : Nat → Bool) : Nat := countLit b [-67, -68]
def count938 (b : Nat → Bool) : Nat := countLit b [-64, -65, -67, -68]
def count942 (b : Nat → Bool) : Nat := countLit b [-56, -59, -61, -64, -65, -67, -68]
def count949 (b : Nat → Bool) : Nat := countLit b [-70, -73]
def count951 (b : Nat → Bool) : Nat := countLit b [-76, -77]
def count953 (b : Nat → Bool) : Nat := countLit b [-70, -73, -76, -77]
def count957 (b : Nat → Bool) : Nat := countLit b [-78, -83]
def count959 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count961 (b : Nat → Bool) : Nat := countLit b [-78, -83, -84, -85]
def count965 (b : Nat → Bool) : Nat := countLit b [-70, -73, -76, -77, -78, -83, -84, -85]
def count973 (b : Nat → Bool) : Nat := countLit b [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -83, -84, -85]
def count988 (b : Nat → Bool) : Nat := countLit b [-88, -91]
def count990 (b : Nat → Bool) : Nat := countLit b [-87, -88, -91]
def count993 (b : Nat → Bool) : Nat := countLit b [-94, -96]
def count995 (b : Nat → Bool) : Nat := countLit b [-97, -102]
def count997 (b : Nat → Bool) : Nat := countLit b [-94, -96, -97, -102]
def count1001 (b : Nat → Bool) : Nat := countLit b [-87, -88, -91, -94, -96, -97, -102]
def count1008 (b : Nat → Bool) : Nat := countLit b [-103, -104]
def count1010 (b : Nat → Bool) : Nat := countLit b [-106, -109]
def count1012 (b : Nat → Bool) : Nat := countLit b [-103, -104, -106, -109]
def count1016 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1018 (b : Nat → Bool) : Nat := countLit b [-116, -117]
def count1020 (b : Nat → Bool) : Nat := countLit b [-110, -111, -116, -117]
def count1024 (b : Nat → Bool) : Nat := countLit b [-103, -104, -106, -109, -110, -111, -116, -117]
def count1032 (b : Nat → Bool) : Nat := countLit b [-87, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]
def count1047 (b : Nat → Bool) : Nat := countLit b [-56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -83, -84, -85, -87, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]
def count1066 (b : Nat → Bool) : Nat := countLit b [-1, -3, -7, -8, -9, -13, -14, -16, -17, -19, -20, -24, -26, -28, -29, -32, -33, -34, -36, -40, -41, -42, -44, -46, -47, -48, -51, -52, -54, -56, -59, -61, -64, -65, -67, -68, -70, -73, -76, -77, -78, -83, -84, -85, -87, -88, -91, -94, -96, -97, -102, -103, -104, -106, -109, -110, -111, -116, -117]
def count1085 (b : Nat → Bool) : Nat := countLit b [4, 5]
def count1087 (b : Nat → Bool) : Nat := countLit b [2, 4, 5]
def count1090 (b : Nat → Bool) : Nat := countLit b [6, 10]
def count1092 (b : Nat → Bool) : Nat := countLit b [11, 12]
def count1094 (b : Nat → Bool) : Nat := countLit b [6, 10, 11, 12]
def count1098 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 10, 11, 12]
def count1105 (b : Nat → Bool) : Nat := countLit b [18, 21]
def count1107 (b : Nat → Bool) : Nat := countLit b [15, 18, 21]
def count1110 (b : Nat → Bool) : Nat := countLit b [22, 23]
def count1112 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count1114 (b : Nat → Bool) : Nat := countLit b [22, 23, 25, 27]
def count1118 (b : Nat → Bool) : Nat := countLit b [15, 18, 21, 22, 23, 25, 27]
def count1125 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 10, 11, 12, 15, 18, 21, 22, 23, 25, 27]
def count1139 (b : Nat → Bool) : Nat := countLit b [31, 35]
def count1141 (b : Nat → Bool) : Nat := countLit b [30, 31, 35]
def count1144 (b : Nat → Bool) : Nat := countLit b [37, 38]
def count1146 (b : Nat → Bool) : Nat := countLit b [39, 43]
def count1148 (b : Nat → Bool) : Nat := countLit b [37, 38, 39, 43]
def count1152 (b : Nat → Bool) : Nat := countLit b [30, 31, 35, 37, 38, 39, 43]
def count1159 (b : Nat → Bool) : Nat := countLit b [45, 49]
def count1161 (b : Nat → Bool) : Nat := countLit b [50, 53]
def count1163 (b : Nat → Bool) : Nat := countLit b [45, 49, 50, 53]
def count1167 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count1169 (b : Nat → Bool) : Nat := countLit b [58, 60]
def count1171 (b : Nat → Bool) : Nat := countLit b [55, 57, 58, 60]
def count1175 (b : Nat → Bool) : Nat := countLit b [45, 49, 50, 53, 55, 57, 58, 60]
def count1183 (b : Nat → Bool) : Nat := countLit b [30, 31, 35, 37, 38, 39, 43, 45, 49, 50, 53, 55, 57, 58, 60]
def count1198 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 10, 11, 12, 15, 18, 21, 22, 23, 25, 27, 30, 31, 35, 37, 38, 39, 43, 45, 49, 50, 53, 55, 57, 58, 60]
def count1227 (b : Nat → Bool) : Nat := countLit b [63, 66]
def count1229 (b : Nat → Bool) : Nat := countLit b [62, 63, 66]
def count1232 (b : Nat → Bool) : Nat := countLit b [69, 71]
def count1234 (b : Nat → Bool) : Nat := countLit b [72, 74]
def count1236 (b : Nat → Bool) : Nat := countLit b [69, 71, 72, 74]
def count1240 (b : Nat → Bool) : Nat := countLit b [62, 63, 66, 69, 71, 72, 74]
def count1247 (b : Nat → Bool) : Nat := countLit b [79, 80]
def count1249 (b : Nat → Bool) : Nat := countLit b [75, 79, 80]
def count1252 (b : Nat → Bool) : Nat := countLit b [81, 82]
def count1254 (b : Nat → Bool) : Nat := countLit b [86, 89]
def count1256 (b : Nat → Bool) : Nat := countLit b [81, 82, 86, 89]
def count1260 (b : Nat → Bool) : Nat := countLit b [75, 79, 80, 81, 82, 86, 89]
def count1267 (b : Nat → Bool) : Nat := countLit b [62, 63, 66, 69, 71, 72, 74, 75, 79, 80, 81, 82, 86, 89]
def count1281 (b : Nat → Bool) : Nat := countLit b [92, 93]
def count1283 (b : Nat → Bool) : Nat := countLit b [90, 92, 93]
def count1286 (b : Nat → Bool) : Nat := countLit b [95, 98]
def count1288 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count1290 (b : Nat → Bool) : Nat := countLit b [95, 98, 99, 100]
def count1294 (b : Nat → Bool) : Nat := countLit b [90, 92, 93, 95, 98, 99, 100]
def count1301 (b : Nat → Bool) : Nat := countLit b [101, 105]
def count1303 (b : Nat → Bool) : Nat := countLit b [107, 108]
def count1305 (b : Nat → Bool) : Nat := countLit b [101, 105, 107, 108]
def count1309 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count1311 (b : Nat → Bool) : Nat := countLit b [114, 115]
def count1313 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 115]
def count1317 (b : Nat → Bool) : Nat := countLit b [101, 105, 107, 108, 112, 113, 114, 115]
def count1325 (b : Nat → Bool) : Nat := countLit b [90, 92, 93, 95, 98, 99, 100, 101, 105, 107, 108, 112, 113, 114, 115]
def count1340 (b : Nat → Bool) : Nat := countLit b [62, 63, 66, 69, 71, 72, 74, 75, 79, 80, 81, 82, 86, 89, 90, 92, 93, 95, 98, 99, 100, 101, 105, 107, 108, 112, 113, 114, 115]
def count1369 (b : Nat → Bool) : Nat := countLit b [2, 4, 5, 6, 10, 11, 12, 15, 18, 21, 22, 23, 25, 27, 30, 31, 35, 37, 38, 39, 43, 45, 49, 50, 53, 55, 57, 58, 60, 62, 63, 66, 69, 71, 72, 74, 75, 79, 80, 81, 82, 86, 89, 90, 92, 93, 95, 98, 99, 100, 101, 105, 107, 108, 112, 113, 114, 115]
def count1411 (b : Nat → Bool) : Nat := countLit b [-4, -5]
def count1413 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5]
def count1416 (b : Nat → Bool) : Nat := countLit b [-6, -10]
def count1418 (b : Nat → Bool) : Nat := countLit b [-11, -12]
def count1420 (b : Nat → Bool) : Nat := countLit b [-6, -10, -11, -12]
def count1424 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -10, -11, -12]
def count1431 (b : Nat → Bool) : Nat := countLit b [-18, -21]
def count1433 (b : Nat → Bool) : Nat := countLit b [-15, -18, -21]
def count1436 (b : Nat → Bool) : Nat := countLit b [-22, -23]
def count1438 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count1440 (b : Nat → Bool) : Nat := countLit b [-22, -23, -25, -27]
def count1444 (b : Nat → Bool) : Nat := countLit b [-15, -18, -21, -22, -23, -25, -27]
def count1451 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27]
def count1465 (b : Nat → Bool) : Nat := countLit b [-31, -35]
def count1467 (b : Nat → Bool) : Nat := countLit b [-30, -31, -35]
def count1470 (b : Nat → Bool) : Nat := countLit b [-37, -38]
def count1472 (b : Nat → Bool) : Nat := countLit b [-39, -43]
def count1474 (b : Nat → Bool) : Nat := countLit b [-37, -38, -39, -43]
def count1478 (b : Nat → Bool) : Nat := countLit b [-30, -31, -35, -37, -38, -39, -43]
def count1485 (b : Nat → Bool) : Nat := countLit b [-45, -49]
def count1487 (b : Nat → Bool) : Nat := countLit b [-50, -53]
def count1489 (b : Nat → Bool) : Nat := countLit b [-45, -49, -50, -53]
def count1493 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count1495 (b : Nat → Bool) : Nat := countLit b [-58, -60]
def count1497 (b : Nat → Bool) : Nat := countLit b [-55, -57, -58, -60]
def count1501 (b : Nat → Bool) : Nat := countLit b [-45, -49, -50, -53, -55, -57, -58, -60]
def count1509 (b : Nat → Bool) : Nat := countLit b [-30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]
def count1524 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60]
def count1542 (b : Nat → Bool) : Nat := countLit b [-63, -66]
def count1544 (b : Nat → Bool) : Nat := countLit b [-62, -63, -66]
def count1547 (b : Nat → Bool) : Nat := countLit b [-69, -71]
def count1549 (b : Nat → Bool) : Nat := countLit b [-72, -74]
def count1551 (b : Nat → Bool) : Nat := countLit b [-69, -71, -72, -74]
def count1555 (b : Nat → Bool) : Nat := countLit b [-62, -63, -66, -69, -71, -72, -74]
def count1562 (b : Nat → Bool) : Nat := countLit b [-79, -80]
def count1564 (b : Nat → Bool) : Nat := countLit b [-75, -79, -80]
def count1567 (b : Nat → Bool) : Nat := countLit b [-81, -82]
def count1569 (b : Nat → Bool) : Nat := countLit b [-86, -89]
def count1571 (b : Nat → Bool) : Nat := countLit b [-81, -82, -86, -89]
def count1575 (b : Nat → Bool) : Nat := countLit b [-75, -79, -80, -81, -82, -86, -89]
def count1582 (b : Nat → Bool) : Nat := countLit b [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89]
def count1596 (b : Nat → Bool) : Nat := countLit b [-92, -93]
def count1598 (b : Nat → Bool) : Nat := countLit b [-90, -92, -93]
def count1601 (b : Nat → Bool) : Nat := countLit b [-95, -98]
def count1603 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1605 (b : Nat → Bool) : Nat := countLit b [-95, -98, -99, -100]
def count1609 (b : Nat → Bool) : Nat := countLit b [-90, -92, -93, -95, -98, -99, -100]
def count1616 (b : Nat → Bool) : Nat := countLit b [-101, -105]
def count1618 (b : Nat → Bool) : Nat := countLit b [-107, -108]
def count1620 (b : Nat → Bool) : Nat := countLit b [-101, -105, -107, -108]
def count1624 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1626 (b : Nat → Bool) : Nat := countLit b [-114, -115]
def count1628 (b : Nat → Bool) : Nat := countLit b [-112, -113, -114, -115]
def count1632 (b : Nat → Bool) : Nat := countLit b [-101, -105, -107, -108, -112, -113, -114, -115]
def count1640 (b : Nat → Bool) : Nat := countLit b [-90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]
def count1655 (b : Nat → Bool) : Nat := countLit b [-62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]
def count1673 (b : Nat → Bool) : Nat := countLit b [-2, -4, -5, -6, -10, -11, -12, -15, -18, -21, -22, -23, -25, -27, -30, -31, -35, -37, -38, -39, -43, -45, -49, -50, -53, -55, -57, -58, -60, -62, -63, -66, -69, -71, -72, -74, -75, -79, -80, -81, -82, -86, -89, -90, -92, -93, -95, -98, -99, -100, -101, -105, -107, -108, -112, -113, -114, -115]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 845 then (if i < 422 then (if i < 211 then (if i < 105 then (if i < 52 then (if i < 26 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 19 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 17 then b 16 else (if i < 18 then b 17 else b 18))) else (if i < 22 then (if i < 20 then b 19 else (if i < 21 then b 20 else b 21)) else (if i < 24 then (if i < 23 then b 22 else b 23) else (if i < 25 then b 24 else b 25))))) else (if i < 39 then (if i < 32 then (if i < 29 then (if i < 27 then b 26 else (if i < 28 then b 27 else b 28)) else (if i < 30 then b 29 else (if i < 31 then b 30 else b 31))) else (if i < 35 then (if i < 33 then b 32 else (if i < 34 then b 33 else b 34)) else (if i < 37 then (if i < 36 then b 35 else b 36) else (if i < 38 then b 37 else b 38)))) else (if i < 45 then (if i < 42 then (if i < 40 then b 39 else (if i < 41 then b 40 else b 41)) else (if i < 43 then b 42 else (if i < 44 then b 43 else b 44))) else (if i < 48 then (if i < 46 then b 45 else (if i < 47 then b 46 else b 47)) else (if i < 50 then (if i < 49 then b 48 else b 49) else (if i < 51 then b 50 else b 51)))))) else (if i < 78 then (if i < 65 then (if i < 58 then (if i < 55 then (if i < 53 then b 52 else (if i < 54 then b 53 else b 54)) else (if i < 56 then b 55 else (if i < 57 then b 56 else b 57))) else (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else b 64)))) else (if i < 71 then (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 69 then b 68 else (if i < 70 then b 69 else b 70))) else (if i < 74 then (if i < 72 then b 71 else (if i < 73 then b 72 else b 73)) else (if i < 76 then (if i < 75 then b 74 else b 75) else (if i < 77 then b 76 else b 77))))) else (if i < 91 then (if i < 84 then (if i < 81 then (if i < 79 then b 78 else (if i < 80 then b 79 else b 80)) else (if i < 82 then b 81 else (if i < 83 then b 82 else b 83))) else (if i < 87 then (if i < 85 then b 84 else (if i < 86 then b 85 else b 86)) else (if i < 89 then (if i < 88 then b 87 else b 88) else (if i < 90 then b 89 else b 90)))) else (if i < 98 then (if i < 94 then (if i < 92 then b 91 else (if i < 93 then b 92 else b 93)) else (if i < 96 then (if i < 95 then b 94 else b 95) else (if i < 97 then b 96 else b 97))) else (if i < 101 then (if i < 99 then b 98 else (if i < 100 then b 99 else b 100)) else (if i < 103 then (if i < 102 then b 101 else b 102) else (if i < 104 then b 103 else b 104))))))) else (if i < 158 then (if i < 131 then (if i < 118 then (if i < 111 then (if i < 108 then (if i < 106 then b 105 else (if i < 107 then b 106 else b 107)) else (if i < 109 then b 108 else (if i < 110 then b 109 else b 110))) else (if i < 114 then (if i < 112 then b 111 else (if i < 113 then b 112 else b 113)) else (if i < 116 then (if i < 115 then b 114 else b 115) else (if i < 117 then b 116 else b 117)))) else (if i < 124 then (if i < 121 then (if i < 119 then b 118 else (if i < 120 then b 119 else b 120)) else (if i < 122 then b 121 else (if i < 123 then b 122 else b 123))) else (if i < 127 then (if i < 125 then b 124 else (if i < 126 then b 125 else b 126)) else (if i < 129 then (if i < 128 then b 127 else b 128) else (if i < 130 then b 129 else b 130))))) else (if i < 144 then (if i < 137 then (if i < 134 then (if i < 132 then b 131 else (if i < 133 then b 132 else b 133)) else (if i < 135 then b 134 else (if i < 136 then b 135 else b 136))) else (if i < 140 then (if i < 138 then b 137 else (if i < 139 then b 138 else b 139)) else (if i < 142 then (if i < 141 then b 140 else b 141) else (if i < 143 then b 142 else b 143)))) else (if i < 151 then (if i < 147 then (if i < 145 then b 144 else (if i < 146 then b 145 else b 146)) else (if i < 149 then (if i < 148 then b 147 else b 148) else (if i < 150 then b 149 else b 150))) else (if i < 154 then (if i < 152 then b 151 else (if i < 153 then b 152 else b 153)) else (if i < 156 then (if i < 155 then b 154 else b 155) else (if i < 157 then b 156 else b 157)))))) else (if i < 184 then (if i < 171 then (if i < 164 then (if i < 161 then (if i < 159 then b 158 else (if i < 160 then b 159 else b 160)) else (if i < 162 then b 161 else (if i < 163 then b 162 else b 163))) else (if i < 167 then (if i < 165 then b 164 else (if i < 166 then b 165 else b 166)) else (if i < 169 then (if i < 168 then b 167 else b 168) else (if i < 170 then b 169 else b 170)))) else (if i < 177 then (if i < 174 then (if i < 172 then b 171 else (if i < 173 then b 172 else b 173)) else (if i < 175 then b 174 else (if i < 176 then b 175 else b 176))) else (if i < 180 then (if i < 178 then b 177 else (if i < 179 then b 178 else b 179)) else (if i < 182 then (if i < 181 then b 180 else b 181) else (if i < 183 then b 182 else b 183))))) else (if i < 197 then (if i < 190 then (if i < 187 then (if i < 185 then b 184 else (if i < 186 then b 185 else b 186)) else (if i < 188 then b 187 else (if i < 189 then b 188 else b 189))) else (if i < 193 then (if i < 191 then b 190 else (if i < 192 then b 191 else b 192)) else (if i < 195 then (if i < 194 then b 193 else b 194) else (if i < 196 then b 195 else b 196)))) else (if i < 204 then (if i < 200 then (if i < 198 then b 197 else (if i < 199 then b 198 else b 199)) else (if i < 202 then (if i < 201 then b 200 else b 201) else (if i < 203 then b 202 else b 203))) else (if i < 207 then (if i < 205 then b 204 else (if i < 206 then b 205 else b 206)) else (if i < 209 then (if i < 208 then b 207 else b 208) else (if i < 210 then b 209 else b 210)))))))) else (if i < 316 then (if i < 263 then (if i < 237 then (if i < 224 then (if i < 217 then (if i < 214 then (if i < 212 then b 211 else (if i < 213 then b 212 else b 213)) else (if i < 215 then b 214 else (if i < 216 then b 215 else b 216))) else (if i < 220 then (if i < 218 then b 217 else (if i < 219 then b 218 else b 219)) else (if i < 222 then (if i < 221 then b 220 else b 221) else (if i < 223 then b 222 else b 223)))) else (if i < 230 then (if i < 227 then (if i < 225 then b 224 else (if i < 226 then b 225 else b 226)) else (if i < 228 then b 227 else (if i < 229 then b 228 else b 229))) else (if i < 233 then (if i < 231 then b 230 else (if i < 232 then b 231 else b 232)) else (if i < 235 then (if i < 234 then b 233 else b 234) else (if i < 236 then decide (1 ≤ count235 b) else decide (2 ≤ count235 b)))))) else (if i < 250 then (if i < 243 then (if i < 240 then (if i < 238 then decide (1 ≤ count237 b) else (if i < 239 then decide (2 ≤ count237 b) else decide (1 ≤ count239 b))) else (if i < 241 then decide (2 ≤ count239 b) else (if i < 242 then decide (1 ≤ count241 b) else decide (2 ≤ count241 b)))) else (if i < 246 then (if i < 244 then decide (1 ≤ count243 b) else (if i < 245 then decide (2 ≤ count243 b) else decide (1 ≤ count245 b))) else (if i < 248 then (if i < 247 then decide (2 ≤ count245 b) else decide (1 ≤ count247 b)) else (if i < 249 then decide (2 ≤ count247 b) else decide (1 ≤ count249 b))))) else (if i < 256 then (if i < 253 then (if i < 251 then decide (2 ≤ count249 b) else (if i < 252 then decide (1 ≤ count251 b) else decide (2 ≤ count251 b))) else (if i < 254 then decide (1 ≤ count253 b) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b)))) else (if i < 259 then (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))) else (if i < 261 then (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)) else (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b))))))) else (if i < 289 then (if i < 276 then (if i < 269 then (if i < 266 then (if i < 264 then decide (1 ≤ count263 b) else (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b))) else (if i < 267 then decide (2 ≤ count265 b) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b)))) else (if i < 272 then (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))) else (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))))) else (if i < 282 then (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 280 then decide (1 ≤ count279 b) else (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)))) else (if i < 285 then (if i < 283 then decide (2 ≤ count281 b) else (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b))) else (if i < 287 then (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b)) else (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)))))) else (if i < 302 then (if i < 295 then (if i < 292 then (if i < 290 then decide (1 ≤ count289 b) else (if i < 291 then decide (2 ≤ count289 b) else decide (1 ≤ count291 b))) else (if i < 293 then decide (2 ≤ count291 b) else (if i < 294 then decide (1 ≤ count293 b) else decide (2 ≤ count293 b)))) else (if i < 298 then (if i < 296 then decide (1 ≤ count295 b) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b))) else (if i < 300 then (if i < 299 then decide (2 ≤ count297 b) else decide (1 ≤ count299 b)) else (if i < 301 then decide (2 ≤ count299 b) else decide (1 ≤ count301 b))))) else (if i < 309 then (if i < 305 then (if i < 303 then decide (2 ≤ count301 b) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))) else (if i < 307 then (if i < 306 then decide (1 ≤ count305 b) else decide (2 ≤ count305 b)) else (if i < 308 then decide (1 ≤ count307 b) else decide (2 ≤ count307 b)))) else (if i < 312 then (if i < 310 then decide (1 ≤ count309 b) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b))) else (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b)))))))) else (if i < 369 then (if i < 342 then (if i < 329 then (if i < 322 then (if i < 319 then (if i < 317 then decide (2 ≤ count315 b) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))) else (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b)))) else (if i < 325 then (if i < 323 then decide (2 ≤ count321 b) else (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b))) else (if i < 327 then (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))))) else (if i < 335 then (if i < 332 then (if i < 330 then decide (1 ≤ count329 b) else (if i < 331 then decide (2 ≤ count329 b) else decide (1 ≤ count331 b))) else (if i < 333 then decide (2 ≤ count331 b) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b)))) else (if i < 338 then (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b))) else (if i < 340 then (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)))))) else (if i < 355 then (if i < 348 then (if i < 345 then (if i < 343 then decide (2 ≤ count341 b) else (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b))) else (if i < 346 then decide (1 ≤ count345 b) else (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)))) else (if i < 351 then (if i < 349 then decide (2 ≤ count347 b) else (if i < 350 then decide (1 ≤ count349 b) else decide (2 ≤ count349 b))) else (if i < 353 then (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b)) else (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b))))) else (if i < 362 then (if i < 358 then (if i < 356 then decide (1 ≤ count355 b) else (if i < 357 then decide (2 ≤ count355 b) else decide (1 ≤ count357 b))) else (if i < 360 then (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b)) else (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)))) else (if i < 365 then (if i < 363 then decide (2 ≤ count361 b) else (if i < 364 then decide (1 ≤ count363 b) else decide (2 ≤ count363 b))) else (if i < 367 then (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b)) else (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b))))))) else (if i < 395 then (if i < 382 then (if i < 375 then (if i < 372 then (if i < 370 then decide (1 ≤ count369 b) else (if i < 371 then decide (2 ≤ count369 b) else decide (1 ≤ count371 b))) else (if i < 373 then decide (2 ≤ count371 b) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b)))) else (if i < 378 then (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))) else (if i < 380 then (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))))) else (if i < 388 then (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 386 then decide (1 ≤ count385 b) else (if i < 387 then decide (2 ≤ count385 b) else decide (1 ≤ count387 b)))) else (if i < 391 then (if i < 389 then decide (2 ≤ count387 b) else (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b))) else (if i < 393 then (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b)) else (if i < 394 then decide (1 ≤ count393 b) else decide (2 ≤ count393 b)))))) else (if i < 408 then (if i < 401 then (if i < 398 then (if i < 396 then decide (1 ≤ count395 b) else (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b))) else (if i < 399 then decide (2 ≤ count397 b) else (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)))) else (if i < 404 then (if i < 402 then decide (1 ≤ count401 b) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 406 then (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b)) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))))) else (if i < 415 then (if i < 411 then (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))) else (if i < 413 then (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 420 then (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b)))))))))) else (if i < 633 then (if i < 527 then (if i < 474 then (if i < 448 then (if i < 435 then (if i < 428 then (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 426 then decide (1 ≤ count425 b) else (if i < 427 then decide (2 ≤ count425 b) else decide (1 ≤ count427 b)))) else (if i < 431 then (if i < 429 then decide (2 ≤ count427 b) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))) else (if i < 433 then (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b)) else (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b))))) else (if i < 441 then (if i < 438 then (if i < 436 then decide (1 ≤ count435 b) else (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b))) else (if i < 439 then decide (2 ≤ count437 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b)))) else (if i < 444 then (if i < 442 then decide (1 ≤ count441 b) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b))) else (if i < 446 then (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)) else (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b)))))) else (if i < 461 then (if i < 454 then (if i < 451 then (if i < 449 then decide (2 ≤ count447 b) else (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b))) else (if i < 452 then decide (1 ≤ count451 b) else (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b)))) else (if i < 457 then (if i < 455 then decide (2 ≤ count453 b) else (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b))) else (if i < 459 then (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b))))) else (if i < 467 then (if i < 464 then (if i < 462 then decide (1 ≤ count461 b) else (if i < 463 then decide (2 ≤ count461 b) else decide (1 ≤ count463 b))) else (if i < 465 then decide (2 ≤ count463 b) else (if i < 466 then decide (1 ≤ count465 b) else decide (2 ≤ count465 b)))) else (if i < 470 then (if i < 468 then decide (1 ≤ count467 b) else (if i < 469 then decide (2 ≤ count467 b) else decide (3 ≤ count467 b))) else (if i < 472 then (if i < 471 then decide (1 ≤ count470 b) else decide (2 ≤ count470 b)) else (if i < 473 then decide (1 ≤ count472 b) else decide (2 ≤ count472 b))))))) else (if i < 500 then (if i < 487 then (if i < 480 then (if i < 477 then (if i < 475 then decide (1 ≤ count474 b) else (if i < 476 then decide (2 ≤ count474 b) else decide (3 ≤ count474 b))) else (if i < 478 then decide (4 ≤ count474 b) else (if i < 479 then decide (1 ≤ count478 b) else decide (2 ≤ count478 b)))) else (if i < 483 then (if i < 481 then decide (3 ≤ count478 b) else (if i < 482 then decide (4 ≤ count478 b) else decide (5 ≤ count478 b))) else (if i < 485 then (if i < 484 then decide (6 ≤ count478 b) else decide (7 ≤ count478 b)) else (if i < 486 then decide (1 ≤ count485 b) else decide (2 ≤ count485 b))))) else (if i < 493 then (if i < 490 then (if i < 488 then decide (1 ≤ count487 b) else (if i < 489 then decide (2 ≤ count487 b) else decide (3 ≤ count487 b))) else (if i < 491 then decide (1 ≤ count490 b) else (if i < 492 then decide (2 ≤ count490 b) else decide (1 ≤ count492 b)))) else (if i < 496 then (if i < 494 then decide (2 ≤ count492 b) else (if i < 495 then decide (1 ≤ count494 b) else decide (2 ≤ count494 b))) else (if i < 498 then (if i < 497 then decide (3 ≤ count494 b) else decide (4 ≤ count494 b)) else (if i < 499 then decide (1 ≤ count498 b) else decide (2 ≤ count498 b)))))) else (if i < 513 then (if i < 506 then (if i < 503 then (if i < 501 then decide (3 ≤ count498 b) else (if i < 502 then decide (4 ≤ count498 b) else decide (5 ≤ count498 b))) else (if i < 504 then decide (6 ≤ count498 b) else (if i < 505 then decide (7 ≤ count498 b) else decide (1 ≤ count505 b)))) else (if i < 509 then (if i < 507 then decide (2 ≤ count505 b) else (if i < 508 then decide (3 ≤ count505 b) else decide (4 ≤ count505 b))) else (if i < 511 then (if i < 510 then decide (5 ≤ count505 b) else decide (6 ≤ count505 b)) else (if i < 512 then decide (7 ≤ count505 b) else decide (8 ≤ count505 b))))) else (if i < 520 then (if i < 516 then (if i < 514 then decide (9 ≤ count505 b) else (if i < 515 then decide (10 ≤ count505 b) else decide (11 ≤ count505 b))) else (if i < 518 then (if i < 517 then decide (12 ≤ count505 b) else decide (13 ≤ count505 b)) else (if i < 519 then decide (14 ≤ count505 b) else decide (1 ≤ count519 b)))) else (if i < 523 then (if i < 521 then decide (2 ≤ count519 b) else (if i < 522 then decide (1 ≤ count521 b) else decide (2 ≤ count521 b))) else (if i < 525 then (if i < 524 then decide (3 ≤ count521 b) else decide (1 ≤ count524 b)) else (if i < 526 then decide (2 ≤ count524 b) else decide (1 ≤ count526 b)))))))) else (if i < 580 then (if i < 553 then (if i < 540 then (if i < 533 then (if i < 530 then (if i < 528 then decide (2 ≤ count526 b) else (if i < 529 then decide (1 ≤ count528 b) else decide (2 ≤ count528 b))) else (if i < 531 then decide (3 ≤ count528 b) else (if i < 532 then decide (4 ≤ count528 b) else decide (1 ≤ count532 b)))) else (if i < 536 then (if i < 534 then decide (2 ≤ count532 b) else (if i < 535 then decide (3 ≤ count532 b) else decide (4 ≤ count532 b))) else (if i < 538 then (if i < 537 then decide (5 ≤ count532 b) else decide (6 ≤ count532 b)) else (if i < 539 then decide (7 ≤ count532 b) else decide (1 ≤ count539 b))))) else (if i < 546 then (if i < 543 then (if i < 541 then decide (2 ≤ count539 b) else (if i < 542 then decide (1 ≤ count541 b) else decide (2 ≤ count541 b))) else (if i < 544 then decide (1 ≤ count543 b) else (if i < 545 then decide (2 ≤ count543 b) else decide (3 ≤ count543 b)))) else (if i < 549 then (if i < 547 then decide (4 ≤ count543 b) else (if i < 548 then decide (1 ≤ count547 b) else decide (2 ≤ count547 b))) else (if i < 551 then (if i < 550 then decide (1 ≤ count549 b) else decide (2 ≤ count549 b)) else (if i < 552 then decide (1 ≤ count551 b) else decide (2 ≤ count551 b)))))) else (if i < 566 then (if i < 559 then (if i < 556 then (if i < 554 then decide (3 ≤ count551 b) else (if i < 555 then decide (4 ≤ count551 b) else decide (1 ≤ count555 b))) else (if i < 557 then decide (2 ≤ count555 b) else (if i < 558 then decide (3 ≤ count555 b) else decide (4 ≤ count555 b)))) else (if i < 562 then (if i < 560 then decide (5 ≤ count555 b) else (if i < 561 then decide (6 ≤ count555 b) else decide (7 ≤ count555 b))) else (if i < 564 then (if i < 563 then decide (8 ≤ count555 b) else decide (1 ≤ count563 b)) else (if i < 565 then decide (2 ≤ count563 b) else decide (3 ≤ count563 b))))) else (if i < 573 then (if i < 569 then (if i < 567 then decide (4 ≤ count563 b) else (if i < 568 then decide (5 ≤ count563 b) else decide (6 ≤ count563 b))) else (if i < 571 then (if i < 570 then decide (7 ≤ count563 b) else decide (8 ≤ count563 b)) else (if i < 572 then decide (9 ≤ count563 b) else decide (10 ≤ count563 b)))) else (if i < 576 then (if i < 574 then decide (11 ≤ count563 b) else (if i < 575 then decide (12 ≤ count563 b) else decide (13 ≤ count563 b))) else (if i < 578 then (if i < 577 then decide (14 ≤ count563 b) else decide (15 ≤ count563 b)) else (if i < 579 then decide (1 ≤ count578 b) else decide (2 ≤ count578 b))))))) else (if i < 606 then (if i < 593 then (if i < 586 then (if i < 583 then (if i < 581 then decide (3 ≤ count578 b) else (if i < 582 then decide (4 ≤ count578 b) else decide (5 ≤ count578 b))) else (if i < 584 then decide (6 ≤ count578 b) else (if i < 585 then decide (7 ≤ count578 b) else decide (8 ≤ count578 b)))) else (if i < 589 then (if i < 587 then decide (9 ≤ count578 b) else (if i < 588 then decide (10 ≤ count578 b) else decide (11 ≤ count578 b))) else (if i < 591 then (if i < 590 then decide (12 ≤ count578 b) else decide (13 ≤ count578 b)) else (if i < 592 then decide (14 ≤ count578 b) else decide (15 ≤ count578 b))))) else (if i < 599 then (if i < 596 then (if i < 594 then decide (16 ≤ count578 b) else (if i < 595 then decide (17 ≤ count578 b) else decide (18 ≤ count578 b))) else (if i < 597 then decide (19 ≤ count578 b) else (if i < 598 then decide (20 ≤ count578 b) else decide (21 ≤ count578 b)))) else (if i < 602 then (if i < 600 then decide (22 ≤ count578 b) else (if i < 601 then decide (23 ≤ count578 b) else decide (24 ≤ count578 b))) else (if i < 604 then (if i < 603 then decide (25 ≤ count578 b) else decide (26 ≤ count578 b)) else (if i < 605 then decide (27 ≤ count578 b) else decide (28 ≤ count578 b)))))) else (if i < 619 then (if i < 612 then (if i < 609 then (if i < 607 then decide (29 ≤ count578 b) else (if i < 608 then decide (1 ≤ count607 b) else decide (2 ≤ count607 b))) else (if i < 610 then decide (1 ≤ count609 b) else (if i < 611 then decide (2 ≤ count609 b) else decide (3 ≤ count609 b)))) else (if i < 615 then (if i < 613 then decide (1 ≤ count612 b) else (if i < 614 then decide (2 ≤ count612 b) else decide (1 ≤ count614 b))) else (if i < 617 then (if i < 616 then decide (2 ≤ count614 b) else decide (1 ≤ count616 b)) else (if i < 618 then decide (2 ≤ count616 b) else decide (3 ≤ count616 b))))) else (if i < 626 then (if i < 622 then (if i < 620 then decide (4 ≤ count616 b) else (if i < 621 then decide (1 ≤ count620 b) else decide (2 ≤ count620 b))) else (if i < 624 then (if i < 623 then decide (3 ≤ count620 b) else decide (4 ≤ count620 b)) else (if i < 625 then decide (5 ≤ count620 b) else decide (6 ≤ count620 b)))) else (if i < 629 then (if i < 627 then decide (7 ≤ count620 b) else (if i < 628 then decide (1 ≤ count627 b) else decide (2 ≤ count627 b))) else (if i < 631 then (if i < 630 then decide (1 ≤ count629 b) else decide (2 ≤ count629 b)) else (if i < 632 then decide (1 ≤ count631 b) else decide (2 ≤ count631 b))))))))) else (if i < 739 then (if i < 686 then (if i < 659 then (if i < 646 then (if i < 639 then (if i < 636 then (if i < 634 then decide (3 ≤ count631 b) else (if i < 635 then decide (4 ≤ count631 b) else decide (1 ≤ count635 b))) else (if i < 637 then decide (2 ≤ count635 b) else (if i < 638 then decide (1 ≤ count637 b) else decide (2 ≤ count637 b)))) else (if i < 642 then (if i < 640 then decide (1 ≤ count639 b) else (if i < 641 then decide (2 ≤ count639 b) else decide (3 ≤ count639 b))) else (if i < 644 then (if i < 643 then decide (4 ≤ count639 b) else decide (1 ≤ count643 b)) else (if i < 645 then decide (2 ≤ count643 b) else decide (3 ≤ count643 b))))) else (if i < 652 then (if i < 649 then (if i < 647 then decide (4 ≤ count643 b) else (if i < 648 then decide (5 ≤ count643 b) else decide (6 ≤ count643 b))) else (if i < 650 then decide (7 ≤ count643 b) else (if i < 651 then decide (8 ≤ count643 b) else decide (1 ≤ count651 b)))) else (if i < 655 then (if i < 653 then decide (2 ≤ count651 b) else (if i < 654 then decide (3 ≤ count651 b) else decide (4 ≤ count651 b))) else (if i < 657 then (if i < 656 then decide (5 ≤ count651 b) else decide (6 ≤ count651 b)) else (if i < 658 then decide (7 ≤ count651 b) else decide (8 ≤ count651 b)))))) else (if i < 672 then (if i < 665 then (if i < 662 then (if i < 660 then decide (9 ≤ count651 b) else (if i < 661 then decide (10 ≤ count651 b) else decide (11 ≤ count651 b))) else (if i < 663 then decide (12 ≤ count651 b) else (if i < 664 then decide (13 ≤ count651 b) else decide (14 ≤ count651 b)))) else (if i < 668 then (if i < 666 then decide (15 ≤ count651 b) else (if i < 667 then decide (1 ≤ count666 b) else decide (2 ≤ count666 b))) else (if i < 670 then (if i < 669 then decide (1 ≤ count668 b) else decide (2 ≤ count668 b)) else (if i < 671 then decide (3 ≤ count668 b) else decide (1 ≤ count671 b))))) else (if i < 679 then (if i < 675 then (if i < 673 then decide (2 ≤ count671 b) else (if i < 674 then decide (1 ≤ count673 b) else decide (2 ≤ count673 b))) else (if i < 677 then (if i < 676 then decide (1 ≤ count675 b) else decide (2 ≤ count675 b)) else (if i < 678 then decide (3 ≤ count675 b) else decide (4 ≤ count675 b)))) else (if i < 682 then (if i < 680 then decide (1 ≤ count679 b) else (if i < 681 then decide (2 ≤ count679 b) else decide (3 ≤ count679 b))) else (if i < 684 then (if i < 683 then decide (4 ≤ count679 b) else decide (5 ≤ count679 b)) else (if i < 685 then decide (6 ≤ count679 b) else decide (7 ≤ count679 b))))))) else (if i < 712 then (if i < 699 then (if i < 692 then (if i < 689 then (if i < 687 then decide (1 ≤ count686 b) else (if i < 688 then decide (2 ≤ count686 b) else decide (1 ≤ count688 b))) else (if i < 690 then decide (2 ≤ count688 b) else (if i < 691 then decide (1 ≤ count690 b) else decide (2 ≤ count690 b)))) else (if i < 695 then (if i < 693 then decide (3 ≤ count690 b) else (if i < 694 then decide (4 ≤ count690 b) else decide (1 ≤ count694 b))) else (if i < 697 then (if i < 696 then decide (2 ≤ count694 b) else decide (1 ≤ count696 b)) else (if i < 698 then decide (2 ≤ count696 b) else decide (1 ≤ count698 b))))) else (if i < 705 then (if i < 702 then (if i < 700 then decide (2 ≤ count698 b) else (if i < 701 then decide (3 ≤ count698 b) else decide (4 ≤ count698 b))) else (if i < 703 then decide (1 ≤ count702 b) else (if i < 704 then decide (2 ≤ count702 b) else decide (3 ≤ count702 b)))) else (if i < 708 then (if i < 706 then decide (4 ≤ count702 b) else (if i < 707 then decide (5 ≤ count702 b) else decide (6 ≤ count702 b))) else (if i < 710 then (if i < 709 then decide (7 ≤ count702 b) else decide (8 ≤ count702 b)) else (if i < 711 then decide (1 ≤ count710 b) else decide (2 ≤ count710 b)))))) else (if i < 725 then (if i < 718 then (if i < 715 then (if i < 713 then decide (3 ≤ count710 b) else (if i < 714 then decide (4 ≤ count710 b) else decide (5 ≤ count710 b))) else (if i < 716 then decide (6 ≤ count710 b) else (if i < 717 then decide (7 ≤ count710 b) else decide (8 ≤ count710 b)))) else (if i < 721 then (if i < 719 then decide (9 ≤ count710 b) else (if i < 720 then decide (10 ≤ count710 b) else decide (11 ≤ count710 b))) else (if i < 723 then (if i < 722 then decide (12 ≤ count710 b) else decide (13 ≤ count710 b)) else (if i < 724 then decide (14 ≤ count710 b) else decide (15 ≤ count710 b))))) else (if i < 732 then (if i < 728 then (if i < 726 then decide (1 ≤ count725 b) else (if i < 727 then decide (2 ≤ count725 b) else decide (3 ≤ count725 b))) else (if i < 730 then (if i < 729 then decide (4 ≤ count725 b) else decide (5 ≤ count725 b)) else (if i < 731 then decide (6 ≤ count725 b) else decide (7 ≤ count725 b)))) else (if i < 735 then (if i < 733 then decide (8 ≤ count725 b) else (if i < 734 then decide (9 ≤ count725 b) else decide (10 ≤ count725 b))) else (if i < 737 then (if i < 736 then decide (11 ≤ count725 b) else decide (12 ≤ count725 b)) else (if i < 738 then decide (13 ≤ count725 b) else decide (14 ≤ count725 b)))))))) else (if i < 792 then (if i < 765 then (if i < 752 then (if i < 745 then (if i < 742 then (if i < 740 then decide (15 ≤ count725 b) else (if i < 741 then decide (16 ≤ count725 b) else decide (17 ≤ count725 b))) else (if i < 743 then decide (18 ≤ count725 b) else (if i < 744 then decide (19 ≤ count725 b) else decide (20 ≤ count725 b)))) else (if i < 748 then (if i < 746 then decide (21 ≤ count725 b) else (if i < 747 then decide (22 ≤ count725 b) else decide (23 ≤ count725 b))) else (if i < 750 then (if i < 749 then decide (24 ≤ count725 b) else decide (25 ≤ count725 b)) else (if i < 751 then decide (26 ≤ count725 b) else decide (27 ≤ count725 b))))) else (if i < 758 then (if i < 755 then (if i < 753 then decide (28 ≤ count725 b) else (if i < 754 then decide (29 ≤ count725 b) else decide (30 ≤ count725 b))) else (if i < 756 then decide (1 ≤ count755 b) else (if i < 757 then decide (2 ≤ count755 b) else decide (3 ≤ count755 b)))) else (if i < 761 then (if i < 759 then decide (4 ≤ count755 b) else (if i < 760 then decide (5 ≤ count755 b) else decide (6 ≤ count755 b))) else (if i < 763 then (if i < 762 then decide (7 ≤ count755 b) else decide (8 ≤ count755 b)) else (if i < 764 then decide (9 ≤ count755 b) else decide (10 ≤ count755 b)))))) else (if i < 778 then (if i < 771 then (if i < 768 then (if i < 766 then decide (11 ≤ count755 b) else (if i < 767 then decide (12 ≤ count755 b) else decide (13 ≤ count755 b))) else (if i < 769 then decide (14 ≤ count755 b) else (if i < 770 then decide (15 ≤ count755 b) else decide (16 ≤ count755 b)))) else (if i < 774 then (if i < 772 then decide (17 ≤ count755 b) else (if i < 773 then decide (18 ≤ count755 b) else decide (19 ≤ count755 b))) else (if i < 776 then (if i < 775 then decide (20 ≤ count755 b) else decide (21 ≤ count755 b)) else (if i < 777 then decide (22 ≤ count755 b) else decide (23 ≤ count755 b))))) else (if i < 785 then (if i < 781 then (if i < 779 then decide (24 ≤ count755 b) else (if i < 780 then decide (25 ≤ count755 b) else decide (26 ≤ count755 b))) else (if i < 783 then (if i < 782 then decide (27 ≤ count755 b) else decide (28 ≤ count755 b)) else (if i < 784 then decide (29 ≤ count755 b) else decide (30 ≤ count755 b)))) else (if i < 788 then (if i < 786 then decide (31 ≤ count755 b) else (if i < 787 then decide (32 ≤ count755 b) else decide (33 ≤ count755 b))) else (if i < 790 then (if i < 789 then decide (34 ≤ count755 b) else decide (35 ≤ count755 b)) else (if i < 791 then decide (36 ≤ count755 b) else decide (37 ≤ count755 b))))))) else (if i < 818 then (if i < 805 then (if i < 798 then (if i < 795 then (if i < 793 then decide (38 ≤ count755 b) else (if i < 794 then decide (39 ≤ count755 b) else decide (40 ≤ count755 b))) else (if i < 796 then decide (41 ≤ count755 b) else (if i < 797 then decide (42 ≤ count755 b) else decide (1 ≤ count797 b)))) else (if i < 801 then (if i < 799 then decide (2 ≤ count797 b) else (if i < 800 then decide (1 ≤ count799 b) else decide (2 ≤ count799 b))) else (if i < 803 then (if i < 802 then decide (3 ≤ count799 b) else decide (1 ≤ count802 b)) else (if i < 804 then decide (2 ≤ count802 b) else decide (1 ≤ count804 b))))) else (if i < 811 then (if i < 808 then (if i < 806 then decide (2 ≤ count804 b) else (if i < 807 then decide (1 ≤ count806 b) else decide (2 ≤ count806 b))) else (if i < 809 then decide (3 ≤ count806 b) else (if i < 810 then decide (4 ≤ count806 b) else decide (1 ≤ count810 b)))) else (if i < 814 then (if i < 812 then decide (2 ≤ count810 b) else (if i < 813 then decide (3 ≤ count810 b) else decide (4 ≤ count810 b))) else (if i < 816 then (if i < 815 then decide (5 ≤ count810 b) else decide (6 ≤ count810 b)) else (if i < 817 then decide (7 ≤ count810 b) else decide (1 ≤ count817 b)))))) else (if i < 831 then (if i < 824 then (if i < 821 then (if i < 819 then decide (2 ≤ count817 b) else (if i < 820 then decide (1 ≤ count819 b) else decide (2 ≤ count819 b))) else (if i < 822 then decide (3 ≤ count819 b) else (if i < 823 then decide (1 ≤ count822 b) else decide (2 ≤ count822 b)))) else (if i < 827 then (if i < 825 then decide (1 ≤ count824 b) else (if i < 826 then decide (2 ≤ count824 b) else decide (1 ≤ count826 b))) else (if i < 829 then (if i < 828 then decide (2 ≤ count826 b) else decide (3 ≤ count826 b)) else (if i < 830 then decide (4 ≤ count826 b) else decide (1 ≤ count830 b))))) else (if i < 838 then (if i < 834 then (if i < 832 then decide (2 ≤ count830 b) else (if i < 833 then decide (3 ≤ count830 b) else decide (4 ≤ count830 b))) else (if i < 836 then (if i < 835 then decide (5 ≤ count830 b) else decide (6 ≤ count830 b)) else (if i < 837 then decide (7 ≤ count830 b) else decide (1 ≤ count837 b)))) else (if i < 841 then (if i < 839 then decide (2 ≤ count837 b) else (if i < 840 then decide (3 ≤ count837 b) else decide (4 ≤ count837 b))) else (if i < 843 then (if i < 842 then decide (5 ≤ count837 b) else decide (6 ≤ count837 b)) else (if i < 844 then decide (7 ≤ count837 b) else decide (8 ≤ count837 b))))))))))) else (if i < 1268 then (if i < 1056 then (if i < 950 then (if i < 897 then (if i < 871 then (if i < 858 then (if i < 851 then (if i < 848 then (if i < 846 then decide (9 ≤ count837 b) else (if i < 847 then decide (10 ≤ count837 b) else decide (11 ≤ count837 b))) else (if i < 849 then decide (12 ≤ count837 b) else (if i < 850 then decide (13 ≤ count837 b) else decide (14 ≤ count837 b)))) else (if i < 854 then (if i < 852 then decide (1 ≤ count851 b) else (if i < 853 then decide (2 ≤ count851 b) else decide (1 ≤ count853 b))) else (if i < 856 then (if i < 855 then decide (2 ≤ count853 b) else decide (3 ≤ count853 b)) else (if i < 857 then decide (1 ≤ count856 b) else decide (2 ≤ count856 b))))) else (if i < 864 then (if i < 861 then (if i < 859 then decide (1 ≤ count858 b) else (if i < 860 then decide (2 ≤ count858 b) else decide (1 ≤ count860 b))) else (if i < 862 then decide (2 ≤ count860 b) else (if i < 863 then decide (3 ≤ count860 b) else decide (4 ≤ count860 b)))) else (if i < 867 then (if i < 865 then decide (1 ≤ count864 b) else (if i < 866 then decide (2 ≤ count864 b) else decide (3 ≤ count864 b))) else (if i < 869 then (if i < 868 then decide (4 ≤ count864 b) else decide (5 ≤ count864 b)) else (if i < 870 then decide (6 ≤ count864 b) else decide (7 ≤ count864 b)))))) else (if i < 884 then (if i < 877 then (if i < 874 then (if i < 872 then decide (1 ≤ count871 b) else (if i < 873 then decide (2 ≤ count871 b) else decide (1 ≤ count873 b))) else (if i < 875 then decide (2 ≤ count873 b) else (if i < 876 then decide (1 ≤ count875 b) else decide (2 ≤ count875 b)))) else (if i < 880 then (if i < 878 then decide (3 ≤ count875 b) else (if i < 879 then decide (4 ≤ count875 b) else decide (1 ≤ count879 b))) else (if i < 882 then (if i < 881 then decide (2 ≤ count879 b) else decide (1 ≤ count881 b)) else (if i < 883 then decide (2 ≤ count881 b) else decide (1 ≤ count883 b))))) else (if i < 890 then (if i < 887 then (if i < 885 then decide (2 ≤ count883 b) else (if i < 886 then decide (3 ≤ count883 b) else decide (4 ≤ count883 b))) else (if i < 888 then decide (1 ≤ count887 b) else (if i < 889 then decide (2 ≤ count887 b) else decide (3 ≤ count887 b)))) else (if i < 893 then (if i < 891 then decide (4 ≤ count887 b) else (if i < 892 then decide (5 ≤ count887 b) else decide (6 ≤ count887 b))) else (if i < 895 then (if i < 894 then decide (7 ≤ count887 b) else decide (8 ≤ count887 b)) else (if i < 896 then decide (1 ≤ count895 b) else decide (2 ≤ count895 b))))))) else (if i < 923 then (if i < 910 then (if i < 903 then (if i < 900 then (if i < 898 then decide (3 ≤ count895 b) else (if i < 899 then decide (4 ≤ count895 b) else decide (5 ≤ count895 b))) else (if i < 901 then decide (6 ≤ count895 b) else (if i < 902 then decide (7 ≤ count895 b) else decide (8 ≤ count895 b)))) else (if i < 906 then (if i < 904 then decide (9 ≤ count895 b) else (if i < 905 then decide (10 ≤ count895 b) else decide (11 ≤ count895 b))) else (if i < 908 then (if i < 907 then decide (12 ≤ count895 b) else decide (13 ≤ count895 b)) else (if i < 909 then decide (14 ≤ count895 b) else decide (15 ≤ count895 b))))) else (if i < 916 then (if i < 913 then (if i < 911 then decide (1 ≤ count910 b) else (if i < 912 then decide (2 ≤ count910 b) else decide (3 ≤ count910 b))) else (if i < 914 then decide (4 ≤ count910 b) else (if i < 915 then decide (5 ≤ count910 b) else decide (6 ≤ count910 b)))) else (if i < 919 then (if i < 917 then decide (7 ≤ count910 b) else (if i < 918 then decide (8 ≤ count910 b) else decide (9 ≤ count910 b))) else (if i < 921 then (if i < 920 then decide (10 ≤ count910 b) else decide (11 ≤ count910 b)) else (if i < 922 then decide (12 ≤ count910 b) else decide (13 ≤ count910 b)))))) else (if i < 936 then (if i < 929 then (if i < 926 then (if i < 924 then decide (14 ≤ count910 b) else (if i < 925 then decide (15 ≤ count910 b) else decide (16 ≤ count910 b))) else (if i < 927 then decide (17 ≤ count910 b) else (if i < 928 then decide (18 ≤ count910 b) else decide (19 ≤ count910 b)))) else (if i < 932 then (if i < 930 then decide (1 ≤ count929 b) else (if i < 931 then decide (2 ≤ count929 b) else decide (1 ≤ count931 b))) else (if i < 934 then (if i < 933 then decide (2 ≤ count931 b) else decide (3 ≤ count931 b)) else (if i < 935 then decide (1 ≤ count934 b) else decide (2 ≤ count934 b))))) else (if i < 943 then (if i < 939 then (if i < 937 then decide (1 ≤ count936 b) else (if i < 938 then decide (2 ≤ count936 b) else decide (1 ≤ count938 b))) else (if i < 941 then (if i < 940 then decide (2 ≤ count938 b) else decide (3 ≤ count938 b)) else (if i < 942 then decide (4 ≤ count938 b) else decide (1 ≤ count942 b)))) else (if i < 946 then (if i < 944 then decide (2 ≤ count942 b) else (if i < 945 then decide (3 ≤ count942 b) else decide (4 ≤ count942 b))) else (if i < 948 then (if i < 947 then decide (5 ≤ count942 b) else decide (6 ≤ count942 b)) else (if i < 949 then decide (7 ≤ count942 b) else decide (1 ≤ count949 b)))))))) else (if i < 1003 then (if i < 976 then (if i < 963 then (if i < 956 then (if i < 953 then (if i < 951 then decide (2 ≤ count949 b) else (if i < 952 then decide (1 ≤ count951 b) else decide (2 ≤ count951 b))) else (if i < 954 then decide (1 ≤ count953 b) else (if i < 955 then decide (2 ≤ count953 b) else decide (3 ≤ count953 b)))) else (if i < 959 then (if i < 957 then decide (4 ≤ count953 b) else (if i < 958 then decide (1 ≤ count957 b) else decide (2 ≤ count957 b))) else (if i < 961 then (if i < 960 then decide (1 ≤ count959 b) else decide (2 ≤ count959 b)) else (if i < 962 then decide (1 ≤ count961 b) else decide (2 ≤ count961 b))))) else (if i < 969 then (if i < 966 then (if i < 964 then decide (3 ≤ count961 b) else (if i < 965 then decide (4 ≤ count961 b) else decide (1 ≤ count965 b))) else (if i < 967 then decide (2 ≤ count965 b) else (if i < 968 then decide (3 ≤ count965 b) else decide (4 ≤ count965 b)))) else (if i < 972 then (if i < 970 then decide (5 ≤ count965 b) else (if i < 971 then decide (6 ≤ count965 b) else decide (7 ≤ count965 b))) else (if i < 974 then (if i < 973 then decide (8 ≤ count965 b) else decide (1 ≤ count973 b)) else (if i < 975 then decide (2 ≤ count973 b) else decide (3 ≤ count973 b)))))) else (if i < 989 then (if i < 982 then (if i < 979 then (if i < 977 then decide (4 ≤ count973 b) else (if i < 978 then decide (5 ≤ count973 b) else decide (6 ≤ count973 b))) else (if i < 980 then decide (7 ≤ count973 b) else (if i < 981 then decide (8 ≤ count973 b) else decide (9 ≤ count973 b)))) else (if i < 985 then (if i < 983 then decide (10 ≤ count973 b) else (if i < 984 then decide (11 ≤ count973 b) else decide (12 ≤ count973 b))) else (if i < 987 then (if i < 986 then decide (13 ≤ count973 b) else decide (14 ≤ count973 b)) else (if i < 988 then decide (15 ≤ count973 b) else decide (1 ≤ count988 b))))) else (if i < 996 then (if i < 992 then (if i < 990 then decide (2 ≤ count988 b) else (if i < 991 then decide (1 ≤ count990 b) else decide (2 ≤ count990 b))) else (if i < 994 then (if i < 993 then decide (3 ≤ count990 b) else decide (1 ≤ count993 b)) else (if i < 995 then decide (2 ≤ count993 b) else decide (1 ≤ count995 b)))) else (if i < 999 then (if i < 997 then decide (2 ≤ count995 b) else (if i < 998 then decide (1 ≤ count997 b) else decide (2 ≤ count997 b))) else (if i < 1001 then (if i < 1000 then decide (3 ≤ count997 b) else decide (4 ≤ count997 b)) else (if i < 1002 then decide (1 ≤ count1001 b) else decide (2 ≤ count1001 b))))))) else (if i < 1029 then (if i < 1016 then (if i < 1009 then (if i < 1006 then (if i < 1004 then decide (3 ≤ count1001 b) else (if i < 1005 then decide (4 ≤ count1001 b) else decide (5 ≤ count1001 b))) else (if i < 1007 then decide (6 ≤ count1001 b) else (if i < 1008 then decide (7 ≤ count1001 b) else decide (1 ≤ count1008 b)))) else (if i < 1012 then (if i < 1010 then decide (2 ≤ count1008 b) else (if i < 1011 then decide (1 ≤ count1010 b) else decide (2 ≤ count1010 b))) else (if i < 1014 then (if i < 1013 then decide (1 ≤ count1012 b) else decide (2 ≤ count1012 b)) else (if i < 1015 then decide (3 ≤ count1012 b) else decide (4 ≤ count1012 b))))) else (if i < 1022 then (if i < 1019 then (if i < 1017 then decide (1 ≤ count1016 b) else (if i < 1018 then decide (2 ≤ count1016 b) else decide (1 ≤ count1018 b))) else (if i < 1020 then decide (2 ≤ count1018 b) else (if i < 1021 then decide (1 ≤ count1020 b) else decide (2 ≤ count1020 b)))) else (if i < 1025 then (if i < 1023 then decide (3 ≤ count1020 b) else (if i < 1024 then decide (4 ≤ count1020 b) else decide (1 ≤ count1024 b))) else (if i < 1027 then (if i < 1026 then decide (2 ≤ count1024 b) else decide (3 ≤ count1024 b)) else (if i < 1028 then decide (4 ≤ count1024 b) else decide (5 ≤ count1024 b)))))) else (if i < 1042 then (if i < 1035 then (if i < 1032 then (if i < 1030 then decide (6 ≤ count1024 b) else (if i < 1031 then decide (7 ≤ count1024 b) else decide (8 ≤ count1024 b))) else (if i < 1033 then decide (1 ≤ count1032 b) else (if i < 1034 then decide (2 ≤ count1032 b) else decide (3 ≤ count1032 b)))) else (if i < 1038 then (if i < 1036 then decide (4 ≤ count1032 b) else (if i < 1037 then decide (5 ≤ count1032 b) else decide (6 ≤ count1032 b))) else (if i < 1040 then (if i < 1039 then decide (7 ≤ count1032 b) else decide (8 ≤ count1032 b)) else (if i < 1041 then decide (9 ≤ count1032 b) else decide (10 ≤ count1032 b))))) else (if i < 1049 then (if i < 1045 then (if i < 1043 then decide (11 ≤ count1032 b) else (if i < 1044 then decide (12 ≤ count1032 b) else decide (13 ≤ count1032 b))) else (if i < 1047 then (if i < 1046 then decide (14 ≤ count1032 b) else decide (15 ≤ count1032 b)) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b)))) else (if i < 1052 then (if i < 1050 then decide (3 ≤ count1047 b) else (if i < 1051 then decide (4 ≤ count1047 b) else decide (5 ≤ count1047 b))) else (if i < 1054 then (if i < 1053 then decide (6 ≤ count1047 b) else decide (7 ≤ count1047 b)) else (if i < 1055 then decide (8 ≤ count1047 b) else decide (9 ≤ count1047 b))))))))) else (if i < 1162 then (if i < 1109 then (if i < 1082 then (if i < 1069 then (if i < 1062 then (if i < 1059 then (if i < 1057 then decide (10 ≤ count1047 b) else (if i < 1058 then decide (11 ≤ count1047 b) else decide (12 ≤ count1047 b))) else (if i < 1060 then decide (13 ≤ count1047 b) else (if i < 1061 then decide (14 ≤ count1047 b) else decide (15 ≤ count1047 b)))) else (if i < 1065 then (if i < 1063 then decide (16 ≤ count1047 b) else (if i < 1064 then decide (17 ≤ count1047 b) else decide (18 ≤ count1047 b))) else (if i < 1067 then (if i < 1066 then decide (19 ≤ count1047 b) else decide (1 ≤ count1066 b)) else (if i < 1068 then decide (2 ≤ count1066 b) else decide (3 ≤ count1066 b))))) else (if i < 1075 then (if i < 1072 then (if i < 1070 then decide (4 ≤ count1066 b) else (if i < 1071 then decide (5 ≤ count1066 b) else decide (6 ≤ count1066 b))) else (if i < 1073 then decide (7 ≤ count1066 b) else (if i < 1074 then decide (8 ≤ count1066 b) else decide (9 ≤ count1066 b)))) else (if i < 1078 then (if i < 1076 then decide (10 ≤ count1066 b) else (if i < 1077 then decide (11 ≤ count1066 b) else decide (12 ≤ count1066 b))) else (if i < 1080 then (if i < 1079 then decide (13 ≤ count1066 b) else decide (14 ≤ count1066 b)) else (if i < 1081 then decide (15 ≤ count1066 b) else decide (16 ≤ count1066 b)))))) else (if i < 1095 then (if i < 1088 then (if i < 1085 then (if i < 1083 then decide (17 ≤ count1066 b) else (if i < 1084 then decide (18 ≤ count1066 b) else decide (19 ≤ count1066 b))) else (if i < 1086 then decide (1 ≤ count1085 b) else (if i < 1087 then decide (2 ≤ count1085 b) else decide (1 ≤ count1087 b)))) else (if i < 1091 then (if i < 1089 then decide (2 ≤ count1087 b) else (if i < 1090 then decide (3 ≤ count1087 b) else decide (1 ≤ count1090 b))) else (if i < 1093 then (if i < 1092 then decide (2 ≤ count1090 b) else decide (1 ≤ count1092 b)) else (if i < 1094 then decide (2 ≤ count1092 b) else decide (1 ≤ count1094 b))))) else (if i < 1102 then (if i < 1098 then (if i < 1096 then decide (2 ≤ count1094 b) else (if i < 1097 then decide (3 ≤ count1094 b) else decide (4 ≤ count1094 b))) else (if i < 1100 then (if i < 1099 then decide (1 ≤ count1098 b) else decide (2 ≤ count1098 b)) else (if i < 1101 then decide (3 ≤ count1098 b) else decide (4 ≤ count1098 b)))) else (if i < 1105 then (if i < 1103 then decide (5 ≤ count1098 b) else (if i < 1104 then decide (6 ≤ count1098 b) else decide (7 ≤ count1098 b))) else (if i < 1107 then (if i < 1106 then decide (1 ≤ count1105 b) else decide (2 ≤ count1105 b)) else (if i < 1108 then decide (1 ≤ count1107 b) else decide (2 ≤ count1107 b))))))) else (if i < 1135 then (if i < 1122 then (if i < 1115 then (if i < 1112 then (if i < 1110 then decide (3 ≤ count1107 b) else (if i < 1111 then decide (1 ≤ count1110 b) else decide (2 ≤ count1110 b))) else (if i < 1113 then decide (1 ≤ count1112 b) else (if i < 1114 then decide (2 ≤ count1112 b) else decide (1 ≤ count1114 b)))) else (if i < 1118 then (if i < 1116 then decide (2 ≤ count1114 b) else (if i < 1117 then decide (3 ≤ count1114 b) else decide (4 ≤ count1114 b))) else (if i < 1120 then (if i < 1119 then decide (1 ≤ count1118 b) else decide (2 ≤ count1118 b)) else (if i < 1121 then decide (3 ≤ count1118 b) else decide (4 ≤ count1118 b))))) else (if i < 1128 then (if i < 1125 then (if i < 1123 then decide (5 ≤ count1118 b) else (if i < 1124 then decide (6 ≤ count1118 b) else decide (7 ≤ count1118 b))) else (if i < 1126 then decide (1 ≤ count1125 b) else (if i < 1127 then decide (2 ≤ count1125 b) else decide (3 ≤ count1125 b)))) else (if i < 1131 then (if i < 1129 then decide (4 ≤ count1125 b) else (if i < 1130 then decide (5 ≤ count1125 b) else decide (6 ≤ count1125 b))) else (if i < 1133 then (if i < 1132 then decide (7 ≤ count1125 b) else decide (8 ≤ count1125 b)) else (if i < 1134 then decide (9 ≤ count1125 b) else decide (10 ≤ count1125 b)))))) else (if i < 1148 then (if i < 1141 then (if i < 1138 then (if i < 1136 then decide (11 ≤ count1125 b) else (if i < 1137 then decide (12 ≤ count1125 b) else decide (13 ≤ count1125 b))) else (if i < 1139 then decide (14 ≤ count1125 b) else (if i < 1140 then decide (1 ≤ count1139 b) else decide (2 ≤ count1139 b)))) else (if i < 1144 then (if i < 1142 then decide (1 ≤ count1141 b) else (if i < 1143 then decide (2 ≤ count1141 b) else decide (3 ≤ count1141 b))) else (if i < 1146 then (if i < 1145 then decide (1 ≤ count1144 b) else decide (2 ≤ count1144 b)) else (if i < 1147 then decide (1 ≤ count1146 b) else decide (2 ≤ count1146 b))))) else (if i < 1155 then (if i < 1151 then (if i < 1149 then decide (1 ≤ count1148 b) else (if i < 1150 then decide (2 ≤ count1148 b) else decide (3 ≤ count1148 b))) else (if i < 1153 then (if i < 1152 then decide (4 ≤ count1148 b) else decide (1 ≤ count1152 b)) else (if i < 1154 then decide (2 ≤ count1152 b) else decide (3 ≤ count1152 b)))) else (if i < 1158 then (if i < 1156 then decide (4 ≤ count1152 b) else (if i < 1157 then decide (5 ≤ count1152 b) else decide (6 ≤ count1152 b))) else (if i < 1160 then (if i < 1159 then decide (7 ≤ count1152 b) else decide (1 ≤ count1159 b)) else (if i < 1161 then decide (2 ≤ count1159 b) else decide (1 ≤ count1161 b)))))))) else (if i < 1215 then (if i < 1188 then (if i < 1175 then (if i < 1168 then (if i < 1165 then (if i < 1163 then decide (2 ≤ count1161 b) else (if i < 1164 then decide (1 ≤ count1163 b) else decide (2 ≤ count1163 b))) else (if i < 1166 then decide (3 ≤ count1163 b) else (if i < 1167 then decide (4 ≤ count1163 b) else decide (1 ≤ count1167 b)))) else (if i < 1171 then (if i < 1169 then decide (2 ≤ count1167 b) else (if i < 1170 then decide (1 ≤ count1169 b) else decide (2 ≤ count1169 b))) else (if i < 1173 then (if i < 1172 then decide (1 ≤ count1171 b) else decide (2 ≤ count1171 b)) else (if i < 1174 then decide (3 ≤ count1171 b) else decide (4 ≤ count1171 b))))) else (if i < 1181 then (if i < 1178 then (if i < 1176 then decide (1 ≤ count1175 b) else (if i < 1177 then decide (2 ≤ count1175 b) else decide (3 ≤ count1175 b))) else (if i < 1179 then decide (4 ≤ count1175 b) else (if i < 1180 then decide (5 ≤ count1175 b) else decide (6 ≤ count1175 b)))) else (if i < 1184 then (if i < 1182 then decide (7 ≤ count1175 b) else (if i < 1183 then decide (8 ≤ count1175 b) else decide (1 ≤ count1183 b))) else (if i < 1186 then (if i < 1185 then decide (2 ≤ count1183 b) else decide (3 ≤ count1183 b)) else (if i < 1187 then decide (4 ≤ count1183 b) else decide (5 ≤ count1183 b)))))) else (if i < 1201 then (if i < 1194 then (if i < 1191 then (if i < 1189 then decide (6 ≤ count1183 b) else (if i < 1190 then decide (7 ≤ count1183 b) else decide (8 ≤ count1183 b))) else (if i < 1192 then decide (9 ≤ count1183 b) else (if i < 1193 then decide (10 ≤ count1183 b) else decide (11 ≤ count1183 b)))) else (if i < 1197 then (if i < 1195 then decide (12 ≤ count1183 b) else (if i < 1196 then decide (13 ≤ count1183 b) else decide (14 ≤ count1183 b))) else (if i < 1199 then (if i < 1198 then decide (15 ≤ count1183 b) else decide (1 ≤ count1198 b)) else (if i < 1200 then decide (2 ≤ count1198 b) else decide (3 ≤ count1198 b))))) else (if i < 1208 then (if i < 1204 then (if i < 1202 then decide (4 ≤ count1198 b) else (if i < 1203 then decide (5 ≤ count1198 b) else decide (6 ≤ count1198 b))) else (if i < 1206 then (if i < 1205 then decide (7 ≤ count1198 b) else decide (8 ≤ count1198 b)) else (if i < 1207 then decide (9 ≤ count1198 b) else decide (10 ≤ count1198 b)))) else (if i < 1211 then (if i < 1209 then decide (11 ≤ count1198 b) else (if i < 1210 then decide (12 ≤ count1198 b) else decide (13 ≤ count1198 b))) else (if i < 1213 then (if i < 1212 then decide (14 ≤ count1198 b) else decide (15 ≤ count1198 b)) else (if i < 1214 then decide (16 ≤ count1198 b) else decide (17 ≤ count1198 b))))))) else (if i < 1241 then (if i < 1228 then (if i < 1221 then (if i < 1218 then (if i < 1216 then decide (18 ≤ count1198 b) else (if i < 1217 then decide (19 ≤ count1198 b) else decide (20 ≤ count1198 b))) else (if i < 1219 then decide (21 ≤ count1198 b) else (if i < 1220 then decide (22 ≤ count1198 b) else decide (23 ≤ count1198 b)))) else (if i < 1224 then (if i < 1222 then decide (24 ≤ count1198 b) else (if i < 1223 then decide (25 ≤ count1198 b) else decide (26 ≤ count1198 b))) else (if i < 1226 then (if i < 1225 then decide (27 ≤ count1198 b) else decide (28 ≤ count1198 b)) else (if i < 1227 then decide (29 ≤ count1198 b) else decide (1 ≤ count1227 b))))) else (if i < 1234 then (if i < 1231 then (if i < 1229 then decide (2 ≤ count1227 b) else (if i < 1230 then decide (1 ≤ count1229 b) else decide (2 ≤ count1229 b))) else (if i < 1232 then decide (3 ≤ count1229 b) else (if i < 1233 then decide (1 ≤ count1232 b) else decide (2 ≤ count1232 b)))) else (if i < 1237 then (if i < 1235 then decide (1 ≤ count1234 b) else (if i < 1236 then decide (2 ≤ count1234 b) else decide (1 ≤ count1236 b))) else (if i < 1239 then (if i < 1238 then decide (2 ≤ count1236 b) else decide (3 ≤ count1236 b)) else (if i < 1240 then decide (4 ≤ count1236 b) else decide (1 ≤ count1240 b)))))) else (if i < 1254 then (if i < 1247 then (if i < 1244 then (if i < 1242 then decide (2 ≤ count1240 b) else (if i < 1243 then decide (3 ≤ count1240 b) else decide (4 ≤ count1240 b))) else (if i < 1245 then decide (5 ≤ count1240 b) else (if i < 1246 then decide (6 ≤ count1240 b) else decide (7 ≤ count1240 b)))) else (if i < 1250 then (if i < 1248 then decide (1 ≤ count1247 b) else (if i < 1249 then decide (2 ≤ count1247 b) else decide (1 ≤ count1249 b))) else (if i < 1252 then (if i < 1251 then decide (2 ≤ count1249 b) else decide (3 ≤ count1249 b)) else (if i < 1253 then decide (1 ≤ count1252 b) else decide (2 ≤ count1252 b))))) else (if i < 1261 then (if i < 1257 then (if i < 1255 then decide (1 ≤ count1254 b) else (if i < 1256 then decide (2 ≤ count1254 b) else decide (1 ≤ count1256 b))) else (if i < 1259 then (if i < 1258 then decide (2 ≤ count1256 b) else decide (3 ≤ count1256 b)) else (if i < 1260 then decide (4 ≤ count1256 b) else decide (1 ≤ count1260 b)))) else (if i < 1264 then (if i < 1262 then decide (2 ≤ count1260 b) else (if i < 1263 then decide (3 ≤ count1260 b) else decide (4 ≤ count1260 b))) else (if i < 1266 then (if i < 1265 then decide (5 ≤ count1260 b) else decide (6 ≤ count1260 b)) else (if i < 1267 then decide (7 ≤ count1260 b) else decide (1 ≤ count1267 b)))))))))) else (if i < 1479 then (if i < 1373 then (if i < 1320 then (if i < 1294 then (if i < 1281 then (if i < 1274 then (if i < 1271 then (if i < 1269 then decide (2 ≤ count1267 b) else (if i < 1270 then decide (3 ≤ count1267 b) else decide (4 ≤ count1267 b))) else (if i < 1272 then decide (5 ≤ count1267 b) else (if i < 1273 then decide (6 ≤ count1267 b) else decide (7 ≤ count1267 b)))) else (if i < 1277 then (if i < 1275 then decide (8 ≤ count1267 b) else (if i < 1276 then decide (9 ≤ count1267 b) else decide (10 ≤ count1267 b))) else (if i < 1279 then (if i < 1278 then decide (11 ≤ count1267 b) else decide (12 ≤ count1267 b)) else (if i < 1280 then decide (13 ≤ count1267 b) else decide (14 ≤ count1267 b))))) else (if i < 1287 then (if i < 1284 then (if i < 1282 then decide (1 ≤ count1281 b) else (if i < 1283 then decide (2 ≤ count1281 b) else decide (1 ≤ count1283 b))) else (if i < 1285 then decide (2 ≤ count1283 b) else (if i < 1286 then decide (3 ≤ count1283 b) else decide (1 ≤ count1286 b)))) else (if i < 1290 then (if i < 1288 then decide (2 ≤ count1286 b) else (if i < 1289 then decide (1 ≤ count1288 b) else decide (2 ≤ count1288 b))) else (if i < 1292 then (if i < 1291 then decide (1 ≤ count1290 b) else decide (2 ≤ count1290 b)) else (if i < 1293 then decide (3 ≤ count1290 b) else decide (4 ≤ count1290 b)))))) else (if i < 1307 then (if i < 1300 then (if i < 1297 then (if i < 1295 then decide (1 ≤ count1294 b) else (if i < 1296 then decide (2 ≤ count1294 b) else decide (3 ≤ count1294 b))) else (if i < 1298 then decide (4 ≤ count1294 b) else (if i < 1299 then decide (5 ≤ count1294 b) else decide (6 ≤ count1294 b)))) else (if i < 1303 then (if i < 1301 then decide (7 ≤ count1294 b) else (if i < 1302 then decide (1 ≤ count1301 b) else decide (2 ≤ count1301 b))) else (if i < 1305 then (if i < 1304 then decide (1 ≤ count1303 b) else decide (2 ≤ count1303 b)) else (if i < 1306 then decide (1 ≤ count1305 b) else decide (2 ≤ count1305 b))))) else (if i < 1313 then (if i < 1310 then (if i < 1308 then decide (3 ≤ count1305 b) else (if i < 1309 then decide (4 ≤ count1305 b) else decide (1 ≤ count1309 b))) else (if i < 1311 then decide (2 ≤ count1309 b) else (if i < 1312 then decide (1 ≤ count1311 b) else decide (2 ≤ count1311 b)))) else (if i < 1316 then (if i < 1314 then decide (1 ≤ count1313 b) else (if i < 1315 then decide (2 ≤ count1313 b) else decide (3 ≤ count1313 b))) else (if i < 1318 then (if i < 1317 then decide (4 ≤ count1313 b) else decide (1 ≤ count1317 b)) else (if i < 1319 then decide (2 ≤ count1317 b) else decide (3 ≤ count1317 b))))))) else (if i < 1346 then (if i < 1333 then (if i < 1326 then (if i < 1323 then (if i < 1321 then decide (4 ≤ count1317 b) else (if i < 1322 then decide (5 ≤ count1317 b) else decide (6 ≤ count1317 b))) else (if i < 1324 then decide (7 ≤ count1317 b) else (if i < 1325 then decide (8 ≤ count1317 b) else decide (1 ≤ count1325 b)))) else (if i < 1329 then (if i < 1327 then decide (2 ≤ count1325 b) else (if i < 1328 then decide (3 ≤ count1325 b) else decide (4 ≤ count1325 b))) else (if i < 1331 then (if i < 1330 then decide (5 ≤ count1325 b) else decide (6 ≤ count1325 b)) else (if i < 1332 then decide (7 ≤ count1325 b) else decide (8 ≤ count1325 b))))) else (if i < 1339 then (if i < 1336 then (if i < 1334 then decide (9 ≤ count1325 b) else (if i < 1335 then decide (10 ≤ count1325 b) else decide (11 ≤ count1325 b))) else (if i < 1337 then decide (12 ≤ count1325 b) else (if i < 1338 then decide (13 ≤ count1325 b) else decide (14 ≤ count1325 b)))) else (if i < 1342 then (if i < 1340 then decide (15 ≤ count1325 b) else (if i < 1341 then decide (1 ≤ count1340 b) else decide (2 ≤ count1340 b))) else (if i < 1344 then (if i < 1343 then decide (3 ≤ count1340 b) else decide (4 ≤ count1340 b)) else (if i < 1345 then decide (5 ≤ count1340 b) else decide (6 ≤ count1340 b)))))) else (if i < 1359 then (if i < 1352 then (if i < 1349 then (if i < 1347 then decide (7 ≤ count1340 b) else (if i < 1348 then decide (8 ≤ count1340 b) else decide (9 ≤ count1340 b))) else (if i < 1350 then decide (10 ≤ count1340 b) else (if i < 1351 then decide (11 ≤ count1340 b) else decide (12 ≤ count1340 b)))) else (if i < 1355 then (if i < 1353 then decide (13 ≤ count1340 b) else (if i < 1354 then decide (14 ≤ count1340 b) else decide (15 ≤ count1340 b))) else (if i < 1357 then (if i < 1356 then decide (16 ≤ count1340 b) else decide (17 ≤ count1340 b)) else (if i < 1358 then decide (18 ≤ count1340 b) else decide (19 ≤ count1340 b))))) else (if i < 1366 then (if i < 1362 then (if i < 1360 then decide (20 ≤ count1340 b) else (if i < 1361 then decide (21 ≤ count1340 b) else decide (22 ≤ count1340 b))) else (if i < 1364 then (if i < 1363 then decide (23 ≤ count1340 b) else decide (24 ≤ count1340 b)) else (if i < 1365 then decide (25 ≤ count1340 b) else decide (26 ≤ count1340 b)))) else (if i < 1369 then (if i < 1367 then decide (27 ≤ count1340 b) else (if i < 1368 then decide (28 ≤ count1340 b) else decide (29 ≤ count1340 b))) else (if i < 1371 then (if i < 1370 then decide (1 ≤ count1369 b) else decide (2 ≤ count1369 b)) else (if i < 1372 then decide (3 ≤ count1369 b) else decide (4 ≤ count1369 b)))))))) else (if i < 1426 then (if i < 1399 then (if i < 1386 then (if i < 1379 then (if i < 1376 then (if i < 1374 then decide (5 ≤ count1369 b) else (if i < 1375 then decide (6 ≤ count1369 b) else decide (7 ≤ count1369 b))) else (if i < 1377 then decide (8 ≤ count1369 b) else (if i < 1378 then decide (9 ≤ count1369 b) else decide (10 ≤ count1369 b)))) else (if i < 1382 then (if i < 1380 then decide (11 ≤ count1369 b) else (if i < 1381 then decide (12 ≤ count1369 b) else decide (13 ≤ count1369 b))) else (if i < 1384 then (if i < 1383 then decide (14 ≤ count1369 b) else decide (15 ≤ count1369 b)) else (if i < 1385 then decide (16 ≤ count1369 b) else decide (17 ≤ count1369 b))))) else (if i < 1392 then (if i < 1389 then (if i < 1387 then decide (18 ≤ count1369 b) else (if i < 1388 then decide (19 ≤ count1369 b) else decide (20 ≤ count1369 b))) else (if i < 1390 then decide (21 ≤ count1369 b) else (if i < 1391 then decide (22 ≤ count1369 b) else decide (23 ≤ count1369 b)))) else (if i < 1395 then (if i < 1393 then decide (24 ≤ count1369 b) else (if i < 1394 then decide (25 ≤ count1369 b) else decide (26 ≤ count1369 b))) else (if i < 1397 then (if i < 1396 then decide (27 ≤ count1369 b) else decide (28 ≤ count1369 b)) else (if i < 1398 then decide (29 ≤ count1369 b) else decide (30 ≤ count1369 b)))))) else (if i < 1412 then (if i < 1405 then (if i < 1402 then (if i < 1400 then decide (31 ≤ count1369 b) else (if i < 1401 then decide (32 ≤ count1369 b) else decide (33 ≤ count1369 b))) else (if i < 1403 then decide (34 ≤ count1369 b) else (if i < 1404 then decide (35 ≤ count1369 b) else decide (36 ≤ count1369 b)))) else (if i < 1408 then (if i < 1406 then decide (37 ≤ count1369 b) else (if i < 1407 then decide (38 ≤ count1369 b) else decide (39 ≤ count1369 b))) else (if i < 1410 then (if i < 1409 then decide (40 ≤ count1369 b) else decide (41 ≤ count1369 b)) else (if i < 1411 then decide (42 ≤ count1369 b) else decide (1 ≤ count1411 b))))) else (if i < 1419 then (if i < 1415 then (if i < 1413 then decide (2 ≤ count1411 b) else (if i < 1414 then decide (1 ≤ count1413 b) else decide (2 ≤ count1413 b))) else (if i < 1417 then (if i < 1416 then decide (3 ≤ count1413 b) else decide (1 ≤ count1416 b)) else (if i < 1418 then decide (2 ≤ count1416 b) else decide (1 ≤ count1418 b)))) else (if i < 1422 then (if i < 1420 then decide (2 ≤ count1418 b) else (if i < 1421 then decide (1 ≤ count1420 b) else decide (2 ≤ count1420 b))) else (if i < 1424 then (if i < 1423 then decide (3 ≤ count1420 b) else decide (4 ≤ count1420 b)) else (if i < 1425 then decide (1 ≤ count1424 b) else decide (2 ≤ count1424 b))))))) else (if i < 1452 then (if i < 1439 then (if i < 1432 then (if i < 1429 then (if i < 1427 then decide (3 ≤ count1424 b) else (if i < 1428 then decide (4 ≤ count1424 b) else decide (5 ≤ count1424 b))) else (if i < 1430 then decide (6 ≤ count1424 b) else (if i < 1431 then decide (7 ≤ count1424 b) else decide (1 ≤ count1431 b)))) else (if i < 1435 then (if i < 1433 then decide (2 ≤ count1431 b) else (if i < 1434 then decide (1 ≤ count1433 b) else decide (2 ≤ count1433 b))) else (if i < 1437 then (if i < 1436 then decide (3 ≤ count1433 b) else decide (1 ≤ count1436 b)) else (if i < 1438 then decide (2 ≤ count1436 b) else decide (1 ≤ count1438 b))))) else (if i < 1445 then (if i < 1442 then (if i < 1440 then decide (2 ≤ count1438 b) else (if i < 1441 then decide (1 ≤ count1440 b) else decide (2 ≤ count1440 b))) else (if i < 1443 then decide (3 ≤ count1440 b) else (if i < 1444 then decide (4 ≤ count1440 b) else decide (1 ≤ count1444 b)))) else (if i < 1448 then (if i < 1446 then decide (2 ≤ count1444 b) else (if i < 1447 then decide (3 ≤ count1444 b) else decide (4 ≤ count1444 b))) else (if i < 1450 then (if i < 1449 then decide (5 ≤ count1444 b) else decide (6 ≤ count1444 b)) else (if i < 1451 then decide (7 ≤ count1444 b) else decide (1 ≤ count1451 b)))))) else (if i < 1465 then (if i < 1458 then (if i < 1455 then (if i < 1453 then decide (2 ≤ count1451 b) else (if i < 1454 then decide (3 ≤ count1451 b) else decide (4 ≤ count1451 b))) else (if i < 1456 then decide (5 ≤ count1451 b) else (if i < 1457 then decide (6 ≤ count1451 b) else decide (7 ≤ count1451 b)))) else (if i < 1461 then (if i < 1459 then decide (8 ≤ count1451 b) else (if i < 1460 then decide (9 ≤ count1451 b) else decide (10 ≤ count1451 b))) else (if i < 1463 then (if i < 1462 then decide (11 ≤ count1451 b) else decide (12 ≤ count1451 b)) else (if i < 1464 then decide (13 ≤ count1451 b) else decide (14 ≤ count1451 b))))) else (if i < 1472 then (if i < 1468 then (if i < 1466 then decide (1 ≤ count1465 b) else (if i < 1467 then decide (2 ≤ count1465 b) else decide (1 ≤ count1467 b))) else (if i < 1470 then (if i < 1469 then decide (2 ≤ count1467 b) else decide (3 ≤ count1467 b)) else (if i < 1471 then decide (1 ≤ count1470 b) else decide (2 ≤ count1470 b)))) else (if i < 1475 then (if i < 1473 then decide (1 ≤ count1472 b) else (if i < 1474 then decide (2 ≤ count1472 b) else decide (1 ≤ count1474 b))) else (if i < 1477 then (if i < 1476 then decide (2 ≤ count1474 b) else decide (3 ≤ count1474 b)) else (if i < 1478 then decide (4 ≤ count1474 b) else decide (1 ≤ count1478 b))))))))) else (if i < 1585 then (if i < 1532 then (if i < 1505 then (if i < 1492 then (if i < 1485 then (if i < 1482 then (if i < 1480 then decide (2 ≤ count1478 b) else (if i < 1481 then decide (3 ≤ count1478 b) else decide (4 ≤ count1478 b))) else (if i < 1483 then decide (5 ≤ count1478 b) else (if i < 1484 then decide (6 ≤ count1478 b) else decide (7 ≤ count1478 b)))) else (if i < 1488 then (if i < 1486 then decide (1 ≤ count1485 b) else (if i < 1487 then decide (2 ≤ count1485 b) else decide (1 ≤ count1487 b))) else (if i < 1490 then (if i < 1489 then decide (2 ≤ count1487 b) else decide (1 ≤ count1489 b)) else (if i < 1491 then decide (2 ≤ count1489 b) else decide (3 ≤ count1489 b))))) else (if i < 1498 then (if i < 1495 then (if i < 1493 then decide (4 ≤ count1489 b) else (if i < 1494 then decide (1 ≤ count1493 b) else decide (2 ≤ count1493 b))) else (if i < 1496 then decide (1 ≤ count1495 b) else (if i < 1497 then decide (2 ≤ count1495 b) else decide (1 ≤ count1497 b)))) else (if i < 1501 then (if i < 1499 then decide (2 ≤ count1497 b) else (if i < 1500 then decide (3 ≤ count1497 b) else decide (4 ≤ count1497 b))) else (if i < 1503 then (if i < 1502 then decide (1 ≤ count1501 b) else decide (2 ≤ count1501 b)) else (if i < 1504 then decide (3 ≤ count1501 b) else decide (4 ≤ count1501 b)))))) else (if i < 1518 then (if i < 1511 then (if i < 1508 then (if i < 1506 then decide (5 ≤ count1501 b) else (if i < 1507 then decide (6 ≤ count1501 b) else decide (7 ≤ count1501 b))) else (if i < 1509 then decide (8 ≤ count1501 b) else (if i < 1510 then decide (1 ≤ count1509 b) else decide (2 ≤ count1509 b)))) else (if i < 1514 then (if i < 1512 then decide (3 ≤ count1509 b) else (if i < 1513 then decide (4 ≤ count1509 b) else decide (5 ≤ count1509 b))) else (if i < 1516 then (if i < 1515 then decide (6 ≤ count1509 b) else decide (7 ≤ count1509 b)) else (if i < 1517 then decide (8 ≤ count1509 b) else decide (9 ≤ count1509 b))))) else (if i < 1525 then (if i < 1521 then (if i < 1519 then decide (10 ≤ count1509 b) else (if i < 1520 then decide (11 ≤ count1509 b) else decide (12 ≤ count1509 b))) else (if i < 1523 then (if i < 1522 then decide (13 ≤ count1509 b) else decide (14 ≤ count1509 b)) else (if i < 1524 then decide (15 ≤ count1509 b) else decide (1 ≤ count1524 b)))) else (if i < 1528 then (if i < 1526 then decide (2 ≤ count1524 b) else (if i < 1527 then decide (3 ≤ count1524 b) else decide (4 ≤ count1524 b))) else (if i < 1530 then (if i < 1529 then decide (5 ≤ count1524 b) else decide (6 ≤ count1524 b)) else (if i < 1531 then decide (7 ≤ count1524 b) else decide (8 ≤ count1524 b))))))) else (if i < 1558 then (if i < 1545 then (if i < 1538 then (if i < 1535 then (if i < 1533 then decide (9 ≤ count1524 b) else (if i < 1534 then decide (10 ≤ count1524 b) else decide (11 ≤ count1524 b))) else (if i < 1536 then decide (12 ≤ count1524 b) else (if i < 1537 then decide (13 ≤ count1524 b) else decide (14 ≤ count1524 b)))) else (if i < 1541 then (if i < 1539 then decide (15 ≤ count1524 b) else (if i < 1540 then decide (16 ≤ count1524 b) else decide (17 ≤ count1524 b))) else (if i < 1543 then (if i < 1542 then decide (18 ≤ count1524 b) else decide (1 ≤ count1542 b)) else (if i < 1544 then decide (2 ≤ count1542 b) else decide (1 ≤ count1544 b))))) else (if i < 1551 then (if i < 1548 then (if i < 1546 then decide (2 ≤ count1544 b) else (if i < 1547 then decide (3 ≤ count1544 b) else decide (1 ≤ count1547 b))) else (if i < 1549 then decide (2 ≤ count1547 b) else (if i < 1550 then decide (1 ≤ count1549 b) else decide (2 ≤ count1549 b)))) else (if i < 1554 then (if i < 1552 then decide (1 ≤ count1551 b) else (if i < 1553 then decide (2 ≤ count1551 b) else decide (3 ≤ count1551 b))) else (if i < 1556 then (if i < 1555 then decide (4 ≤ count1551 b) else decide (1 ≤ count1555 b)) else (if i < 1557 then decide (2 ≤ count1555 b) else decide (3 ≤ count1555 b)))))) else (if i < 1571 then (if i < 1564 then (if i < 1561 then (if i < 1559 then decide (4 ≤ count1555 b) else (if i < 1560 then decide (5 ≤ count1555 b) else decide (6 ≤ count1555 b))) else (if i < 1562 then decide (7 ≤ count1555 b) else (if i < 1563 then decide (1 ≤ count1562 b) else decide (2 ≤ count1562 b)))) else (if i < 1567 then (if i < 1565 then decide (1 ≤ count1564 b) else (if i < 1566 then decide (2 ≤ count1564 b) else decide (3 ≤ count1564 b))) else (if i < 1569 then (if i < 1568 then decide (1 ≤ count1567 b) else decide (2 ≤ count1567 b)) else (if i < 1570 then decide (1 ≤ count1569 b) else decide (2 ≤ count1569 b))))) else (if i < 1578 then (if i < 1574 then (if i < 1572 then decide (1 ≤ count1571 b) else (if i < 1573 then decide (2 ≤ count1571 b) else decide (3 ≤ count1571 b))) else (if i < 1576 then (if i < 1575 then decide (4 ≤ count1571 b) else decide (1 ≤ count1575 b)) else (if i < 1577 then decide (2 ≤ count1575 b) else decide (3 ≤ count1575 b)))) else (if i < 1581 then (if i < 1579 then decide (4 ≤ count1575 b) else (if i < 1580 then decide (5 ≤ count1575 b) else decide (6 ≤ count1575 b))) else (if i < 1583 then (if i < 1582 then decide (7 ≤ count1575 b) else decide (1 ≤ count1582 b)) else (if i < 1584 then decide (2 ≤ count1582 b) else decide (3 ≤ count1582 b)))))))) else (if i < 1638 then (if i < 1611 then (if i < 1598 then (if i < 1591 then (if i < 1588 then (if i < 1586 then decide (4 ≤ count1582 b) else (if i < 1587 then decide (5 ≤ count1582 b) else decide (6 ≤ count1582 b))) else (if i < 1589 then decide (7 ≤ count1582 b) else (if i < 1590 then decide (8 ≤ count1582 b) else decide (9 ≤ count1582 b)))) else (if i < 1594 then (if i < 1592 then decide (10 ≤ count1582 b) else (if i < 1593 then decide (11 ≤ count1582 b) else decide (12 ≤ count1582 b))) else (if i < 1596 then (if i < 1595 then decide (13 ≤ count1582 b) else decide (14 ≤ count1582 b)) else (if i < 1597 then decide (1 ≤ count1596 b) else decide (2 ≤ count1596 b))))) else (if i < 1604 then (if i < 1601 then (if i < 1599 then decide (1 ≤ count1598 b) else (if i < 1600 then decide (2 ≤ count1598 b) else decide (3 ≤ count1598 b))) else (if i < 1602 then decide (1 ≤ count1601 b) else (if i < 1603 then decide (2 ≤ count1601 b) else decide (1 ≤ count1603 b)))) else (if i < 1607 then (if i < 1605 then decide (2 ≤ count1603 b) else (if i < 1606 then decide (1 ≤ count1605 b) else decide (2 ≤ count1605 b))) else (if i < 1609 then (if i < 1608 then decide (3 ≤ count1605 b) else decide (4 ≤ count1605 b)) else (if i < 1610 then decide (1 ≤ count1609 b) else decide (2 ≤ count1609 b)))))) else (if i < 1624 then (if i < 1617 then (if i < 1614 then (if i < 1612 then decide (3 ≤ count1609 b) else (if i < 1613 then decide (4 ≤ count1609 b) else decide (5 ≤ count1609 b))) else (if i < 1615 then decide (6 ≤ count1609 b) else (if i < 1616 then decide (7 ≤ count1609 b) else decide (1 ≤ count1616 b)))) else (if i < 1620 then (if i < 1618 then decide (2 ≤ count1616 b) else (if i < 1619 then decide (1 ≤ count1618 b) else decide (2 ≤ count1618 b))) else (if i < 1622 then (if i < 1621 then decide (1 ≤ count1620 b) else decide (2 ≤ count1620 b)) else (if i < 1623 then decide (3 ≤ count1620 b) else decide (4 ≤ count1620 b))))) else (if i < 1631 then (if i < 1627 then (if i < 1625 then decide (1 ≤ count1624 b) else (if i < 1626 then decide (2 ≤ count1624 b) else decide (1 ≤ count1626 b))) else (if i < 1629 then (if i < 1628 then decide (2 ≤ count1626 b) else decide (1 ≤ count1628 b)) else (if i < 1630 then decide (2 ≤ count1628 b) else decide (3 ≤ count1628 b)))) else (if i < 1634 then (if i < 1632 then decide (4 ≤ count1628 b) else (if i < 1633 then decide (1 ≤ count1632 b) else decide (2 ≤ count1632 b))) else (if i < 1636 then (if i < 1635 then decide (3 ≤ count1632 b) else decide (4 ≤ count1632 b)) else (if i < 1637 then decide (5 ≤ count1632 b) else decide (6 ≤ count1632 b))))))) else (if i < 1664 then (if i < 1651 then (if i < 1644 then (if i < 1641 then (if i < 1639 then decide (7 ≤ count1632 b) else (if i < 1640 then decide (8 ≤ count1632 b) else decide (1 ≤ count1640 b))) else (if i < 1642 then decide (2 ≤ count1640 b) else (if i < 1643 then decide (3 ≤ count1640 b) else decide (4 ≤ count1640 b)))) else (if i < 1647 then (if i < 1645 then decide (5 ≤ count1640 b) else (if i < 1646 then decide (6 ≤ count1640 b) else decide (7 ≤ count1640 b))) else (if i < 1649 then (if i < 1648 then decide (8 ≤ count1640 b) else decide (9 ≤ count1640 b)) else (if i < 1650 then decide (10 ≤ count1640 b) else decide (11 ≤ count1640 b))))) else (if i < 1657 then (if i < 1654 then (if i < 1652 then decide (12 ≤ count1640 b) else (if i < 1653 then decide (13 ≤ count1640 b) else decide (14 ≤ count1640 b))) else (if i < 1655 then decide (15 ≤ count1640 b) else (if i < 1656 then decide (1 ≤ count1655 b) else decide (2 ≤ count1655 b)))) else (if i < 1660 then (if i < 1658 then decide (3 ≤ count1655 b) else (if i < 1659 then decide (4 ≤ count1655 b) else decide (5 ≤ count1655 b))) else (if i < 1662 then (if i < 1661 then decide (6 ≤ count1655 b) else decide (7 ≤ count1655 b)) else (if i < 1663 then decide (8 ≤ count1655 b) else decide (9 ≤ count1655 b)))))) else (if i < 1677 then (if i < 1670 then (if i < 1667 then (if i < 1665 then decide (10 ≤ count1655 b) else (if i < 1666 then decide (11 ≤ count1655 b) else decide (12 ≤ count1655 b))) else (if i < 1668 then decide (13 ≤ count1655 b) else (if i < 1669 then decide (14 ≤ count1655 b) else decide (15 ≤ count1655 b)))) else (if i < 1673 then (if i < 1671 then decide (16 ≤ count1655 b) else (if i < 1672 then decide (17 ≤ count1655 b) else decide (18 ≤ count1655 b))) else (if i < 1675 then (if i < 1674 then decide (1 ≤ count1673 b) else decide (2 ≤ count1673 b)) else (if i < 1676 then decide (3 ≤ count1673 b) else decide (4 ≤ count1673 b))))) else (if i < 1684 then (if i < 1680 then (if i < 1678 then decide (5 ≤ count1673 b) else (if i < 1679 then decide (6 ≤ count1673 b) else decide (7 ≤ count1673 b))) else (if i < 1682 then (if i < 1681 then decide (8 ≤ count1673 b) else decide (9 ≤ count1673 b)) else (if i < 1683 then decide (10 ≤ count1673 b) else decide (11 ≤ count1673 b)))) else (if i < 1687 then (if i < 1685 then decide (12 ≤ count1673 b) else (if i < 1686 then decide (13 ≤ count1673 b) else decide (14 ≤ count1673 b))) else (if i < 1689 then (if i < 1688 then decide (15 ≤ count1673 b) else decide (16 ≤ count1673 b)) else (if i < 1690 then decide (17 ≤ count1673 b) else decide (18 ≤ count1673 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (6 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (8 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (11 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (13 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (15 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (17 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (18 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (19 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (22 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (28 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (29 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (30 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (128 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (130 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (132 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (134 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (135 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (136 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (137 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (138 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (140 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (142 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (148 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (149 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (151 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (153 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (154 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (155 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (157 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (159 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (198 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (201 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (205 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (207 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (214 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (218 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (220 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (221 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (222 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (226 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (230 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (238 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (256 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (257 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (258 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (260 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (261 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (262 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (263 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (264 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (266 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (267 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (268 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (270 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (271 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (273 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (275 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (276 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (277 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (279 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (280 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (281 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (282 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (283 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (287 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (320 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (321 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (326 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (327 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (328 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (329 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (331 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (333 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (335 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (337 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (338 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (339 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (342 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (346 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (348 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (349 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (350 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (384 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (385 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (389 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (390 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (391 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (392 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (393 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (395 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (397 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (399 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (400 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (401 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (402 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (403 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (406 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (410 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (412 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (413 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (414 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (480 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (481 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (486 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (487 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (493 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (495 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (497 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (498 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (499 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (502 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (506 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (508 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (509 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (510 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (BallClauseLogic.Endpoint q (6 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (BallClauseLogic.Endpoint q (11 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (13 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (30 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (128 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (130 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (140 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (142 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (153 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (155 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (159 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (201 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (205 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (207 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (214 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (218 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (220 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (221 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (226 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (230 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (238 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (256 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (260 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (262 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (266 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (270 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (326 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (328 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (329 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (331 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (335 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (339 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (346 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (349 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (392 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (395 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (400 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (487 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (493 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (495 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (497 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (499 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (502 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (509 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (510 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (1 ≤ count235 (baseVal q)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (1 ≤ count237 (baseVal q)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (1 ≤ count239 (baseVal q)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (2 ≤ count239 (baseVal q)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (1 ≤ count241 (baseVal q)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (1 ≤ count243 (baseVal q)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (2 ≤ count243 (baseVal q)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (2 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value258 (q : Snake 81) : valuation q 258 = decide (2 ≤ count257 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value260 (q : Snake 81) : valuation q 260 = decide (2 ≤ count259 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value278 (q : Snake 81) : valuation q 278 = decide (2 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value286 (q : Snake 81) : valuation q 286 = decide (2 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value288 (q : Snake 81) : valuation q 288 = decide (2 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value304 (q : Snake 81) : valuation q 304 = decide (2 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value306 (q : Snake 81) : valuation q 306 = decide (2 ≤ count305 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value316 (q : Snake 81) : valuation q 316 = decide (2 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value324 (q : Snake 81) : valuation q 324 = decide (2 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value326 (q : Snake 81) : valuation q 326 = decide (2 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value346 (q : Snake 81) : valuation q 346 = decide (2 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value348 (q : Snake 81) : valuation q 348 = decide (2 ≤ count347 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value354 (q : Snake 81) : valuation q 354 = decide (2 ≤ count353 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value367 (q : Snake 81) : valuation q 367 = decide (1 ≤ count367 (baseVal q)) := rfl
theorem value368 (q : Snake 81) : valuation q 368 = decide (2 ≤ count367 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value370 (q : Snake 81) : valuation q 370 = decide (2 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value372 (q : Snake 81) : valuation q 372 = decide (2 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value374 (q : Snake 81) : valuation q 374 = decide (2 ≤ count373 (baseVal q)) := rfl
theorem value375 (q : Snake 81) : valuation q 375 = decide (1 ≤ count375 (baseVal q)) := rfl
theorem value376 (q : Snake 81) : valuation q 376 = decide (2 ≤ count375 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value378 (q : Snake 81) : valuation q 378 = decide (2 ≤ count377 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value392 (q : Snake 81) : valuation q 392 = decide (2 ≤ count391 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value397 (q : Snake 81) : valuation q 397 = decide (1 ≤ count397 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value400 (q : Snake 81) : valuation q 400 = decide (2 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value402 (q : Snake 81) : valuation q 402 = decide (2 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value414 (q : Snake 81) : valuation q 414 = decide (2 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value422 (q : Snake 81) : valuation q 422 = decide (2 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value426 (q : Snake 81) : valuation q 426 = decide (2 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value428 (q : Snake 81) : valuation q 428 = decide (2 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value430 (q : Snake 81) : valuation q 430 = decide (2 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value460 (q : Snake 81) : valuation q 460 = decide (2 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value462 (q : Snake 81) : valuation q 462 = decide (2 ≤ count461 (baseVal q)) := rfl
theorem value464 (q : Snake 81) : valuation q 464 = decide (2 ≤ count463 (baseVal q)) := rfl
theorem value1411 (q : Snake 81) : valuation q 1411 = decide (1 ≤ count1411 (baseVal q)) := rfl
theorem value1412 (q : Snake 81) : valuation q 1412 = decide (2 ≤ count1411 (baseVal q)) := rfl
theorem value1413 (q : Snake 81) : valuation q 1413 = decide (1 ≤ count1413 (baseVal q)) := rfl
theorem value1414 (q : Snake 81) : valuation q 1414 = decide (2 ≤ count1413 (baseVal q)) := rfl
theorem value1415 (q : Snake 81) : valuation q 1415 = decide (3 ≤ count1413 (baseVal q)) := rfl
theorem value1416 (q : Snake 81) : valuation q 1416 = decide (1 ≤ count1416 (baseVal q)) := rfl
theorem value1417 (q : Snake 81) : valuation q 1417 = decide (2 ≤ count1416 (baseVal q)) := rfl
theorem value1418 (q : Snake 81) : valuation q 1418 = decide (1 ≤ count1418 (baseVal q)) := rfl
theorem value1419 (q : Snake 81) : valuation q 1419 = decide (2 ≤ count1418 (baseVal q)) := rfl
theorem value1420 (q : Snake 81) : valuation q 1420 = decide (1 ≤ count1420 (baseVal q)) := rfl
theorem value1421 (q : Snake 81) : valuation q 1421 = decide (2 ≤ count1420 (baseVal q)) := rfl
theorem value1422 (q : Snake 81) : valuation q 1422 = decide (3 ≤ count1420 (baseVal q)) := rfl
theorem value1423 (q : Snake 81) : valuation q 1423 = decide (4 ≤ count1420 (baseVal q)) := rfl
theorem value1424 (q : Snake 81) : valuation q 1424 = decide (1 ≤ count1424 (baseVal q)) := rfl
theorem value1425 (q : Snake 81) : valuation q 1425 = decide (2 ≤ count1424 (baseVal q)) := rfl
theorem value1426 (q : Snake 81) : valuation q 1426 = decide (3 ≤ count1424 (baseVal q)) := rfl
theorem value1427 (q : Snake 81) : valuation q 1427 = decide (4 ≤ count1424 (baseVal q)) := rfl
theorem value1428 (q : Snake 81) : valuation q 1428 = decide (5 ≤ count1424 (baseVal q)) := rfl
theorem value1431 (q : Snake 81) : valuation q 1431 = decide (1 ≤ count1431 (baseVal q)) := rfl
theorem value1432 (q : Snake 81) : valuation q 1432 = decide (2 ≤ count1431 (baseVal q)) := rfl
theorem value1433 (q : Snake 81) : valuation q 1433 = decide (1 ≤ count1433 (baseVal q)) := rfl
theorem value1434 (q : Snake 81) : valuation q 1434 = decide (2 ≤ count1433 (baseVal q)) := rfl
theorem value1435 (q : Snake 81) : valuation q 1435 = decide (3 ≤ count1433 (baseVal q)) := rfl
theorem value1436 (q : Snake 81) : valuation q 1436 = decide (1 ≤ count1436 (baseVal q)) := rfl
theorem value1437 (q : Snake 81) : valuation q 1437 = decide (2 ≤ count1436 (baseVal q)) := rfl
theorem value1438 (q : Snake 81) : valuation q 1438 = decide (1 ≤ count1438 (baseVal q)) := rfl
theorem value1439 (q : Snake 81) : valuation q 1439 = decide (2 ≤ count1438 (baseVal q)) := rfl
theorem value1440 (q : Snake 81) : valuation q 1440 = decide (1 ≤ count1440 (baseVal q)) := rfl
theorem value1441 (q : Snake 81) : valuation q 1441 = decide (2 ≤ count1440 (baseVal q)) := rfl
theorem value1442 (q : Snake 81) : valuation q 1442 = decide (3 ≤ count1440 (baseVal q)) := rfl
theorem value1443 (q : Snake 81) : valuation q 1443 = decide (4 ≤ count1440 (baseVal q)) := rfl
theorem value1444 (q : Snake 81) : valuation q 1444 = decide (1 ≤ count1444 (baseVal q)) := rfl
theorem value1445 (q : Snake 81) : valuation q 1445 = decide (2 ≤ count1444 (baseVal q)) := rfl
theorem value1446 (q : Snake 81) : valuation q 1446 = decide (3 ≤ count1444 (baseVal q)) := rfl
theorem value1447 (q : Snake 81) : valuation q 1447 = decide (4 ≤ count1444 (baseVal q)) := rfl
theorem value1448 (q : Snake 81) : valuation q 1448 = decide (5 ≤ count1444 (baseVal q)) := rfl
theorem value1449 (q : Snake 81) : valuation q 1449 = decide (6 ≤ count1444 (baseVal q)) := rfl
theorem value1451 (q : Snake 81) : valuation q 1451 = decide (1 ≤ count1451 (baseVal q)) := rfl
theorem value1452 (q : Snake 81) : valuation q 1452 = decide (2 ≤ count1451 (baseVal q)) := rfl
theorem value1453 (q : Snake 81) : valuation q 1453 = decide (3 ≤ count1451 (baseVal q)) := rfl
theorem value1454 (q : Snake 81) : valuation q 1454 = decide (4 ≤ count1451 (baseVal q)) := rfl
theorem value1455 (q : Snake 81) : valuation q 1455 = decide (5 ≤ count1451 (baseVal q)) := rfl
theorem value1456 (q : Snake 81) : valuation q 1456 = decide (6 ≤ count1451 (baseVal q)) := rfl
theorem value1457 (q : Snake 81) : valuation q 1457 = decide (7 ≤ count1451 (baseVal q)) := rfl
theorem value1458 (q : Snake 81) : valuation q 1458 = decide (8 ≤ count1451 (baseVal q)) := rfl
theorem value1459 (q : Snake 81) : valuation q 1459 = decide (9 ≤ count1451 (baseVal q)) := rfl
theorem value1460 (q : Snake 81) : valuation q 1460 = decide (10 ≤ count1451 (baseVal q)) := rfl
theorem value1465 (q : Snake 81) : valuation q 1465 = decide (1 ≤ count1465 (baseVal q)) := rfl
theorem value1466 (q : Snake 81) : valuation q 1466 = decide (2 ≤ count1465 (baseVal q)) := rfl
theorem value1467 (q : Snake 81) : valuation q 1467 = decide (1 ≤ count1467 (baseVal q)) := rfl
theorem value1468 (q : Snake 81) : valuation q 1468 = decide (2 ≤ count1467 (baseVal q)) := rfl
theorem value1469 (q : Snake 81) : valuation q 1469 = decide (3 ≤ count1467 (baseVal q)) := rfl
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
theorem value1485 (q : Snake 81) : valuation q 1485 = decide (1 ≤ count1485 (baseVal q)) := rfl
theorem value1486 (q : Snake 81) : valuation q 1486 = decide (2 ≤ count1485 (baseVal q)) := rfl
theorem value1487 (q : Snake 81) : valuation q 1487 = decide (1 ≤ count1487 (baseVal q)) := rfl
theorem value1488 (q : Snake 81) : valuation q 1488 = decide (2 ≤ count1487 (baseVal q)) := rfl
theorem value1489 (q : Snake 81) : valuation q 1489 = decide (1 ≤ count1489 (baseVal q)) := rfl
theorem value1490 (q : Snake 81) : valuation q 1490 = decide (2 ≤ count1489 (baseVal q)) := rfl
theorem value1491 (q : Snake 81) : valuation q 1491 = decide (3 ≤ count1489 (baseVal q)) := rfl
theorem value1492 (q : Snake 81) : valuation q 1492 = decide (4 ≤ count1489 (baseVal q)) := rfl
theorem value1493 (q : Snake 81) : valuation q 1493 = decide (1 ≤ count1493 (baseVal q)) := rfl
theorem value1494 (q : Snake 81) : valuation q 1494 = decide (2 ≤ count1493 (baseVal q)) := rfl
theorem value1495 (q : Snake 81) : valuation q 1495 = decide (1 ≤ count1495 (baseVal q)) := rfl
theorem value1496 (q : Snake 81) : valuation q 1496 = decide (2 ≤ count1495 (baseVal q)) := rfl
theorem value1497 (q : Snake 81) : valuation q 1497 = decide (1 ≤ count1497 (baseVal q)) := rfl
theorem value1498 (q : Snake 81) : valuation q 1498 = decide (2 ≤ count1497 (baseVal q)) := rfl
theorem value1499 (q : Snake 81) : valuation q 1499 = decide (3 ≤ count1497 (baseVal q)) := rfl
theorem value1500 (q : Snake 81) : valuation q 1500 = decide (4 ≤ count1497 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (2 ≤ count1501 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (3 ≤ count1501 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (4 ≤ count1501 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (5 ≤ count1501 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (6 ≤ count1501 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (7 ≤ count1501 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (3 ≤ count1509 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (4 ≤ count1509 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (5 ≤ count1509 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (6 ≤ count1509 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (7 ≤ count1509 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (8 ≤ count1509 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (9 ≤ count1509 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (7 ≤ count1524 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (8 ≤ count1524 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (9 ≤ count1524 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (10 ≤ count1524 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (11 ≤ count1524 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (12 ≤ count1524 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (13 ≤ count1524 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (1 ≤ count1542 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (2 ≤ count1542 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (1 ≤ count1544 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (2 ≤ count1544 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (3 ≤ count1544 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (1 ≤ count1547 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (2 ≤ count1547 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (1 ≤ count1549 (baseVal q)) := rfl
theorem value1550 (q : Snake 81) : valuation q 1550 = decide (2 ≤ count1549 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1552 (q : Snake 81) : valuation q 1552 = decide (2 ≤ count1551 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (3 ≤ count1551 (baseVal q)) := rfl
theorem value1554 (q : Snake 81) : valuation q 1554 = decide (4 ≤ count1551 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (1 ≤ count1555 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (2 ≤ count1555 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (3 ≤ count1555 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (4 ≤ count1555 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (5 ≤ count1555 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (6 ≤ count1555 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (1 ≤ count1562 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (2 ≤ count1562 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1567 (q : Snake 81) : valuation q 1567 = decide (1 ≤ count1567 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (2 ≤ count1567 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (1 ≤ count1569 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (2 ≤ count1569 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (1 ≤ count1571 (baseVal q)) := rfl
theorem value1572 (q : Snake 81) : valuation q 1572 = decide (2 ≤ count1571 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (3 ≤ count1571 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (1 ≤ count1575 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (2 ≤ count1575 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (3 ≤ count1575 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (2 ≤ count1582 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (3 ≤ count1582 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (4 ≤ count1582 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (5 ≤ count1582 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (6 ≤ count1582 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (7 ≤ count1582 (baseVal q)) := rfl
theorem value1596 (q : Snake 81) : valuation q 1596 = decide (1 ≤ count1596 (baseVal q)) := rfl
theorem value1597 (q : Snake 81) : valuation q 1597 = decide (2 ≤ count1596 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (1 ≤ count1598 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (2 ≤ count1598 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (3 ≤ count1598 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (1 ≤ count1601 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (2 ≤ count1601 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (1 ≤ count1603 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (2 ≤ count1603 (baseVal q)) := rfl
theorem value1605 (q : Snake 81) : valuation q 1605 = decide (1 ≤ count1605 (baseVal q)) := rfl
theorem value1606 (q : Snake 81) : valuation q 1606 = decide (2 ≤ count1605 (baseVal q)) := rfl
theorem value1607 (q : Snake 81) : valuation q 1607 = decide (3 ≤ count1605 (baseVal q)) := rfl
theorem value1609 (q : Snake 81) : valuation q 1609 = decide (1 ≤ count1609 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (2 ≤ count1609 (baseVal q)) := rfl
theorem value1611 (q : Snake 81) : valuation q 1611 = decide (3 ≤ count1609 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (4 ≤ count1609 (baseVal q)) := rfl
theorem value1613 (q : Snake 81) : valuation q 1613 = decide (5 ≤ count1609 (baseVal q)) := rfl
theorem value1616 (q : Snake 81) : valuation q 1616 = decide (1 ≤ count1616 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (1 ≤ count1620 (baseVal q)) := rfl
theorem value1624 (q : Snake 81) : valuation q 1624 = decide (1 ≤ count1624 (baseVal q)) := rfl
theorem value1626 (q : Snake 81) : valuation q 1626 = decide (1 ≤ count1626 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (1 ≤ count1628 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (1 ≤ count1632 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (2 ≤ count1632 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (1 ≤ count1640 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (2 ≤ count1640 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (3 ≤ count1640 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (4 ≤ count1640 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (5 ≤ count1640 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (6 ≤ count1640 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (5 ≤ count1655 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (6 ≤ count1655 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (7 ≤ count1655 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (8 ≤ count1655 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (9 ≤ count1655 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (10 ≤ count1655 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (11 ≤ count1655 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (18 ≤ count1673 (baseVal q)) := rfl
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
theorem meaningNeg79 (b : Nat → Bool) : literal (valuationOf b) (-79) = decide (1 ≤ countLit b [-79]) := by
  change literal b (-79) = decide (1 ≤ countLit b [-79])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-79) <;> decide
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
theorem meaningNeg35 (b : Nat → Bool) : literal (valuationOf b) (-35) = decide (1 ≤ countLit b [-35]) := by
  change literal b (-35) = decide (1 ≤ countLit b [-35])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-35) <;> decide
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
theorem meaningNeg27 (b : Nat → Bool) : literal (valuationOf b) (-27) = decide (1 ≤ countLit b [-27]) := by
  change literal b (-27) = decide (1 ≤ countLit b [-27])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-27) <;> decide
theorem meaningNeg25 (b : Nat → Bool) : literal (valuationOf b) (-25) = decide (1 ≤ countLit b [-25]) := by
  change literal b (-25) = decide (1 ≤ countLit b [-25])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-25) <;> decide
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
theorem meaningNeg2 (b : Nat → Bool) : literal (valuationOf b) (-2) = decide (1 ≤ countLit b [-2]) := by
  change literal b (-2) = decide (1 ≤ countLit b [-2])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-2) <;> decide
theorem meaning119 (b : Nat → Bool) : literal (valuationOf b) (119) = decide (1 ≤ countLit b [119]) := by
  change literal b (119) = decide (1 ≤ countLit b [119])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (119) <;> decide
theorem meaning121 (b : Nat → Bool) : literal (valuationOf b) (121) = decide (1 ≤ countLit b [121]) := by
  change literal b (121) = decide (1 ≤ countLit b [121])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (121) <;> decide
theorem meaning122 (b : Nat → Bool) : literal (valuationOf b) (122) = decide (1 ≤ countLit b [122]) := by
  change literal b (122) = decide (1 ≤ countLit b [122])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (122) <;> decide
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
theorem meaning129 (b : Nat → Bool) : literal (valuationOf b) (129) = decide (1 ≤ countLit b [129]) := by
  change literal b (129) = decide (1 ≤ countLit b [129])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (129) <;> decide
theorem meaning132 (b : Nat → Bool) : literal (valuationOf b) (132) = decide (1 ≤ countLit b [132]) := by
  change literal b (132) = decide (1 ≤ countLit b [132])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (132) <;> decide
theorem meaning138 (b : Nat → Bool) : literal (valuationOf b) (138) = decide (1 ≤ countLit b [138]) := by
  change literal b (138) = decide (1 ≤ countLit b [138])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (138) <;> decide
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
theorem meaning144 (b : Nat → Bool) : literal (valuationOf b) (144) = decide (1 ≤ countLit b [144]) := by
  change literal b (144) = decide (1 ≤ countLit b [144])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (144) <;> decide
theorem meaning147 (b : Nat → Bool) : literal (valuationOf b) (147) = decide (1 ≤ countLit b [147]) := by
  change literal b (147) = decide (1 ≤ countLit b [147])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (147) <;> decide
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
theorem meaning170 (b : Nat → Bool) : literal (valuationOf b) (170) = decide (1 ≤ countLit b [170]) := by
  change literal b (170) = decide (1 ≤ countLit b [170])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (170) <;> decide
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
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
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
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
theorem meaning192 (b : Nat → Bool) : literal (valuationOf b) (192) = decide (1 ≤ countLit b [192]) := by
  change literal b (192) = decide (1 ≤ countLit b [192])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (192) <;> decide
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
theorem meaning212 (b : Nat → Bool) : literal (valuationOf b) (212) = decide (1 ≤ countLit b [212]) := by
  change literal b (212) = decide (1 ≤ countLit b [212])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (212) <;> decide
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) (215) = decide (1 ≤ countLit b [215]) := by
  change literal b (215) = decide (1 ≤ countLit b [215])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (215) <;> decide
theorem meaning216 (b : Nat → Bool) : literal (valuationOf b) (216) = decide (1 ≤ countLit b [216]) := by
  change literal b (216) = decide (1 ≤ countLit b [216])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (216) <;> decide
theorem meaning218 (b : Nat → Bool) : literal (valuationOf b) (218) = decide (1 ≤ countLit b [218]) := by
  change literal b (218) = decide (1 ≤ countLit b [218])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (218) <;> decide
theorem meaning222 (b : Nat → Bool) : literal (valuationOf b) (222) = decide (1 ≤ countLit b [222]) := by
  change literal b (222) = decide (1 ≤ countLit b [222])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (222) <;> decide
theorem meaning224 (b : Nat → Bool) : literal (valuationOf b) (224) = decide (1 ≤ countLit b [224]) := by
  change literal b (224) = decide (1 ≤ countLit b [224])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (224) <;> decide
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) (225) = decide (1 ≤ countLit b [225]) := by
  change literal b (225) = decide (1 ≤ countLit b [225])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (225) <;> decide
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) (229) = decide (1 ≤ countLit b [229]) := by
  change literal b (229) = decide (1 ≤ countLit b [229])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (229) <;> decide
theorem meaning230 (b : Nat → Bool) : literal (valuationOf b) (230) = decide (1 ≤ countLit b [230]) := by
  change literal b (230) = decide (1 ≤ countLit b [230])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (230) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
theorem meaning232 (b : Nat → Bool) : literal (valuationOf b) (232) = decide (1 ≤ countLit b [232]) := by
  change literal b (232) = decide (1 ≤ countLit b [232])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (232) <;> decide
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) 235 = decide (1 ≤ count235 b) := rfl
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) 237 = decide (1 ≤ count237 b) := rfl
theorem meaning239 (b : Nat → Bool) : literal (valuationOf b) 239 = decide (1 ≤ count239 b) := rfl
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) 240 = decide (2 ≤ count239 b) := rfl
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) 241 = decide (1 ≤ count241 b) := rfl
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) 243 = decide (1 ≤ count243 b) := rfl
theorem meaning244 (b : Nat → Bool) : literal (valuationOf b) 244 = decide (2 ≤ count243 b) := rfl
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning246 (b : Nat → Bool) : literal (valuationOf b) 246 = decide (2 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning258 (b : Nat → Bool) : literal (valuationOf b) 258 = decide (2 ≤ count257 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning260 (b : Nat → Bool) : literal (valuationOf b) 260 = decide (2 ≤ count259 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning278 (b : Nat → Bool) : literal (valuationOf b) 278 = decide (2 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning286 (b : Nat → Bool) : literal (valuationOf b) 286 = decide (2 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning288 (b : Nat → Bool) : literal (valuationOf b) 288 = decide (2 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning304 (b : Nat → Bool) : literal (valuationOf b) 304 = decide (2 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning306 (b : Nat → Bool) : literal (valuationOf b) 306 = decide (2 ≤ count305 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning316 (b : Nat → Bool) : literal (valuationOf b) 316 = decide (2 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning324 (b : Nat → Bool) : literal (valuationOf b) 324 = decide (2 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning326 (b : Nat → Bool) : literal (valuationOf b) 326 = decide (2 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning346 (b : Nat → Bool) : literal (valuationOf b) 346 = decide (2 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning348 (b : Nat → Bool) : literal (valuationOf b) 348 = decide (2 ≤ count347 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning354 (b : Nat → Bool) : literal (valuationOf b) 354 = decide (2 ≤ count353 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning367 (b : Nat → Bool) : literal (valuationOf b) 367 = decide (1 ≤ count367 b) := rfl
theorem meaning368 (b : Nat → Bool) : literal (valuationOf b) 368 = decide (2 ≤ count367 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning370 (b : Nat → Bool) : literal (valuationOf b) 370 = decide (2 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning372 (b : Nat → Bool) : literal (valuationOf b) 372 = decide (2 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning374 (b : Nat → Bool) : literal (valuationOf b) 374 = decide (2 ≤ count373 b) := rfl
theorem meaning375 (b : Nat → Bool) : literal (valuationOf b) 375 = decide (1 ≤ count375 b) := rfl
theorem meaning376 (b : Nat → Bool) : literal (valuationOf b) 376 = decide (2 ≤ count375 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning378 (b : Nat → Bool) : literal (valuationOf b) 378 = decide (2 ≤ count377 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning392 (b : Nat → Bool) : literal (valuationOf b) 392 = decide (2 ≤ count391 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning397 (b : Nat → Bool) : literal (valuationOf b) 397 = decide (1 ≤ count397 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning400 (b : Nat → Bool) : literal (valuationOf b) 400 = decide (2 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning402 (b : Nat → Bool) : literal (valuationOf b) 402 = decide (2 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning414 (b : Nat → Bool) : literal (valuationOf b) 414 = decide (2 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning422 (b : Nat → Bool) : literal (valuationOf b) 422 = decide (2 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning426 (b : Nat → Bool) : literal (valuationOf b) 426 = decide (2 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning428 (b : Nat → Bool) : literal (valuationOf b) 428 = decide (2 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning430 (b : Nat → Bool) : literal (valuationOf b) 430 = decide (2 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning460 (b : Nat → Bool) : literal (valuationOf b) 460 = decide (2 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning462 (b : Nat → Bool) : literal (valuationOf b) 462 = decide (2 ≤ count461 b) := rfl
theorem meaning464 (b : Nat → Bool) : literal (valuationOf b) 464 = decide (2 ≤ count463 b) := rfl
theorem meaning1411 (b : Nat → Bool) : literal (valuationOf b) 1411 = decide (1 ≤ count1411 b) := rfl
theorem meaning1412 (b : Nat → Bool) : literal (valuationOf b) 1412 = decide (2 ≤ count1411 b) := rfl
theorem meaning1413 (b : Nat → Bool) : literal (valuationOf b) 1413 = decide (1 ≤ count1413 b) := rfl
theorem meaning1414 (b : Nat → Bool) : literal (valuationOf b) 1414 = decide (2 ≤ count1413 b) := rfl
theorem meaning1415 (b : Nat → Bool) : literal (valuationOf b) 1415 = decide (3 ≤ count1413 b) := rfl
theorem meaning1416 (b : Nat → Bool) : literal (valuationOf b) 1416 = decide (1 ≤ count1416 b) := rfl
theorem meaning1417 (b : Nat → Bool) : literal (valuationOf b) 1417 = decide (2 ≤ count1416 b) := rfl
theorem meaning1418 (b : Nat → Bool) : literal (valuationOf b) 1418 = decide (1 ≤ count1418 b) := rfl
theorem meaning1419 (b : Nat → Bool) : literal (valuationOf b) 1419 = decide (2 ≤ count1418 b) := rfl
theorem meaning1420 (b : Nat → Bool) : literal (valuationOf b) 1420 = decide (1 ≤ count1420 b) := rfl
theorem meaning1421 (b : Nat → Bool) : literal (valuationOf b) 1421 = decide (2 ≤ count1420 b) := rfl
theorem meaning1422 (b : Nat → Bool) : literal (valuationOf b) 1422 = decide (3 ≤ count1420 b) := rfl
theorem meaning1423 (b : Nat → Bool) : literal (valuationOf b) 1423 = decide (4 ≤ count1420 b) := rfl
theorem meaning1424 (b : Nat → Bool) : literal (valuationOf b) 1424 = decide (1 ≤ count1424 b) := rfl
theorem meaning1425 (b : Nat → Bool) : literal (valuationOf b) 1425 = decide (2 ≤ count1424 b) := rfl
theorem meaning1426 (b : Nat → Bool) : literal (valuationOf b) 1426 = decide (3 ≤ count1424 b) := rfl
theorem meaning1427 (b : Nat → Bool) : literal (valuationOf b) 1427 = decide (4 ≤ count1424 b) := rfl
theorem meaning1428 (b : Nat → Bool) : literal (valuationOf b) 1428 = decide (5 ≤ count1424 b) := rfl
theorem meaning1431 (b : Nat → Bool) : literal (valuationOf b) 1431 = decide (1 ≤ count1431 b) := rfl
theorem meaning1432 (b : Nat → Bool) : literal (valuationOf b) 1432 = decide (2 ≤ count1431 b) := rfl
theorem meaning1433 (b : Nat → Bool) : literal (valuationOf b) 1433 = decide (1 ≤ count1433 b) := rfl
theorem meaning1434 (b : Nat → Bool) : literal (valuationOf b) 1434 = decide (2 ≤ count1433 b) := rfl
theorem meaning1435 (b : Nat → Bool) : literal (valuationOf b) 1435 = decide (3 ≤ count1433 b) := rfl
theorem meaning1436 (b : Nat → Bool) : literal (valuationOf b) 1436 = decide (1 ≤ count1436 b) := rfl
theorem meaning1437 (b : Nat → Bool) : literal (valuationOf b) 1437 = decide (2 ≤ count1436 b) := rfl
theorem meaning1438 (b : Nat → Bool) : literal (valuationOf b) 1438 = decide (1 ≤ count1438 b) := rfl
theorem meaning1439 (b : Nat → Bool) : literal (valuationOf b) 1439 = decide (2 ≤ count1438 b) := rfl
theorem meaning1440 (b : Nat → Bool) : literal (valuationOf b) 1440 = decide (1 ≤ count1440 b) := rfl
theorem meaning1441 (b : Nat → Bool) : literal (valuationOf b) 1441 = decide (2 ≤ count1440 b) := rfl
theorem meaning1442 (b : Nat → Bool) : literal (valuationOf b) 1442 = decide (3 ≤ count1440 b) := rfl
theorem meaning1443 (b : Nat → Bool) : literal (valuationOf b) 1443 = decide (4 ≤ count1440 b) := rfl
theorem meaning1444 (b : Nat → Bool) : literal (valuationOf b) 1444 = decide (1 ≤ count1444 b) := rfl
theorem meaning1445 (b : Nat → Bool) : literal (valuationOf b) 1445 = decide (2 ≤ count1444 b) := rfl
theorem meaning1446 (b : Nat → Bool) : literal (valuationOf b) 1446 = decide (3 ≤ count1444 b) := rfl
theorem meaning1447 (b : Nat → Bool) : literal (valuationOf b) 1447 = decide (4 ≤ count1444 b) := rfl
theorem meaning1448 (b : Nat → Bool) : literal (valuationOf b) 1448 = decide (5 ≤ count1444 b) := rfl
theorem meaning1449 (b : Nat → Bool) : literal (valuationOf b) 1449 = decide (6 ≤ count1444 b) := rfl
theorem meaning1451 (b : Nat → Bool) : literal (valuationOf b) 1451 = decide (1 ≤ count1451 b) := rfl
theorem meaning1452 (b : Nat → Bool) : literal (valuationOf b) 1452 = decide (2 ≤ count1451 b) := rfl
theorem meaning1453 (b : Nat → Bool) : literal (valuationOf b) 1453 = decide (3 ≤ count1451 b) := rfl
theorem meaning1454 (b : Nat → Bool) : literal (valuationOf b) 1454 = decide (4 ≤ count1451 b) := rfl
theorem meaning1455 (b : Nat → Bool) : literal (valuationOf b) 1455 = decide (5 ≤ count1451 b) := rfl
theorem meaning1456 (b : Nat → Bool) : literal (valuationOf b) 1456 = decide (6 ≤ count1451 b) := rfl
theorem meaning1457 (b : Nat → Bool) : literal (valuationOf b) 1457 = decide (7 ≤ count1451 b) := rfl
theorem meaning1458 (b : Nat → Bool) : literal (valuationOf b) 1458 = decide (8 ≤ count1451 b) := rfl
theorem meaning1459 (b : Nat → Bool) : literal (valuationOf b) 1459 = decide (9 ≤ count1451 b) := rfl
theorem meaning1460 (b : Nat → Bool) : literal (valuationOf b) 1460 = decide (10 ≤ count1451 b) := rfl
theorem meaning1465 (b : Nat → Bool) : literal (valuationOf b) 1465 = decide (1 ≤ count1465 b) := rfl
theorem meaning1466 (b : Nat → Bool) : literal (valuationOf b) 1466 = decide (2 ≤ count1465 b) := rfl
theorem meaning1467 (b : Nat → Bool) : literal (valuationOf b) 1467 = decide (1 ≤ count1467 b) := rfl
theorem meaning1468 (b : Nat → Bool) : literal (valuationOf b) 1468 = decide (2 ≤ count1467 b) := rfl
theorem meaning1469 (b : Nat → Bool) : literal (valuationOf b) 1469 = decide (3 ≤ count1467 b) := rfl
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
theorem meaning1485 (b : Nat → Bool) : literal (valuationOf b) 1485 = decide (1 ≤ count1485 b) := rfl
theorem meaning1486 (b : Nat → Bool) : literal (valuationOf b) 1486 = decide (2 ≤ count1485 b) := rfl
theorem meaning1487 (b : Nat → Bool) : literal (valuationOf b) 1487 = decide (1 ≤ count1487 b) := rfl
theorem meaning1488 (b : Nat → Bool) : literal (valuationOf b) 1488 = decide (2 ≤ count1487 b) := rfl
theorem meaning1489 (b : Nat → Bool) : literal (valuationOf b) 1489 = decide (1 ≤ count1489 b) := rfl
theorem meaning1490 (b : Nat → Bool) : literal (valuationOf b) 1490 = decide (2 ≤ count1489 b) := rfl
theorem meaning1491 (b : Nat → Bool) : literal (valuationOf b) 1491 = decide (3 ≤ count1489 b) := rfl
theorem meaning1492 (b : Nat → Bool) : literal (valuationOf b) 1492 = decide (4 ≤ count1489 b) := rfl
theorem meaning1493 (b : Nat → Bool) : literal (valuationOf b) 1493 = decide (1 ≤ count1493 b) := rfl
theorem meaning1494 (b : Nat → Bool) : literal (valuationOf b) 1494 = decide (2 ≤ count1493 b) := rfl
theorem meaning1495 (b : Nat → Bool) : literal (valuationOf b) 1495 = decide (1 ≤ count1495 b) := rfl
theorem meaning1496 (b : Nat → Bool) : literal (valuationOf b) 1496 = decide (2 ≤ count1495 b) := rfl
theorem meaning1497 (b : Nat → Bool) : literal (valuationOf b) 1497 = decide (1 ≤ count1497 b) := rfl
theorem meaning1498 (b : Nat → Bool) : literal (valuationOf b) 1498 = decide (2 ≤ count1497 b) := rfl
theorem meaning1499 (b : Nat → Bool) : literal (valuationOf b) 1499 = decide (3 ≤ count1497 b) := rfl
theorem meaning1500 (b : Nat → Bool) : literal (valuationOf b) 1500 = decide (4 ≤ count1497 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (2 ≤ count1501 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (3 ≤ count1501 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (4 ≤ count1501 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (5 ≤ count1501 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (6 ≤ count1501 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (7 ≤ count1501 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (3 ≤ count1509 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (4 ≤ count1509 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (5 ≤ count1509 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (6 ≤ count1509 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (7 ≤ count1509 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (8 ≤ count1509 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (9 ≤ count1509 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (7 ≤ count1524 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (8 ≤ count1524 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (9 ≤ count1524 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (10 ≤ count1524 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (11 ≤ count1524 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (12 ≤ count1524 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (13 ≤ count1524 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (1 ≤ count1542 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (2 ≤ count1542 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (1 ≤ count1544 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (2 ≤ count1544 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (3 ≤ count1544 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (1 ≤ count1547 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (2 ≤ count1547 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (1 ≤ count1549 b) := rfl
theorem meaning1550 (b : Nat → Bool) : literal (valuationOf b) 1550 = decide (2 ≤ count1549 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1552 (b : Nat → Bool) : literal (valuationOf b) 1552 = decide (2 ≤ count1551 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (3 ≤ count1551 b) := rfl
theorem meaning1554 (b : Nat → Bool) : literal (valuationOf b) 1554 = decide (4 ≤ count1551 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (1 ≤ count1555 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (2 ≤ count1555 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (3 ≤ count1555 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (4 ≤ count1555 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (5 ≤ count1555 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (6 ≤ count1555 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (1 ≤ count1562 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (2 ≤ count1562 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1567 (b : Nat → Bool) : literal (valuationOf b) 1567 = decide (1 ≤ count1567 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (2 ≤ count1567 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (1 ≤ count1569 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (2 ≤ count1569 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (1 ≤ count1571 b) := rfl
theorem meaning1572 (b : Nat → Bool) : literal (valuationOf b) 1572 = decide (2 ≤ count1571 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (3 ≤ count1571 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (1 ≤ count1575 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (2 ≤ count1575 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (3 ≤ count1575 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (2 ≤ count1582 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (3 ≤ count1582 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (4 ≤ count1582 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (5 ≤ count1582 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (6 ≤ count1582 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (7 ≤ count1582 b) := rfl
theorem meaning1596 (b : Nat → Bool) : literal (valuationOf b) 1596 = decide (1 ≤ count1596 b) := rfl
theorem meaning1597 (b : Nat → Bool) : literal (valuationOf b) 1597 = decide (2 ≤ count1596 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (1 ≤ count1598 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (2 ≤ count1598 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (3 ≤ count1598 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (1 ≤ count1601 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (2 ≤ count1601 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (1 ≤ count1603 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (2 ≤ count1603 b) := rfl
theorem meaning1605 (b : Nat → Bool) : literal (valuationOf b) 1605 = decide (1 ≤ count1605 b) := rfl
theorem meaning1606 (b : Nat → Bool) : literal (valuationOf b) 1606 = decide (2 ≤ count1605 b) := rfl
theorem meaning1607 (b : Nat → Bool) : literal (valuationOf b) 1607 = decide (3 ≤ count1605 b) := rfl
theorem meaning1609 (b : Nat → Bool) : literal (valuationOf b) 1609 = decide (1 ≤ count1609 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (2 ≤ count1609 b) := rfl
theorem meaning1611 (b : Nat → Bool) : literal (valuationOf b) 1611 = decide (3 ≤ count1609 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (4 ≤ count1609 b) := rfl
theorem meaning1613 (b : Nat → Bool) : literal (valuationOf b) 1613 = decide (5 ≤ count1609 b) := rfl
theorem meaning1616 (b : Nat → Bool) : literal (valuationOf b) 1616 = decide (1 ≤ count1616 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (1 ≤ count1620 b) := rfl
theorem meaning1624 (b : Nat → Bool) : literal (valuationOf b) 1624 = decide (1 ≤ count1624 b) := rfl
theorem meaning1626 (b : Nat → Bool) : literal (valuationOf b) 1626 = decide (1 ≤ count1626 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (1 ≤ count1628 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (1 ≤ count1632 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (2 ≤ count1632 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (1 ≤ count1640 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (2 ≤ count1640 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (3 ≤ count1640 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (4 ≤ count1640 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (5 ≤ count1640 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (6 ≤ count1640 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (5 ≤ count1655 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (6 ≤ count1655 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (7 ≤ count1655 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (8 ≤ count1655 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (9 ≤ count1655 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (10 ≤ count1655 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (11 ≤ count1655 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (18 ≤ count1673 b) := rfl
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
end Snake9.Regrowth.E112207
