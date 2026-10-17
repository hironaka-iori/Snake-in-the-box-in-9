import E112254Data
namespace Snake9.Regrowth.E112254
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 122 then (if i < 61 then (if i < 30 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (89 : Vertex)) else decide (InPath q (93 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (120 : Vertex)) else decide (InPath q (125 : Vertex))) else (if i < 6 then decide (InPath q (127 : Vertex)) else decide (InPath q (257 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (258 : Vertex)) else decide (InPath q (261 : Vertex))) else (if i < 10 then decide (InPath q (262 : Vertex)) else decide (InPath q (263 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (264 : Vertex)) else decide (InPath q (265 : Vertex))) else (if i < 14 then decide (InPath q (267 : Vertex)) else decide (InPath q (268 : Vertex)))))) else (if i < 22 then (if i < 18 then (if i < 16 then decide (InPath q (271 : Vertex)) else (if i < 17 then decide (InPath q (272 : Vertex)) else decide (InPath q (275 : Vertex)))) else (if i < 20 then (if i < 19 then decide (InPath q (276 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 21 then decide (InPath q (281 : Vertex)) else decide (InPath q (282 : Vertex))))) else (if i < 26 then (if i < 24 then (if i < 23 then decide (InPath q (285 : Vertex)) else decide (InPath q (287 : Vertex))) else (if i < 25 then decide (InPath q (288 : Vertex)) else decide (InPath q (290 : Vertex)))) else (if i < 28 then (if i < 27 then decide (InPath q (293 : Vertex)) else decide (InPath q (295 : Vertex))) else (if i < 29 then decide (InPath q (297 : Vertex)) else decide (InPath q (299 : Vertex))))))) else (if i < 45 then (if i < 37 then (if i < 33 then (if i < 31 then decide (InPath q (300 : Vertex)) else (if i < 32 then decide (InPath q (302 : Vertex)) else decide (InPath q (304 : Vertex)))) else (if i < 35 then (if i < 34 then decide (InPath q (305 : Vertex)) else decide (InPath q (307 : Vertex))) else (if i < 36 then decide (InPath q (308 : Vertex)) else decide (InPath q (310 : Vertex))))) else (if i < 41 then (if i < 39 then (if i < 38 then decide (InPath q (312 : Vertex)) else decide (InPath q (314 : Vertex))) else (if i < 40 then decide (InPath q (317 : Vertex)) else decide (InPath q (318 : Vertex)))) else (if i < 43 then (if i < 42 then decide (InPath q (319 : Vertex)) else decide (InPath q (320 : Vertex))) else (if i < 44 then decide (InPath q (323 : Vertex)) else decide (InPath q (324 : Vertex)))))) else (if i < 53 then (if i < 49 then (if i < 47 then (if i < 46 then decide (InPath q (327 : Vertex)) else decide (InPath q (329 : Vertex))) else (if i < 48 then decide (InPath q (333 : Vertex)) else decide (InPath q (336 : Vertex)))) else (if i < 51 then (if i < 50 then decide (InPath q (338 : Vertex)) else decide (InPath q (344 : Vertex))) else (if i < 52 then decide (InPath q (345 : Vertex)) else decide (InPath q (353 : Vertex))))) else (if i < 57 then (if i < 55 then (if i < 54 then decide (InPath q (355 : Vertex)) else decide (InPath q (356 : Vertex))) else (if i < 56 then decide (InPath q (358 : Vertex)) else decide (InPath q (360 : Vertex)))) else (if i < 59 then (if i < 58 then decide (InPath q (368 : Vertex)) else decide (InPath q (370 : Vertex))) else (if i < 60 then decide (InPath q (376 : Vertex)) else decide (InPath q (377 : Vertex)))))))) else (if i < 91 then (if i < 76 then (if i < 68 then (if i < 64 then (if i < 62 then decide (InPath q (378 : Vertex)) else (if i < 63 then decide (InPath q (379 : Vertex)) else decide (InPath q (380 : Vertex)))) else (if i < 66 then (if i < 65 then decide (InPath q (384 : Vertex)) else decide (InPath q (385 : Vertex))) else (if i < 67 then decide (InPath q (386 : Vertex)) else decide (InPath q (388 : Vertex))))) else (if i < 72 then (if i < 70 then (if i < 69 then decide (InPath q (390 : Vertex)) else decide (InPath q (391 : Vertex))) else (if i < 71 then decide (InPath q (392 : Vertex)) else decide (InPath q (393 : Vertex)))) else (if i < 74 then (if i < 73 then decide (InPath q (396 : Vertex)) else decide (InPath q (399 : Vertex))) else (if i < 75 then decide (InPath q (402 : Vertex)) else decide (InPath q (404 : Vertex)))))) else (if i < 83 then (if i < 79 then (if i < 77 then decide (InPath q (407 : Vertex)) else (if i < 78 then decide (InPath q (409 : Vertex)) else decide (InPath q (410 : Vertex)))) else (if i < 81 then (if i < 80 then decide (InPath q (412 : Vertex)) else decide (InPath q (413 : Vertex))) else (if i < 82 then decide (InPath q (415 : Vertex)) else decide (InPath q (416 : Vertex))))) else (if i < 87 then (if i < 85 then (if i < 84 then decide (InPath q (419 : Vertex)) else decide (InPath q (420 : Vertex))) else (if i < 86 then decide (InPath q (423 : Vertex)) else decide (InPath q (425 : Vertex)))) else (if i < 89 then (if i < 88 then decide (InPath q (426 : Vertex)) else decide (InPath q (427 : Vertex))) else (if i < 90 then decide (InPath q (429 : Vertex)) else decide (InPath q (430 : Vertex))))))) else (if i < 106 then (if i < 98 then (if i < 94 then (if i < 92 then decide (InPath q (432 : Vertex)) else (if i < 93 then decide (InPath q (433 : Vertex)) else decide (InPath q (435 : Vertex)))) else (if i < 96 then (if i < 95 then decide (InPath q (436 : Vertex)) else decide (InPath q (437 : Vertex))) else (if i < 97 then decide (InPath q (438 : Vertex)) else decide (InPath q (440 : Vertex))))) else (if i < 102 then (if i < 100 then (if i < 99 then decide (InPath q (442 : Vertex)) else decide (InPath q (443 : Vertex))) else (if i < 101 then decide (InPath q (445 : Vertex)) else decide (InPath q (446 : Vertex)))) else (if i < 104 then (if i < 103 then decide (InPath q (448 : Vertex)) else decide (InPath q (454 : Vertex))) else (if i < 105 then decide (InPath q (455 : Vertex)) else decide (InPath q (460 : Vertex)))))) else (if i < 114 then (if i < 110 then (if i < 108 then (if i < 107 then decide (InPath q (461 : Vertex)) else decide (InPath q (470 : Vertex))) else (if i < 109 then decide (InPath q (472 : Vertex)) else decide (InPath q (476 : Vertex)))) else (if i < 112 then (if i < 111 then decide (InPath q (481 : Vertex)) else decide (InPath q (482 : Vertex))) else (if i < 113 then decide (InPath q (485 : Vertex)) else decide (InPath q (486 : Vertex))))) else (if i < 118 then (if i < 116 then (if i < 115 then decide (InPath q (488 : Vertex)) else decide (InPath q (489 : Vertex))) else (if i < 117 then decide (InPath q (492 : Vertex)) else decide (InPath q (496 : Vertex)))) else (if i < 120 then (if i < 119 then decide (InPath q (498 : Vertex)) else decide (InPath q (500 : Vertex))) else (if i < 121 then decide (InPath q (504 : Vertex)) else decide (InPath q (506 : Vertex))))))))) else (if i < 183 then (if i < 152 then (if i < 137 then (if i < 129 then (if i < 125 then (if i < 123 then decide (InPath q (508 : Vertex)) else (if i < 124 then decide (BallClauseLogic.Endpoint q (89 : Vertex)) else decide (BallClauseLogic.Endpoint q (93 : Vertex)))) else (if i < 127 then (if i < 126 then decide (BallClauseLogic.Endpoint q (120 : Vertex)) else decide (BallClauseLogic.Endpoint q (125 : Vertex))) else (if i < 128 then decide (BallClauseLogic.Endpoint q (127 : Vertex)) else decide (BallClauseLogic.Endpoint q (257 : Vertex))))) else (if i < 133 then (if i < 131 then (if i < 130 then decide (BallClauseLogic.Endpoint q (258 : Vertex)) else decide (BallClauseLogic.Endpoint q (261 : Vertex))) else (if i < 132 then decide (BallClauseLogic.Endpoint q (262 : Vertex)) else decide (BallClauseLogic.Endpoint q (263 : Vertex)))) else (if i < 135 then (if i < 134 then decide (BallClauseLogic.Endpoint q (264 : Vertex)) else decide (BallClauseLogic.Endpoint q (265 : Vertex))) else (if i < 136 then decide (BallClauseLogic.Endpoint q (267 : Vertex)) else decide (BallClauseLogic.Endpoint q (268 : Vertex)))))) else (if i < 144 then (if i < 140 then (if i < 138 then decide (BallClauseLogic.Endpoint q (271 : Vertex)) else (if i < 139 then decide (BallClauseLogic.Endpoint q (272 : Vertex)) else decide (BallClauseLogic.Endpoint q (275 : Vertex)))) else (if i < 142 then (if i < 141 then decide (BallClauseLogic.Endpoint q (276 : Vertex)) else decide (BallClauseLogic.Endpoint q (279 : Vertex))) else (if i < 143 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex))))) else (if i < 148 then (if i < 146 then (if i < 145 then decide (BallClauseLogic.Endpoint q (285 : Vertex)) else decide (BallClauseLogic.Endpoint q (287 : Vertex))) else (if i < 147 then decide (BallClauseLogic.Endpoint q (288 : Vertex)) else decide (BallClauseLogic.Endpoint q (290 : Vertex)))) else (if i < 150 then (if i < 149 then decide (BallClauseLogic.Endpoint q (293 : Vertex)) else decide (BallClauseLogic.Endpoint q (295 : Vertex))) else (if i < 151 then decide (BallClauseLogic.Endpoint q (297 : Vertex)) else decide (BallClauseLogic.Endpoint q (299 : Vertex))))))) else (if i < 167 then (if i < 159 then (if i < 155 then (if i < 153 then decide (BallClauseLogic.Endpoint q (300 : Vertex)) else (if i < 154 then decide (BallClauseLogic.Endpoint q (302 : Vertex)) else decide (BallClauseLogic.Endpoint q (304 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (305 : Vertex)) else decide (BallClauseLogic.Endpoint q (307 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (308 : Vertex)) else decide (BallClauseLogic.Endpoint q (310 : Vertex))))) else (if i < 163 then (if i < 161 then (if i < 160 then decide (BallClauseLogic.Endpoint q (312 : Vertex)) else decide (BallClauseLogic.Endpoint q (314 : Vertex))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (317 : Vertex)) else decide (BallClauseLogic.Endpoint q (318 : Vertex)))) else (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (319 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (323 : Vertex)) else decide (BallClauseLogic.Endpoint q (324 : Vertex)))))) else (if i < 175 then (if i < 171 then (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (327 : Vertex)) else decide (BallClauseLogic.Endpoint q (329 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (336 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (338 : Vertex)) else decide (BallClauseLogic.Endpoint q (344 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (345 : Vertex)) else decide (BallClauseLogic.Endpoint q (353 : Vertex))))) else (if i < 179 then (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (355 : Vertex)) else decide (BallClauseLogic.Endpoint q (356 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (358 : Vertex)) else decide (BallClauseLogic.Endpoint q (360 : Vertex)))) else (if i < 181 then (if i < 180 then decide (BallClauseLogic.Endpoint q (368 : Vertex)) else decide (BallClauseLogic.Endpoint q (370 : Vertex))) else (if i < 182 then decide (BallClauseLogic.Endpoint q (376 : Vertex)) else decide (BallClauseLogic.Endpoint q (377 : Vertex)))))))) else (if i < 214 then (if i < 198 then (if i < 190 then (if i < 186 then (if i < 184 then decide (BallClauseLogic.Endpoint q (378 : Vertex)) else (if i < 185 then decide (BallClauseLogic.Endpoint q (379 : Vertex)) else decide (BallClauseLogic.Endpoint q (380 : Vertex)))) else (if i < 188 then (if i < 187 then decide (BallClauseLogic.Endpoint q (384 : Vertex)) else decide (BallClauseLogic.Endpoint q (385 : Vertex))) else (if i < 189 then decide (BallClauseLogic.Endpoint q (386 : Vertex)) else decide (BallClauseLogic.Endpoint q (388 : Vertex))))) else (if i < 194 then (if i < 192 then (if i < 191 then decide (BallClauseLogic.Endpoint q (390 : Vertex)) else decide (BallClauseLogic.Endpoint q (391 : Vertex))) else (if i < 193 then decide (BallClauseLogic.Endpoint q (392 : Vertex)) else decide (BallClauseLogic.Endpoint q (393 : Vertex)))) else (if i < 196 then (if i < 195 then decide (BallClauseLogic.Endpoint q (396 : Vertex)) else decide (BallClauseLogic.Endpoint q (399 : Vertex))) else (if i < 197 then decide (BallClauseLogic.Endpoint q (402 : Vertex)) else decide (BallClauseLogic.Endpoint q (404 : Vertex)))))) else (if i < 206 then (if i < 202 then (if i < 200 then (if i < 199 then decide (BallClauseLogic.Endpoint q (407 : Vertex)) else decide (BallClauseLogic.Endpoint q (409 : Vertex))) else (if i < 201 then decide (BallClauseLogic.Endpoint q (410 : Vertex)) else decide (BallClauseLogic.Endpoint q (412 : Vertex)))) else (if i < 204 then (if i < 203 then decide (BallClauseLogic.Endpoint q (413 : Vertex)) else decide (BallClauseLogic.Endpoint q (415 : Vertex))) else (if i < 205 then decide (BallClauseLogic.Endpoint q (416 : Vertex)) else decide (BallClauseLogic.Endpoint q (419 : Vertex))))) else (if i < 210 then (if i < 208 then (if i < 207 then decide (BallClauseLogic.Endpoint q (420 : Vertex)) else decide (BallClauseLogic.Endpoint q (423 : Vertex))) else (if i < 209 then decide (BallClauseLogic.Endpoint q (425 : Vertex)) else decide (BallClauseLogic.Endpoint q (426 : Vertex)))) else (if i < 212 then (if i < 211 then decide (BallClauseLogic.Endpoint q (427 : Vertex)) else decide (BallClauseLogic.Endpoint q (429 : Vertex))) else (if i < 213 then decide (BallClauseLogic.Endpoint q (430 : Vertex)) else decide (BallClauseLogic.Endpoint q (432 : Vertex))))))) else (if i < 229 then (if i < 221 then (if i < 217 then (if i < 215 then decide (BallClauseLogic.Endpoint q (433 : Vertex)) else (if i < 216 then decide (BallClauseLogic.Endpoint q (435 : Vertex)) else decide (BallClauseLogic.Endpoint q (436 : Vertex)))) else (if i < 219 then (if i < 218 then decide (BallClauseLogic.Endpoint q (437 : Vertex)) else decide (BallClauseLogic.Endpoint q (438 : Vertex))) else (if i < 220 then decide (BallClauseLogic.Endpoint q (440 : Vertex)) else decide (BallClauseLogic.Endpoint q (442 : Vertex))))) else (if i < 225 then (if i < 223 then (if i < 222 then decide (BallClauseLogic.Endpoint q (443 : Vertex)) else decide (BallClauseLogic.Endpoint q (445 : Vertex))) else (if i < 224 then decide (BallClauseLogic.Endpoint q (446 : Vertex)) else decide (BallClauseLogic.Endpoint q (448 : Vertex)))) else (if i < 227 then (if i < 226 then decide (BallClauseLogic.Endpoint q (454 : Vertex)) else decide (BallClauseLogic.Endpoint q (455 : Vertex))) else (if i < 228 then decide (BallClauseLogic.Endpoint q (460 : Vertex)) else decide (BallClauseLogic.Endpoint q (461 : Vertex)))))) else (if i < 237 then (if i < 233 then (if i < 231 then (if i < 230 then decide (BallClauseLogic.Endpoint q (470 : Vertex)) else decide (BallClauseLogic.Endpoint q (472 : Vertex))) else (if i < 232 then decide (BallClauseLogic.Endpoint q (476 : Vertex)) else decide (BallClauseLogic.Endpoint q (481 : Vertex)))) else (if i < 235 then (if i < 234 then decide (BallClauseLogic.Endpoint q (482 : Vertex)) else decide (BallClauseLogic.Endpoint q (485 : Vertex))) else (if i < 236 then decide (BallClauseLogic.Endpoint q (486 : Vertex)) else decide (BallClauseLogic.Endpoint q (488 : Vertex))))) else (if i < 241 then (if i < 239 then (if i < 238 then decide (BallClauseLogic.Endpoint q (489 : Vertex)) else decide (BallClauseLogic.Endpoint q (492 : Vertex))) else (if i < 240 then decide (BallClauseLogic.Endpoint q (496 : Vertex)) else decide (BallClauseLogic.Endpoint q (498 : Vertex)))) else (if i < 243 then (if i < 242 then decide (BallClauseLogic.Endpoint q (500 : Vertex)) else decide (BallClauseLogic.Endpoint q (504 : Vertex))) else (if i < 244 then decide (BallClauseLogic.Endpoint q (506 : Vertex)) else decide (BallClauseLogic.Endpoint q (508 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count245 (b : Nat → Bool) : Nat := countLit b [124, 125]
def count247 (b : Nat → Bool) : Nat := countLit b [123, 124, 125]
def count249 (b : Nat → Bool) : Nat := countLit b [126, 127]
def count251 (b : Nat → Bool) : Nat := countLit b [128, 129]
def count253 (b : Nat → Bool) : Nat := countLit b [126, 127, 128, 129]
def count255 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129]
def count257 (b : Nat → Bool) : Nat := countLit b [130, 131]
def count259 (b : Nat → Bool) : Nat := countLit b [132, 133]
def count261 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133]
def count263 (b : Nat → Bool) : Nat := countLit b [134, 135]
def count265 (b : Nat → Bool) : Nat := countLit b [136, 137]
def count267 (b : Nat → Bool) : Nat := countLit b [134, 135, 136, 137]
def count269 (b : Nat → Bool) : Nat := countLit b [130, 131, 132, 133, 134, 135, 136, 137]
def count271 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [138, 139, 140]
def count277 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count281 (b : Nat → Bool) : Nat := countLit b [141, 142, 143, 144]
def count283 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count289 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count295 (b : Nat → Bool) : Nat := countLit b [149, 150, 151, 152]
def count297 (b : Nat → Bool) : Nat := countLit b [145, 146, 147, 148, 149, 150, 151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count301 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152]
def count303 (b : Nat → Bool) : Nat := countLit b [154, 155]
def count305 (b : Nat → Bool) : Nat := countLit b [153, 154, 155]
def count307 (b : Nat → Bool) : Nat := countLit b [156, 157]
def count309 (b : Nat → Bool) : Nat := countLit b [158, 159]
def count311 (b : Nat → Bool) : Nat := countLit b [156, 157, 158, 159]
def count313 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159]
def count315 (b : Nat → Bool) : Nat := countLit b [160, 161]
def count317 (b : Nat → Bool) : Nat := countLit b [162, 163]
def count319 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163]
def count321 (b : Nat → Bool) : Nat := countLit b [164, 165]
def count323 (b : Nat → Bool) : Nat := countLit b [166, 167]
def count325 (b : Nat → Bool) : Nat := countLit b [164, 165, 166, 167]
def count327 (b : Nat → Bool) : Nat := countLit b [160, 161, 162, 163, 164, 165, 166, 167]
def count329 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167]
def count331 (b : Nat → Bool) : Nat := countLit b [170, 171]
def count333 (b : Nat → Bool) : Nat := countLit b [168, 170, 171]
def count335 (b : Nat → Bool) : Nat := countLit b [172, 173]
def count337 (b : Nat → Bool) : Nat := countLit b [174, 175]
def count339 (b : Nat → Bool) : Nat := countLit b [172, 173, 174, 175]
def count341 (b : Nat → Bool) : Nat := countLit b [168, 170, 171, 172, 173, 174, 175]
def count343 (b : Nat → Bool) : Nat := countLit b [176, 177]
def count345 (b : Nat → Bool) : Nat := countLit b [178, 179]
def count347 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179]
def count349 (b : Nat → Bool) : Nat := countLit b [180, 181]
def count351 (b : Nat → Bool) : Nat := countLit b [182, 183]
def count353 (b : Nat → Bool) : Nat := countLit b [180, 181, 182, 183]
def count355 (b : Nat → Bool) : Nat := countLit b [176, 177, 178, 179, 180, 181, 182, 183]
def count357 (b : Nat → Bool) : Nat := countLit b [168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]
def count359 (b : Nat → Bool) : Nat := countLit b [153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]
def count361 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183]
def count363 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [184, 185, 186]
def count367 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count369 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [191, 192]
def count377 (b : Nat → Bool) : Nat := countLit b [193, 194]
def count379 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194]
def count381 (b : Nat → Bool) : Nat := countLit b [195, 196]
def count383 (b : Nat → Bool) : Nat := countLit b [197, 198]
def count385 (b : Nat → Bool) : Nat := countLit b [195, 196, 197, 198]
def count387 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198]
def count389 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198]
def count391 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count393 (b : Nat → Bool) : Nat := countLit b [199, 200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count397 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count399 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count405 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count407 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209]
def count409 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count411 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count413 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213]
def count415 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209, 210, 211, 212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]
def count419 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213]
def count421 (b : Nat → Bool) : Nat := countLit b [215, 216]
def count423 (b : Nat → Bool) : Nat := countLit b [214, 215, 216]
def count425 (b : Nat → Bool) : Nat := countLit b [217, 218]
def count427 (b : Nat → Bool) : Nat := countLit b [219, 220]
def count429 (b : Nat → Bool) : Nat := countLit b [217, 218, 219, 220]
def count431 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220]
def count433 (b : Nat → Bool) : Nat := countLit b [221, 222]
def count435 (b : Nat → Bool) : Nat := countLit b [223, 224]
def count437 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224]
def count439 (b : Nat → Bool) : Nat := countLit b [225, 226]
def count441 (b : Nat → Bool) : Nat := countLit b [227, 228]
def count443 (b : Nat → Bool) : Nat := countLit b [225, 226, 227, 228]
def count445 (b : Nat → Bool) : Nat := countLit b [221, 222, 223, 224, 225, 226, 227, 228]
def count447 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228]
def count449 (b : Nat → Bool) : Nat := countLit b [229, 230]
def count451 (b : Nat → Bool) : Nat := countLit b [231, 232]
def count453 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232]
def count455 (b : Nat → Bool) : Nat := countLit b [233, 234]
def count457 (b : Nat → Bool) : Nat := countLit b [235, 236]
def count459 (b : Nat → Bool) : Nat := countLit b [233, 234, 235, 236]
def count461 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232, 233, 234, 235, 236]
def count463 (b : Nat → Bool) : Nat := countLit b [237, 238]
def count465 (b : Nat → Bool) : Nat := countLit b [239, 240]
def count467 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240]
def count469 (b : Nat → Bool) : Nat := countLit b [241, 242]
def count471 (b : Nat → Bool) : Nat := countLit b [243, 244]
def count473 (b : Nat → Bool) : Nat := countLit b [241, 242, 243, 244]
def count475 (b : Nat → Bool) : Nat := countLit b [237, 238, 239, 240, 241, 242, 243, 244]
def count477 (b : Nat → Bool) : Nat := countLit b [229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count479 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count481 (b : Nat → Bool) : Nat := countLit b [184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count483 (b : Nat → Bool) : Nat := countLit b [123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244]
def count485 (b : Nat → Bool) : Nat := countLit b [1, 3]
def count487 (b : Nat → Bool) : Nat := countLit b [4, 6]
def count489 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6]
def count493 (b : Nat → Bool) : Nat := countLit b [7, 10]
def count495 (b : Nat → Bool) : Nat := countLit b [11, 13]
def count497 (b : Nat → Bool) : Nat := countLit b [7, 10, 11, 13]
def count501 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 10, 11, 13]
def count509 (b : Nat → Bool) : Nat := countLit b [16, 17]
def count511 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count513 (b : Nat → Bool) : Nat := countLit b [16, 17, 20, 21]
def count517 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count519 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count521 (b : Nat → Bool) : Nat := countLit b [23, 24, 26, 28]
def count525 (b : Nat → Bool) : Nat := countLit b [16, 17, 20, 21, 23, 24, 26, 28]
def count533 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 10, 11, 13, 16, 17, 20, 21, 23, 24, 26, 28]
def count549 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count551 (b : Nat → Bool) : Nat := countLit b [35, 37]
def count553 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 37]
def count557 (b : Nat → Bool) : Nat := countLit b [39, 40]
def count559 (b : Nat → Bool) : Nat := countLit b [42, 43]
def count561 (b : Nat → Bool) : Nat := countLit b [39, 40, 42, 43]
def count565 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 37, 39, 40, 42, 43]
def count573 (b : Nat → Bool) : Nat := countLit b [46, 49]
def count575 (b : Nat → Bool) : Nat := countLit b [50, 52]
def count577 (b : Nat → Bool) : Nat := countLit b [46, 49, 50, 52]
def count581 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count583 (b : Nat → Bool) : Nat := countLit b [57, 60]
def count585 (b : Nat → Bool) : Nat := countLit b [54, 56, 57, 60]
def count589 (b : Nat → Bool) : Nat := countLit b [46, 49, 50, 52, 54, 56, 57, 60]
def count597 (b : Nat → Bool) : Nat := countLit b [30, 33, 35, 37, 39, 40, 42, 43, 46, 49, 50, 52, 54, 56, 57, 60]
def count613 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 10, 11, 13, 16, 17, 20, 21, 23, 24, 26, 28, 30, 33, 35, 37, 39, 40, 42, 43, 46, 49, 50, 52, 54, 56, 57, 60]
def count645 (b : Nat → Bool) : Nat := countLit b [61, 63]
def count647 (b : Nat → Bool) : Nat := countLit b [64, 68]
def count649 (b : Nat → Bool) : Nat := countLit b [61, 63, 64, 68]
def count653 (b : Nat → Bool) : Nat := countLit b [71, 72]
def count655 (b : Nat → Bool) : Nat := countLit b [73, 74]
def count657 (b : Nat → Bool) : Nat := countLit b [71, 72, 73, 74]
def count661 (b : Nat → Bool) : Nat := countLit b [61, 63, 64, 68, 71, 72, 73, 74]
def count669 (b : Nat → Bool) : Nat := countLit b [75, 76]
def count671 (b : Nat → Bool) : Nat := countLit b [80, 84]
def count673 (b : Nat → Bool) : Nat := countLit b [75, 76, 80, 84]
def count677 (b : Nat → Bool) : Nat := countLit b [85, 88]
def count679 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count681 (b : Nat → Bool) : Nat := countLit b [85, 88, 89, 90]
def count685 (b : Nat → Bool) : Nat := countLit b [75, 76, 80, 84, 85, 88, 89, 90]
def count693 (b : Nat → Bool) : Nat := countLit b [61, 63, 64, 68, 71, 72, 73, 74, 75, 76, 80, 84, 85, 88, 89, 90]
def count709 (b : Nat → Bool) : Nat := countLit b [91, 93]
def count711 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count713 (b : Nat → Bool) : Nat := countLit b [91, 93, 95, 96]
def count717 (b : Nat → Bool) : Nat := countLit b [98, 104]
def count719 (b : Nat → Bool) : Nat := countLit b [106, 107]
def count721 (b : Nat → Bool) : Nat := countLit b [98, 104, 106, 107]
def count725 (b : Nat → Bool) : Nat := countLit b [91, 93, 95, 96, 98, 104, 106, 107]
def count733 (b : Nat → Bool) : Nat := countLit b [109, 112]
def count735 (b : Nat → Bool) : Nat := countLit b [113, 115]
def count737 (b : Nat → Bool) : Nat := countLit b [109, 112, 113, 115]
def count741 (b : Nat → Bool) : Nat := countLit b [116, 118]
def count743 (b : Nat → Bool) : Nat := countLit b [119, 120]
def count745 (b : Nat → Bool) : Nat := countLit b [116, 118, 119, 120]
def count749 (b : Nat → Bool) : Nat := countLit b [109, 112, 113, 115, 116, 118, 119, 120]
def count757 (b : Nat → Bool) : Nat := countLit b [91, 93, 95, 96, 98, 104, 106, 107, 109, 112, 113, 115, 116, 118, 119, 120]
def count773 (b : Nat → Bool) : Nat := countLit b [61, 63, 64, 68, 71, 72, 73, 74, 75, 76, 80, 84, 85, 88, 89, 90, 91, 93, 95, 96, 98, 104, 106, 107, 109, 112, 113, 115, 116, 118, 119, 120]
def count805 (b : Nat → Bool) : Nat := countLit b [1, 3, 4, 6, 7, 10, 11, 13, 16, 17, 20, 21, 23, 24, 26, 28, 30, 33, 35, 37, 39, 40, 42, 43, 46, 49, 50, 52, 54, 56, 57, 60, 61, 63, 64, 68, 71, 72, 73, 74, 75, 76, 80, 84, 85, 88, 89, 90, 91, 93, 95, 96, 98, 104, 106, 107, 109, 112, 113, 115, 116, 118, 119, 120]
def count847 (b : Nat → Bool) : Nat := countLit b [-1, -3]
def count849 (b : Nat → Bool) : Nat := countLit b [-4, -6]
def count851 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6]
def count855 (b : Nat → Bool) : Nat := countLit b [-7, -10]
def count857 (b : Nat → Bool) : Nat := countLit b [-11, -13]
def count859 (b : Nat → Bool) : Nat := countLit b [-7, -10, -11, -13]
def count863 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -10, -11, -13]
def count871 (b : Nat → Bool) : Nat := countLit b [-16, -17]
def count873 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count875 (b : Nat → Bool) : Nat := countLit b [-16, -17, -20, -21]
def count879 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count881 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count883 (b : Nat → Bool) : Nat := countLit b [-23, -24, -26, -28]
def count887 (b : Nat → Bool) : Nat := countLit b [-16, -17, -20, -21, -23, -24, -26, -28]
def count895 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -10, -11, -13, -16, -17, -20, -21, -23, -24, -26, -28]
def count911 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count913 (b : Nat → Bool) : Nat := countLit b [-35, -37]
def count915 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -37]
def count919 (b : Nat → Bool) : Nat := countLit b [-39, -40]
def count921 (b : Nat → Bool) : Nat := countLit b [-42, -43]
def count923 (b : Nat → Bool) : Nat := countLit b [-39, -40, -42, -43]
def count927 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -37, -39, -40, -42, -43]
def count935 (b : Nat → Bool) : Nat := countLit b [-46, -49]
def count937 (b : Nat → Bool) : Nat := countLit b [-50, -52]
def count939 (b : Nat → Bool) : Nat := countLit b [-46, -49, -50, -52]
def count943 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count945 (b : Nat → Bool) : Nat := countLit b [-57, -60]
def count947 (b : Nat → Bool) : Nat := countLit b [-54, -56, -57, -60]
def count951 (b : Nat → Bool) : Nat := countLit b [-46, -49, -50, -52, -54, -56, -57, -60]
def count959 (b : Nat → Bool) : Nat := countLit b [-30, -33, -35, -37, -39, -40, -42, -43, -46, -49, -50, -52, -54, -56, -57, -60]
def count975 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -10, -11, -13, -16, -17, -20, -21, -23, -24, -26, -28, -30, -33, -35, -37, -39, -40, -42, -43, -46, -49, -50, -52, -54, -56, -57, -60]
def count999 (b : Nat → Bool) : Nat := countLit b [-61, -63]
def count1001 (b : Nat → Bool) : Nat := countLit b [-64, -68]
def count1003 (b : Nat → Bool) : Nat := countLit b [-61, -63, -64, -68]
def count1007 (b : Nat → Bool) : Nat := countLit b [-71, -72]
def count1009 (b : Nat → Bool) : Nat := countLit b [-73, -74]
def count1011 (b : Nat → Bool) : Nat := countLit b [-71, -72, -73, -74]
def count1015 (b : Nat → Bool) : Nat := countLit b [-61, -63, -64, -68, -71, -72, -73, -74]
def count1023 (b : Nat → Bool) : Nat := countLit b [-75, -76]
def count1025 (b : Nat → Bool) : Nat := countLit b [-80, -84]
def count1027 (b : Nat → Bool) : Nat := countLit b [-75, -76, -80, -84]
def count1031 (b : Nat → Bool) : Nat := countLit b [-85, -88]
def count1033 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count1035 (b : Nat → Bool) : Nat := countLit b [-85, -88, -89, -90]
def count1039 (b : Nat → Bool) : Nat := countLit b [-75, -76, -80, -84, -85, -88, -89, -90]
def count1047 (b : Nat → Bool) : Nat := countLit b [-61, -63, -64, -68, -71, -72, -73, -74, -75, -76, -80, -84, -85, -88, -89, -90]
def count1063 (b : Nat → Bool) : Nat := countLit b [-91, -93]
def count1065 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count1067 (b : Nat → Bool) : Nat := countLit b [-91, -93, -95, -96]
def count1071 (b : Nat → Bool) : Nat := countLit b [-98, -104]
def count1073 (b : Nat → Bool) : Nat := countLit b [-106, -107]
def count1075 (b : Nat → Bool) : Nat := countLit b [-98, -104, -106, -107]
def count1079 (b : Nat → Bool) : Nat := countLit b [-91, -93, -95, -96, -98, -104, -106, -107]
def count1087 (b : Nat → Bool) : Nat := countLit b [-109, -112]
def count1089 (b : Nat → Bool) : Nat := countLit b [-113, -115]
def count1091 (b : Nat → Bool) : Nat := countLit b [-109, -112, -113, -115]
def count1095 (b : Nat → Bool) : Nat := countLit b [-116, -118]
def count1097 (b : Nat → Bool) : Nat := countLit b [-119, -120]
def count1099 (b : Nat → Bool) : Nat := countLit b [-116, -118, -119, -120]
def count1103 (b : Nat → Bool) : Nat := countLit b [-109, -112, -113, -115, -116, -118, -119, -120]
def count1111 (b : Nat → Bool) : Nat := countLit b [-91, -93, -95, -96, -98, -104, -106, -107, -109, -112, -113, -115, -116, -118, -119, -120]
def count1127 (b : Nat → Bool) : Nat := countLit b [-61, -63, -64, -68, -71, -72, -73, -74, -75, -76, -80, -84, -85, -88, -89, -90, -91, -93, -95, -96, -98, -104, -106, -107, -109, -112, -113, -115, -116, -118, -119, -120]
def count1151 (b : Nat → Bool) : Nat := countLit b [-1, -3, -4, -6, -7, -10, -11, -13, -16, -17, -20, -21, -23, -24, -26, -28, -30, -33, -35, -37, -39, -40, -42, -43, -46, -49, -50, -52, -54, -56, -57, -60, -61, -63, -64, -68, -71, -72, -73, -74, -75, -76, -80, -84, -85, -88, -89, -90, -91, -93, -95, -96, -98, -104, -106, -107, -109, -112, -113, -115, -116, -118, -119, -120]
def count1175 (b : Nat → Bool) : Nat := countLit b [5, 8]
def count1177 (b : Nat → Bool) : Nat := countLit b [2, 5, 8]
def count1180 (b : Nat → Bool) : Nat := countLit b [9, 12]
def count1182 (b : Nat → Bool) : Nat := countLit b [14, 15]
def count1184 (b : Nat → Bool) : Nat := countLit b [9, 12, 14, 15]
def count1188 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 12, 14, 15]
def count1195 (b : Nat → Bool) : Nat := countLit b [19, 22]
def count1197 (b : Nat → Bool) : Nat := countLit b [18, 19, 22]
def count1200 (b : Nat → Bool) : Nat := countLit b [25, 27]
def count1202 (b : Nat → Bool) : Nat := countLit b [29, 31]
def count1204 (b : Nat → Bool) : Nat := countLit b [25, 27, 29, 31]
def count1208 (b : Nat → Bool) : Nat := countLit b [18, 19, 22, 25, 27, 29, 31]
def count1215 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 12, 14, 15, 18, 19, 22, 25, 27, 29, 31]
def count1229 (b : Nat → Bool) : Nat := countLit b [34, 36]
def count1231 (b : Nat → Bool) : Nat := countLit b [32, 34, 36]
def count1234 (b : Nat → Bool) : Nat := countLit b [38, 41]
def count1236 (b : Nat → Bool) : Nat := countLit b [44, 45]
def count1238 (b : Nat → Bool) : Nat := countLit b [38, 41, 44, 45]
def count1242 (b : Nat → Bool) : Nat := countLit b [32, 34, 36, 38, 41, 44, 45]
def count1249 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count1251 (b : Nat → Bool) : Nat := countLit b [51, 53]
def count1253 (b : Nat → Bool) : Nat := countLit b [47, 48, 51, 53]
def count1257 (b : Nat → Bool) : Nat := countLit b [55, 58]
def count1259 (b : Nat → Bool) : Nat := countLit b [59, 62]
def count1261 (b : Nat → Bool) : Nat := countLit b [55, 58, 59, 62]
def count1265 (b : Nat → Bool) : Nat := countLit b [47, 48, 51, 53, 55, 58, 59, 62]
def count1273 (b : Nat → Bool) : Nat := countLit b [32, 34, 36, 38, 41, 44, 45, 47, 48, 51, 53, 55, 58, 59, 62]
def count1288 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 12, 14, 15, 18, 19, 22, 25, 27, 29, 31, 32, 34, 36, 38, 41, 44, 45, 47, 48, 51, 53, 55, 58, 59, 62]
def count1317 (b : Nat → Bool) : Nat := countLit b [66, 67]
def count1319 (b : Nat → Bool) : Nat := countLit b [65, 66, 67]
def count1322 (b : Nat → Bool) : Nat := countLit b [69, 70]
def count1324 (b : Nat → Bool) : Nat := countLit b [77, 78]
def count1326 (b : Nat → Bool) : Nat := countLit b [69, 70, 77, 78]
def count1330 (b : Nat → Bool) : Nat := countLit b [65, 66, 67, 69, 70, 77, 78]
def count1337 (b : Nat → Bool) : Nat := countLit b [81, 82]
def count1339 (b : Nat → Bool) : Nat := countLit b [79, 81, 82]
def count1342 (b : Nat → Bool) : Nat := countLit b [83, 86]
def count1344 (b : Nat → Bool) : Nat := countLit b [87, 92]
def count1346 (b : Nat → Bool) : Nat := countLit b [83, 86, 87, 92]
def count1350 (b : Nat → Bool) : Nat := countLit b [79, 81, 82, 83, 86, 87, 92]
def count1357 (b : Nat → Bool) : Nat := countLit b [65, 66, 67, 69, 70, 77, 78, 79, 81, 82, 83, 86, 87, 92]
def count1371 (b : Nat → Bool) : Nat := countLit b [97, 99]
def count1373 (b : Nat → Bool) : Nat := countLit b [94, 97, 99]
def count1376 (b : Nat → Bool) : Nat := countLit b [100, 101]
def count1378 (b : Nat → Bool) : Nat := countLit b [102, 103]
def count1380 (b : Nat → Bool) : Nat := countLit b [100, 101, 102, 103]
def count1384 (b : Nat → Bool) : Nat := countLit b [94, 97, 99, 100, 101, 102, 103]
def count1391 (b : Nat → Bool) : Nat := countLit b [105, 108]
def count1393 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count1395 (b : Nat → Bool) : Nat := countLit b [105, 108, 110, 111]
def count1399 (b : Nat → Bool) : Nat := countLit b [114, 117]
def count1401 (b : Nat → Bool) : Nat := countLit b [121, 122]
def count1403 (b : Nat → Bool) : Nat := countLit b [114, 117, 121, 122]
def count1407 (b : Nat → Bool) : Nat := countLit b [105, 108, 110, 111, 114, 117, 121, 122]
def count1415 (b : Nat → Bool) : Nat := countLit b [94, 97, 99, 100, 101, 102, 103, 105, 108, 110, 111, 114, 117, 121, 122]
def count1430 (b : Nat → Bool) : Nat := countLit b [65, 66, 67, 69, 70, 77, 78, 79, 81, 82, 83, 86, 87, 92, 94, 97, 99, 100, 101, 102, 103, 105, 108, 110, 111, 114, 117, 121, 122]
def count1459 (b : Nat → Bool) : Nat := countLit b [2, 5, 8, 9, 12, 14, 15, 18, 19, 22, 25, 27, 29, 31, 32, 34, 36, 38, 41, 44, 45, 47, 48, 51, 53, 55, 58, 59, 62, 65, 66, 67, 69, 70, 77, 78, 79, 81, 82, 83, 86, 87, 92, 94, 97, 99, 100, 101, 102, 103, 105, 108, 110, 111, 114, 117, 121, 122]
def count1501 (b : Nat → Bool) : Nat := countLit b [-5, -8]
def count1503 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8]
def count1506 (b : Nat → Bool) : Nat := countLit b [-9, -12]
def count1508 (b : Nat → Bool) : Nat := countLit b [-14, -15]
def count1510 (b : Nat → Bool) : Nat := countLit b [-9, -12, -14, -15]
def count1514 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -12, -14, -15]
def count1521 (b : Nat → Bool) : Nat := countLit b [-19, -22]
def count1523 (b : Nat → Bool) : Nat := countLit b [-18, -19, -22]
def count1526 (b : Nat → Bool) : Nat := countLit b [-25, -27]
def count1528 (b : Nat → Bool) : Nat := countLit b [-29, -31]
def count1530 (b : Nat → Bool) : Nat := countLit b [-25, -27, -29, -31]
def count1534 (b : Nat → Bool) : Nat := countLit b [-18, -19, -22, -25, -27, -29, -31]
def count1541 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31]
def count1555 (b : Nat → Bool) : Nat := countLit b [-34, -36]
def count1557 (b : Nat → Bool) : Nat := countLit b [-32, -34, -36]
def count1560 (b : Nat → Bool) : Nat := countLit b [-38, -41]
def count1562 (b : Nat → Bool) : Nat := countLit b [-44, -45]
def count1564 (b : Nat → Bool) : Nat := countLit b [-38, -41, -44, -45]
def count1568 (b : Nat → Bool) : Nat := countLit b [-32, -34, -36, -38, -41, -44, -45]
def count1575 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count1577 (b : Nat → Bool) : Nat := countLit b [-51, -53]
def count1579 (b : Nat → Bool) : Nat := countLit b [-47, -48, -51, -53]
def count1583 (b : Nat → Bool) : Nat := countLit b [-55, -58]
def count1585 (b : Nat → Bool) : Nat := countLit b [-59, -62]
def count1587 (b : Nat → Bool) : Nat := countLit b [-55, -58, -59, -62]
def count1591 (b : Nat → Bool) : Nat := countLit b [-47, -48, -51, -53, -55, -58, -59, -62]
def count1599 (b : Nat → Bool) : Nat := countLit b [-32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]
def count1614 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]
def count1632 (b : Nat → Bool) : Nat := countLit b [-66, -67]
def count1634 (b : Nat → Bool) : Nat := countLit b [-65, -66, -67]
def count1637 (b : Nat → Bool) : Nat := countLit b [-69, -70]
def count1639 (b : Nat → Bool) : Nat := countLit b [-77, -78]
def count1641 (b : Nat → Bool) : Nat := countLit b [-69, -70, -77, -78]
def count1645 (b : Nat → Bool) : Nat := countLit b [-65, -66, -67, -69, -70, -77, -78]
def count1652 (b : Nat → Bool) : Nat := countLit b [-81, -82]
def count1654 (b : Nat → Bool) : Nat := countLit b [-79, -81, -82]
def count1657 (b : Nat → Bool) : Nat := countLit b [-83, -86]
def count1659 (b : Nat → Bool) : Nat := countLit b [-87, -92]
def count1661 (b : Nat → Bool) : Nat := countLit b [-83, -86, -87, -92]
def count1665 (b : Nat → Bool) : Nat := countLit b [-79, -81, -82, -83, -86, -87, -92]
def count1672 (b : Nat → Bool) : Nat := countLit b [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]
def count1686 (b : Nat → Bool) : Nat := countLit b [-97, -99]
def count1688 (b : Nat → Bool) : Nat := countLit b [-94, -97, -99]
def count1691 (b : Nat → Bool) : Nat := countLit b [-100, -101]
def count1693 (b : Nat → Bool) : Nat := countLit b [-102, -103]
def count1695 (b : Nat → Bool) : Nat := countLit b [-100, -101, -102, -103]
def count1699 (b : Nat → Bool) : Nat := countLit b [-94, -97, -99, -100, -101, -102, -103]
def count1706 (b : Nat → Bool) : Nat := countLit b [-105, -108]
def count1708 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1710 (b : Nat → Bool) : Nat := countLit b [-105, -108, -110, -111]
def count1714 (b : Nat → Bool) : Nat := countLit b [-114, -117]
def count1716 (b : Nat → Bool) : Nat := countLit b [-121, -122]
def count1718 (b : Nat → Bool) : Nat := countLit b [-114, -117, -121, -122]
def count1722 (b : Nat → Bool) : Nat := countLit b [-105, -108, -110, -111, -114, -117, -121, -122]
def count1730 (b : Nat → Bool) : Nat := countLit b [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]
def count1745 (b : Nat → Bool) : Nat := countLit b [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]
def count1763 (b : Nat → Bool) : Nat := countLit b [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62, -65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 890 then (if i < 445 then (if i < 222 then (if i < 111 then (if i < 55 then (if i < 27 then (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 4 then b 3 else (if i < 5 then b 4 else b 5))) else (if i < 9 then (if i < 7 then b 6 else (if i < 8 then b 7 else b 8)) else (if i < 11 then (if i < 10 then b 9 else b 10) else (if i < 12 then b 11 else b 12)))) else (if i < 20 then (if i < 16 then (if i < 14 then b 13 else (if i < 15 then b 14 else b 15)) else (if i < 18 then (if i < 17 then b 16 else b 17) else (if i < 19 then b 18 else b 19))) else (if i < 23 then (if i < 21 then b 20 else (if i < 22 then b 21 else b 22)) else (if i < 25 then (if i < 24 then b 23 else b 24) else (if i < 26 then b 25 else b 26))))) else (if i < 41 then (if i < 34 then (if i < 30 then (if i < 28 then b 27 else (if i < 29 then b 28 else b 29)) else (if i < 32 then (if i < 31 then b 30 else b 31) else (if i < 33 then b 32 else b 33))) else (if i < 37 then (if i < 35 then b 34 else (if i < 36 then b 35 else b 36)) else (if i < 39 then (if i < 38 then b 37 else b 38) else (if i < 40 then b 39 else b 40)))) else (if i < 48 then (if i < 44 then (if i < 42 then b 41 else (if i < 43 then b 42 else b 43)) else (if i < 46 then (if i < 45 then b 44 else b 45) else (if i < 47 then b 46 else b 47))) else (if i < 51 then (if i < 49 then b 48 else (if i < 50 then b 49 else b 50)) else (if i < 53 then (if i < 52 then b 51 else b 52) else (if i < 54 then b 53 else b 54)))))) else (if i < 83 then (if i < 69 then (if i < 62 then (if i < 58 then (if i < 56 then b 55 else (if i < 57 then b 56 else b 57)) else (if i < 60 then (if i < 59 then b 58 else b 59) else (if i < 61 then b 60 else b 61))) else (if i < 65 then (if i < 63 then b 62 else (if i < 64 then b 63 else b 64)) else (if i < 67 then (if i < 66 then b 65 else b 66) else (if i < 68 then b 67 else b 68)))) else (if i < 76 then (if i < 72 then (if i < 70 then b 69 else (if i < 71 then b 70 else b 71)) else (if i < 74 then (if i < 73 then b 72 else b 73) else (if i < 75 then b 74 else b 75))) else (if i < 79 then (if i < 77 then b 76 else (if i < 78 then b 77 else b 78)) else (if i < 81 then (if i < 80 then b 79 else b 80) else (if i < 82 then b 81 else b 82))))) else (if i < 97 then (if i < 90 then (if i < 86 then (if i < 84 then b 83 else (if i < 85 then b 84 else b 85)) else (if i < 88 then (if i < 87 then b 86 else b 87) else (if i < 89 then b 88 else b 89))) else (if i < 93 then (if i < 91 then b 90 else (if i < 92 then b 91 else b 92)) else (if i < 95 then (if i < 94 then b 93 else b 94) else (if i < 96 then b 95 else b 96)))) else (if i < 104 then (if i < 100 then (if i < 98 then b 97 else (if i < 99 then b 98 else b 99)) else (if i < 102 then (if i < 101 then b 100 else b 101) else (if i < 103 then b 102 else b 103))) else (if i < 107 then (if i < 105 then b 104 else (if i < 106 then b 105 else b 106)) else (if i < 109 then (if i < 108 then b 107 else b 108) else (if i < 110 then b 109 else b 110))))))) else (if i < 166 then (if i < 138 then (if i < 124 then (if i < 117 then (if i < 114 then (if i < 112 then b 111 else (if i < 113 then b 112 else b 113)) else (if i < 115 then b 114 else (if i < 116 then b 115 else b 116))) else (if i < 120 then (if i < 118 then b 117 else (if i < 119 then b 118 else b 119)) else (if i < 122 then (if i < 121 then b 120 else b 121) else (if i < 123 then b 122 else b 123)))) else (if i < 131 then (if i < 127 then (if i < 125 then b 124 else (if i < 126 then b 125 else b 126)) else (if i < 129 then (if i < 128 then b 127 else b 128) else (if i < 130 then b 129 else b 130))) else (if i < 134 then (if i < 132 then b 131 else (if i < 133 then b 132 else b 133)) else (if i < 136 then (if i < 135 then b 134 else b 135) else (if i < 137 then b 136 else b 137))))) else (if i < 152 then (if i < 145 then (if i < 141 then (if i < 139 then b 138 else (if i < 140 then b 139 else b 140)) else (if i < 143 then (if i < 142 then b 141 else b 142) else (if i < 144 then b 143 else b 144))) else (if i < 148 then (if i < 146 then b 145 else (if i < 147 then b 146 else b 147)) else (if i < 150 then (if i < 149 then b 148 else b 149) else (if i < 151 then b 150 else b 151)))) else (if i < 159 then (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 157 then (if i < 156 then b 155 else b 156) else (if i < 158 then b 157 else b 158))) else (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 164 then (if i < 163 then b 162 else b 163) else (if i < 165 then b 164 else b 165)))))) else (if i < 194 then (if i < 180 then (if i < 173 then (if i < 169 then (if i < 167 then b 166 else (if i < 168 then b 167 else b 168)) else (if i < 171 then (if i < 170 then b 169 else b 170) else (if i < 172 then b 171 else b 172))) else (if i < 176 then (if i < 174 then b 173 else (if i < 175 then b 174 else b 175)) else (if i < 178 then (if i < 177 then b 176 else b 177) else (if i < 179 then b 178 else b 179)))) else (if i < 187 then (if i < 183 then (if i < 181 then b 180 else (if i < 182 then b 181 else b 182)) else (if i < 185 then (if i < 184 then b 183 else b 184) else (if i < 186 then b 185 else b 186))) else (if i < 190 then (if i < 188 then b 187 else (if i < 189 then b 188 else b 189)) else (if i < 192 then (if i < 191 then b 190 else b 191) else (if i < 193 then b 192 else b 193))))) else (if i < 208 then (if i < 201 then (if i < 197 then (if i < 195 then b 194 else (if i < 196 then b 195 else b 196)) else (if i < 199 then (if i < 198 then b 197 else b 198) else (if i < 200 then b 199 else b 200))) else (if i < 204 then (if i < 202 then b 201 else (if i < 203 then b 202 else b 203)) else (if i < 206 then (if i < 205 then b 204 else b 205) else (if i < 207 then b 206 else b 207)))) else (if i < 215 then (if i < 211 then (if i < 209 then b 208 else (if i < 210 then b 209 else b 210)) else (if i < 213 then (if i < 212 then b 211 else b 212) else (if i < 214 then b 213 else b 214))) else (if i < 218 then (if i < 216 then b 215 else (if i < 217 then b 216 else b 217)) else (if i < 220 then (if i < 219 then b 218 else b 219) else (if i < 221 then b 220 else b 221)))))))) else (if i < 333 then (if i < 277 then (if i < 249 then (if i < 235 then (if i < 228 then (if i < 225 then (if i < 223 then b 222 else (if i < 224 then b 223 else b 224)) else (if i < 226 then b 225 else (if i < 227 then b 226 else b 227))) else (if i < 231 then (if i < 229 then b 228 else (if i < 230 then b 229 else b 230)) else (if i < 233 then (if i < 232 then b 231 else b 232) else (if i < 234 then b 233 else b 234)))) else (if i < 242 then (if i < 238 then (if i < 236 then b 235 else (if i < 237 then b 236 else b 237)) else (if i < 240 then (if i < 239 then b 238 else b 239) else (if i < 241 then b 240 else b 241))) else (if i < 245 then (if i < 243 then b 242 else (if i < 244 then b 243 else b 244)) else (if i < 247 then (if i < 246 then decide (1 ≤ count245 b) else decide (2 ≤ count245 b)) else (if i < 248 then decide (1 ≤ count247 b) else decide (2 ≤ count247 b)))))) else (if i < 263 then (if i < 256 then (if i < 252 then (if i < 250 then decide (1 ≤ count249 b) else (if i < 251 then decide (2 ≤ count249 b) else decide (1 ≤ count251 b))) else (if i < 254 then (if i < 253 then decide (2 ≤ count251 b) else decide (1 ≤ count253 b)) else (if i < 255 then decide (2 ≤ count253 b) else decide (1 ≤ count255 b)))) else (if i < 259 then (if i < 257 then decide (2 ≤ count255 b) else (if i < 258 then decide (1 ≤ count257 b) else decide (2 ≤ count257 b))) else (if i < 261 then (if i < 260 then decide (1 ≤ count259 b) else decide (2 ≤ count259 b)) else (if i < 262 then decide (1 ≤ count261 b) else decide (2 ≤ count261 b))))) else (if i < 270 then (if i < 266 then (if i < 264 then decide (1 ≤ count263 b) else (if i < 265 then decide (2 ≤ count263 b) else decide (1 ≤ count265 b))) else (if i < 268 then (if i < 267 then decide (2 ≤ count265 b) else decide (1 ≤ count267 b)) else (if i < 269 then decide (2 ≤ count267 b) else decide (1 ≤ count269 b)))) else (if i < 273 then (if i < 271 then decide (2 ≤ count269 b) else (if i < 272 then decide (1 ≤ count271 b) else decide (2 ≤ count271 b))) else (if i < 275 then (if i < 274 then decide (1 ≤ count273 b) else decide (2 ≤ count273 b)) else (if i < 276 then decide (1 ≤ count275 b) else decide (2 ≤ count275 b))))))) else (if i < 305 then (if i < 291 then (if i < 284 then (if i < 280 then (if i < 278 then decide (1 ≤ count277 b) else (if i < 279 then decide (2 ≤ count277 b) else decide (1 ≤ count279 b))) else (if i < 282 then (if i < 281 then decide (2 ≤ count279 b) else decide (1 ≤ count281 b)) else (if i < 283 then decide (2 ≤ count281 b) else decide (1 ≤ count283 b)))) else (if i < 287 then (if i < 285 then decide (2 ≤ count283 b) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b))) else (if i < 289 then (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))))) else (if i < 298 then (if i < 294 then (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b))) else (if i < 296 then (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)))) else (if i < 301 then (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))) else (if i < 303 then (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b)) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b)))))) else (if i < 319 then (if i < 312 then (if i < 308 then (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))) else (if i < 310 then (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))) else (if i < 315 then (if i < 313 then decide (2 ≤ count311 b) else (if i < 314 then decide (1 ≤ count313 b) else decide (2 ≤ count313 b))) else (if i < 317 then (if i < 316 then decide (1 ≤ count315 b) else decide (2 ≤ count315 b)) else (if i < 318 then decide (1 ≤ count317 b) else decide (2 ≤ count317 b))))) else (if i < 326 then (if i < 322 then (if i < 320 then decide (1 ≤ count319 b) else (if i < 321 then decide (2 ≤ count319 b) else decide (1 ≤ count321 b))) else (if i < 324 then (if i < 323 then decide (2 ≤ count321 b) else decide (1 ≤ count323 b)) else (if i < 325 then decide (2 ≤ count323 b) else decide (1 ≤ count325 b)))) else (if i < 329 then (if i < 327 then decide (2 ≤ count325 b) else (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b))) else (if i < 331 then (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b)) else (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)))))))) else (if i < 389 then (if i < 361 then (if i < 347 then (if i < 340 then (if i < 336 then (if i < 334 then decide (1 ≤ count333 b) else (if i < 335 then decide (2 ≤ count333 b) else decide (1 ≤ count335 b))) else (if i < 338 then (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b)) else (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)))) else (if i < 343 then (if i < 341 then decide (2 ≤ count339 b) else (if i < 342 then decide (1 ≤ count341 b) else decide (2 ≤ count341 b))) else (if i < 345 then (if i < 344 then decide (1 ≤ count343 b) else decide (2 ≤ count343 b)) else (if i < 346 then decide (1 ≤ count345 b) else decide (2 ≤ count345 b))))) else (if i < 354 then (if i < 350 then (if i < 348 then decide (1 ≤ count347 b) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b))) else (if i < 352 then (if i < 351 then decide (2 ≤ count349 b) else decide (1 ≤ count351 b)) else (if i < 353 then decide (2 ≤ count351 b) else decide (1 ≤ count353 b)))) else (if i < 357 then (if i < 355 then decide (2 ≤ count353 b) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b))) else (if i < 359 then (if i < 358 then decide (1 ≤ count357 b) else decide (2 ≤ count357 b)) else (if i < 360 then decide (1 ≤ count359 b) else decide (2 ≤ count359 b)))))) else (if i < 375 then (if i < 368 then (if i < 364 then (if i < 362 then decide (1 ≤ count361 b) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))) else (if i < 366 then (if i < 365 then decide (2 ≤ count363 b) else decide (1 ≤ count365 b)) else (if i < 367 then decide (2 ≤ count365 b) else decide (1 ≤ count367 b)))) else (if i < 371 then (if i < 369 then decide (2 ≤ count367 b) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b))) else (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b))))) else (if i < 382 then (if i < 378 then (if i < 376 then decide (1 ≤ count375 b) else (if i < 377 then decide (2 ≤ count375 b) else decide (1 ≤ count377 b))) else (if i < 380 then (if i < 379 then decide (2 ≤ count377 b) else decide (1 ≤ count379 b)) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b)))) else (if i < 385 then (if i < 383 then decide (2 ≤ count381 b) else (if i < 384 then decide (1 ≤ count383 b) else decide (2 ≤ count383 b))) else (if i < 387 then (if i < 386 then decide (1 ≤ count385 b) else decide (2 ≤ count385 b)) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))))))) else (if i < 417 then (if i < 403 then (if i < 396 then (if i < 392 then (if i < 390 then decide (1 ≤ count389 b) else (if i < 391 then decide (2 ≤ count389 b) else decide (1 ≤ count391 b))) else (if i < 394 then (if i < 393 then decide (2 ≤ count391 b) else decide (1 ≤ count393 b)) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b)))) else (if i < 399 then (if i < 397 then decide (2 ≤ count395 b) else (if i < 398 then decide (1 ≤ count397 b) else decide (2 ≤ count397 b))) else (if i < 401 then (if i < 400 then decide (1 ≤ count399 b) else decide (2 ≤ count399 b)) else (if i < 402 then decide (1 ≤ count401 b) else decide (2 ≤ count401 b))))) else (if i < 410 then (if i < 406 then (if i < 404 then decide (1 ≤ count403 b) else (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b))) else (if i < 408 then (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b)) else (if i < 409 then decide (2 ≤ count407 b) else decide (1 ≤ count409 b)))) else (if i < 413 then (if i < 411 then decide (2 ≤ count409 b) else (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b))) else (if i < 415 then (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)) else (if i < 416 then decide (1 ≤ count415 b) else decide (2 ≤ count415 b)))))) else (if i < 431 then (if i < 424 then (if i < 420 then (if i < 418 then decide (1 ≤ count417 b) else (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b))) else (if i < 422 then (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b)) else (if i < 423 then decide (2 ≤ count421 b) else decide (1 ≤ count423 b)))) else (if i < 427 then (if i < 425 then decide (2 ≤ count423 b) else (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b))) else (if i < 429 then (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)) else (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b))))) else (if i < 438 then (if i < 434 then (if i < 432 then decide (1 ≤ count431 b) else (if i < 433 then decide (2 ≤ count431 b) else decide (1 ≤ count433 b))) else (if i < 436 then (if i < 435 then decide (2 ≤ count433 b) else decide (1 ≤ count435 b)) else (if i < 437 then decide (2 ≤ count435 b) else decide (1 ≤ count437 b)))) else (if i < 441 then (if i < 439 then decide (2 ≤ count437 b) else (if i < 440 then decide (1 ≤ count439 b) else decide (2 ≤ count439 b))) else (if i < 443 then (if i < 442 then decide (1 ≤ count441 b) else decide (2 ≤ count441 b)) else (if i < 444 then decide (1 ≤ count443 b) else decide (2 ≤ count443 b)))))))))) else (if i < 667 then (if i < 556 then (if i < 500 then (if i < 472 then (if i < 458 then (if i < 451 then (if i < 448 then (if i < 446 then decide (1 ≤ count445 b) else (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b))) else (if i < 449 then decide (2 ≤ count447 b) else (if i < 450 then decide (1 ≤ count449 b) else decide (2 ≤ count449 b)))) else (if i < 454 then (if i < 452 then decide (1 ≤ count451 b) else (if i < 453 then decide (2 ≤ count451 b) else decide (1 ≤ count453 b))) else (if i < 456 then (if i < 455 then decide (2 ≤ count453 b) else decide (1 ≤ count455 b)) else (if i < 457 then decide (2 ≤ count455 b) else decide (1 ≤ count457 b))))) else (if i < 465 then (if i < 461 then (if i < 459 then decide (2 ≤ count457 b) else (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b))) else (if i < 463 then (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b)) else (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b)))) else (if i < 468 then (if i < 466 then decide (1 ≤ count465 b) else (if i < 467 then decide (2 ≤ count465 b) else decide (1 ≤ count467 b))) else (if i < 470 then (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b)) else (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b)))))) else (if i < 486 then (if i < 479 then (if i < 475 then (if i < 473 then decide (2 ≤ count471 b) else (if i < 474 then decide (1 ≤ count473 b) else decide (2 ≤ count473 b))) else (if i < 477 then (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b)) else (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b)))) else (if i < 482 then (if i < 480 then decide (1 ≤ count479 b) else (if i < 481 then decide (2 ≤ count479 b) else decide (1 ≤ count481 b))) else (if i < 484 then (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b)) else (if i < 485 then decide (2 ≤ count483 b) else decide (1 ≤ count485 b))))) else (if i < 493 then (if i < 489 then (if i < 487 then decide (2 ≤ count485 b) else (if i < 488 then decide (1 ≤ count487 b) else decide (2 ≤ count487 b))) else (if i < 491 then (if i < 490 then decide (1 ≤ count489 b) else decide (2 ≤ count489 b)) else (if i < 492 then decide (3 ≤ count489 b) else decide (4 ≤ count489 b)))) else (if i < 496 then (if i < 494 then decide (1 ≤ count493 b) else (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b))) else (if i < 498 then (if i < 497 then decide (2 ≤ count495 b) else decide (1 ≤ count497 b)) else (if i < 499 then decide (2 ≤ count497 b) else decide (3 ≤ count497 b))))))) else (if i < 528 then (if i < 514 then (if i < 507 then (if i < 503 then (if i < 501 then decide (4 ≤ count497 b) else (if i < 502 then decide (1 ≤ count501 b) else decide (2 ≤ count501 b))) else (if i < 505 then (if i < 504 then decide (3 ≤ count501 b) else decide (4 ≤ count501 b)) else (if i < 506 then decide (5 ≤ count501 b) else decide (6 ≤ count501 b)))) else (if i < 510 then (if i < 508 then decide (7 ≤ count501 b) else (if i < 509 then decide (8 ≤ count501 b) else decide (1 ≤ count509 b))) else (if i < 512 then (if i < 511 then decide (2 ≤ count509 b) else decide (1 ≤ count511 b)) else (if i < 513 then decide (2 ≤ count511 b) else decide (1 ≤ count513 b))))) else (if i < 521 then (if i < 517 then (if i < 515 then decide (2 ≤ count513 b) else (if i < 516 then decide (3 ≤ count513 b) else decide (4 ≤ count513 b))) else (if i < 519 then (if i < 518 then decide (1 ≤ count517 b) else decide (2 ≤ count517 b)) else (if i < 520 then decide (1 ≤ count519 b) else decide (2 ≤ count519 b)))) else (if i < 524 then (if i < 522 then decide (1 ≤ count521 b) else (if i < 523 then decide (2 ≤ count521 b) else decide (3 ≤ count521 b))) else (if i < 526 then (if i < 525 then decide (4 ≤ count521 b) else decide (1 ≤ count525 b)) else (if i < 527 then decide (2 ≤ count525 b) else decide (3 ≤ count525 b)))))) else (if i < 542 then (if i < 535 then (if i < 531 then (if i < 529 then decide (4 ≤ count525 b) else (if i < 530 then decide (5 ≤ count525 b) else decide (6 ≤ count525 b))) else (if i < 533 then (if i < 532 then decide (7 ≤ count525 b) else decide (8 ≤ count525 b)) else (if i < 534 then decide (1 ≤ count533 b) else decide (2 ≤ count533 b)))) else (if i < 538 then (if i < 536 then decide (3 ≤ count533 b) else (if i < 537 then decide (4 ≤ count533 b) else decide (5 ≤ count533 b))) else (if i < 540 then (if i < 539 then decide (6 ≤ count533 b) else decide (7 ≤ count533 b)) else (if i < 541 then decide (8 ≤ count533 b) else decide (9 ≤ count533 b))))) else (if i < 549 then (if i < 545 then (if i < 543 then decide (10 ≤ count533 b) else (if i < 544 then decide (11 ≤ count533 b) else decide (12 ≤ count533 b))) else (if i < 547 then (if i < 546 then decide (13 ≤ count533 b) else decide (14 ≤ count533 b)) else (if i < 548 then decide (15 ≤ count533 b) else decide (16 ≤ count533 b)))) else (if i < 552 then (if i < 550 then decide (1 ≤ count549 b) else (if i < 551 then decide (2 ≤ count549 b) else decide (1 ≤ count551 b))) else (if i < 554 then (if i < 553 then decide (2 ≤ count551 b) else decide (1 ≤ count553 b)) else (if i < 555 then decide (2 ≤ count553 b) else decide (3 ≤ count553 b)))))))) else (if i < 611 then (if i < 583 then (if i < 569 then (if i < 562 then (if i < 559 then (if i < 557 then decide (4 ≤ count553 b) else (if i < 558 then decide (1 ≤ count557 b) else decide (2 ≤ count557 b))) else (if i < 560 then decide (1 ≤ count559 b) else (if i < 561 then decide (2 ≤ count559 b) else decide (1 ≤ count561 b)))) else (if i < 565 then (if i < 563 then decide (2 ≤ count561 b) else (if i < 564 then decide (3 ≤ count561 b) else decide (4 ≤ count561 b))) else (if i < 567 then (if i < 566 then decide (1 ≤ count565 b) else decide (2 ≤ count565 b)) else (if i < 568 then decide (3 ≤ count565 b) else decide (4 ≤ count565 b))))) else (if i < 576 then (if i < 572 then (if i < 570 then decide (5 ≤ count565 b) else (if i < 571 then decide (6 ≤ count565 b) else decide (7 ≤ count565 b))) else (if i < 574 then (if i < 573 then decide (8 ≤ count565 b) else decide (1 ≤ count573 b)) else (if i < 575 then decide (2 ≤ count573 b) else decide (1 ≤ count575 b)))) else (if i < 579 then (if i < 577 then decide (2 ≤ count575 b) else (if i < 578 then decide (1 ≤ count577 b) else decide (2 ≤ count577 b))) else (if i < 581 then (if i < 580 then decide (3 ≤ count577 b) else decide (4 ≤ count577 b)) else (if i < 582 then decide (1 ≤ count581 b) else decide (2 ≤ count581 b)))))) else (if i < 597 then (if i < 590 then (if i < 586 then (if i < 584 then decide (1 ≤ count583 b) else (if i < 585 then decide (2 ≤ count583 b) else decide (1 ≤ count585 b))) else (if i < 588 then (if i < 587 then decide (2 ≤ count585 b) else decide (3 ≤ count585 b)) else (if i < 589 then decide (4 ≤ count585 b) else decide (1 ≤ count589 b)))) else (if i < 593 then (if i < 591 then decide (2 ≤ count589 b) else (if i < 592 then decide (3 ≤ count589 b) else decide (4 ≤ count589 b))) else (if i < 595 then (if i < 594 then decide (5 ≤ count589 b) else decide (6 ≤ count589 b)) else (if i < 596 then decide (7 ≤ count589 b) else decide (8 ≤ count589 b))))) else (if i < 604 then (if i < 600 then (if i < 598 then decide (1 ≤ count597 b) else (if i < 599 then decide (2 ≤ count597 b) else decide (3 ≤ count597 b))) else (if i < 602 then (if i < 601 then decide (4 ≤ count597 b) else decide (5 ≤ count597 b)) else (if i < 603 then decide (6 ≤ count597 b) else decide (7 ≤ count597 b)))) else (if i < 607 then (if i < 605 then decide (8 ≤ count597 b) else (if i < 606 then decide (9 ≤ count597 b) else decide (10 ≤ count597 b))) else (if i < 609 then (if i < 608 then decide (11 ≤ count597 b) else decide (12 ≤ count597 b)) else (if i < 610 then decide (13 ≤ count597 b) else decide (14 ≤ count597 b))))))) else (if i < 639 then (if i < 625 then (if i < 618 then (if i < 614 then (if i < 612 then decide (15 ≤ count597 b) else (if i < 613 then decide (16 ≤ count597 b) else decide (1 ≤ count613 b))) else (if i < 616 then (if i < 615 then decide (2 ≤ count613 b) else decide (3 ≤ count613 b)) else (if i < 617 then decide (4 ≤ count613 b) else decide (5 ≤ count613 b)))) else (if i < 621 then (if i < 619 then decide (6 ≤ count613 b) else (if i < 620 then decide (7 ≤ count613 b) else decide (8 ≤ count613 b))) else (if i < 623 then (if i < 622 then decide (9 ≤ count613 b) else decide (10 ≤ count613 b)) else (if i < 624 then decide (11 ≤ count613 b) else decide (12 ≤ count613 b))))) else (if i < 632 then (if i < 628 then (if i < 626 then decide (13 ≤ count613 b) else (if i < 627 then decide (14 ≤ count613 b) else decide (15 ≤ count613 b))) else (if i < 630 then (if i < 629 then decide (16 ≤ count613 b) else decide (17 ≤ count613 b)) else (if i < 631 then decide (18 ≤ count613 b) else decide (19 ≤ count613 b)))) else (if i < 635 then (if i < 633 then decide (20 ≤ count613 b) else (if i < 634 then decide (21 ≤ count613 b) else decide (22 ≤ count613 b))) else (if i < 637 then (if i < 636 then decide (23 ≤ count613 b) else decide (24 ≤ count613 b)) else (if i < 638 then decide (25 ≤ count613 b) else decide (26 ≤ count613 b)))))) else (if i < 653 then (if i < 646 then (if i < 642 then (if i < 640 then decide (27 ≤ count613 b) else (if i < 641 then decide (28 ≤ count613 b) else decide (29 ≤ count613 b))) else (if i < 644 then (if i < 643 then decide (30 ≤ count613 b) else decide (31 ≤ count613 b)) else (if i < 645 then decide (32 ≤ count613 b) else decide (1 ≤ count645 b)))) else (if i < 649 then (if i < 647 then decide (2 ≤ count645 b) else (if i < 648 then decide (1 ≤ count647 b) else decide (2 ≤ count647 b))) else (if i < 651 then (if i < 650 then decide (1 ≤ count649 b) else decide (2 ≤ count649 b)) else (if i < 652 then decide (3 ≤ count649 b) else decide (4 ≤ count649 b))))) else (if i < 660 then (if i < 656 then (if i < 654 then decide (1 ≤ count653 b) else (if i < 655 then decide (2 ≤ count653 b) else decide (1 ≤ count655 b))) else (if i < 658 then (if i < 657 then decide (2 ≤ count655 b) else decide (1 ≤ count657 b)) else (if i < 659 then decide (2 ≤ count657 b) else decide (3 ≤ count657 b)))) else (if i < 663 then (if i < 661 then decide (4 ≤ count657 b) else (if i < 662 then decide (1 ≤ count661 b) else decide (2 ≤ count661 b))) else (if i < 665 then (if i < 664 then decide (3 ≤ count661 b) else decide (4 ≤ count661 b)) else (if i < 666 then decide (5 ≤ count661 b) else decide (6 ≤ count661 b))))))))) else (if i < 778 then (if i < 722 then (if i < 694 then (if i < 680 then (if i < 673 then (if i < 670 then (if i < 668 then decide (7 ≤ count661 b) else (if i < 669 then decide (8 ≤ count661 b) else decide (1 ≤ count669 b))) else (if i < 671 then decide (2 ≤ count669 b) else (if i < 672 then decide (1 ≤ count671 b) else decide (2 ≤ count671 b)))) else (if i < 676 then (if i < 674 then decide (1 ≤ count673 b) else (if i < 675 then decide (2 ≤ count673 b) else decide (3 ≤ count673 b))) else (if i < 678 then (if i < 677 then decide (4 ≤ count673 b) else decide (1 ≤ count677 b)) else (if i < 679 then decide (2 ≤ count677 b) else decide (1 ≤ count679 b))))) else (if i < 687 then (if i < 683 then (if i < 681 then decide (2 ≤ count679 b) else (if i < 682 then decide (1 ≤ count681 b) else decide (2 ≤ count681 b))) else (if i < 685 then (if i < 684 then decide (3 ≤ count681 b) else decide (4 ≤ count681 b)) else (if i < 686 then decide (1 ≤ count685 b) else decide (2 ≤ count685 b)))) else (if i < 690 then (if i < 688 then decide (3 ≤ count685 b) else (if i < 689 then decide (4 ≤ count685 b) else decide (5 ≤ count685 b))) else (if i < 692 then (if i < 691 then decide (6 ≤ count685 b) else decide (7 ≤ count685 b)) else (if i < 693 then decide (8 ≤ count685 b) else decide (1 ≤ count693 b)))))) else (if i < 708 then (if i < 701 then (if i < 697 then (if i < 695 then decide (2 ≤ count693 b) else (if i < 696 then decide (3 ≤ count693 b) else decide (4 ≤ count693 b))) else (if i < 699 then (if i < 698 then decide (5 ≤ count693 b) else decide (6 ≤ count693 b)) else (if i < 700 then decide (7 ≤ count693 b) else decide (8 ≤ count693 b)))) else (if i < 704 then (if i < 702 then decide (9 ≤ count693 b) else (if i < 703 then decide (10 ≤ count693 b) else decide (11 ≤ count693 b))) else (if i < 706 then (if i < 705 then decide (12 ≤ count693 b) else decide (13 ≤ count693 b)) else (if i < 707 then decide (14 ≤ count693 b) else decide (15 ≤ count693 b))))) else (if i < 715 then (if i < 711 then (if i < 709 then decide (16 ≤ count693 b) else (if i < 710 then decide (1 ≤ count709 b) else decide (2 ≤ count709 b))) else (if i < 713 then (if i < 712 then decide (1 ≤ count711 b) else decide (2 ≤ count711 b)) else (if i < 714 then decide (1 ≤ count713 b) else decide (2 ≤ count713 b)))) else (if i < 718 then (if i < 716 then decide (3 ≤ count713 b) else (if i < 717 then decide (4 ≤ count713 b) else decide (1 ≤ count717 b))) else (if i < 720 then (if i < 719 then decide (2 ≤ count717 b) else decide (1 ≤ count719 b)) else (if i < 721 then decide (2 ≤ count719 b) else decide (1 ≤ count721 b))))))) else (if i < 750 then (if i < 736 then (if i < 729 then (if i < 725 then (if i < 723 then decide (2 ≤ count721 b) else (if i < 724 then decide (3 ≤ count721 b) else decide (4 ≤ count721 b))) else (if i < 727 then (if i < 726 then decide (1 ≤ count725 b) else decide (2 ≤ count725 b)) else (if i < 728 then decide (3 ≤ count725 b) else decide (4 ≤ count725 b)))) else (if i < 732 then (if i < 730 then decide (5 ≤ count725 b) else (if i < 731 then decide (6 ≤ count725 b) else decide (7 ≤ count725 b))) else (if i < 734 then (if i < 733 then decide (8 ≤ count725 b) else decide (1 ≤ count733 b)) else (if i < 735 then decide (2 ≤ count733 b) else decide (1 ≤ count735 b))))) else (if i < 743 then (if i < 739 then (if i < 737 then decide (2 ≤ count735 b) else (if i < 738 then decide (1 ≤ count737 b) else decide (2 ≤ count737 b))) else (if i < 741 then (if i < 740 then decide (3 ≤ count737 b) else decide (4 ≤ count737 b)) else (if i < 742 then decide (1 ≤ count741 b) else decide (2 ≤ count741 b)))) else (if i < 746 then (if i < 744 then decide (1 ≤ count743 b) else (if i < 745 then decide (2 ≤ count743 b) else decide (1 ≤ count745 b))) else (if i < 748 then (if i < 747 then decide (2 ≤ count745 b) else decide (3 ≤ count745 b)) else (if i < 749 then decide (4 ≤ count745 b) else decide (1 ≤ count749 b)))))) else (if i < 764 then (if i < 757 then (if i < 753 then (if i < 751 then decide (2 ≤ count749 b) else (if i < 752 then decide (3 ≤ count749 b) else decide (4 ≤ count749 b))) else (if i < 755 then (if i < 754 then decide (5 ≤ count749 b) else decide (6 ≤ count749 b)) else (if i < 756 then decide (7 ≤ count749 b) else decide (8 ≤ count749 b)))) else (if i < 760 then (if i < 758 then decide (1 ≤ count757 b) else (if i < 759 then decide (2 ≤ count757 b) else decide (3 ≤ count757 b))) else (if i < 762 then (if i < 761 then decide (4 ≤ count757 b) else decide (5 ≤ count757 b)) else (if i < 763 then decide (6 ≤ count757 b) else decide (7 ≤ count757 b))))) else (if i < 771 then (if i < 767 then (if i < 765 then decide (8 ≤ count757 b) else (if i < 766 then decide (9 ≤ count757 b) else decide (10 ≤ count757 b))) else (if i < 769 then (if i < 768 then decide (11 ≤ count757 b) else decide (12 ≤ count757 b)) else (if i < 770 then decide (13 ≤ count757 b) else decide (14 ≤ count757 b)))) else (if i < 774 then (if i < 772 then decide (15 ≤ count757 b) else (if i < 773 then decide (16 ≤ count757 b) else decide (1 ≤ count773 b))) else (if i < 776 then (if i < 775 then decide (2 ≤ count773 b) else decide (3 ≤ count773 b)) else (if i < 777 then decide (4 ≤ count773 b) else decide (5 ≤ count773 b)))))))) else (if i < 834 then (if i < 806 then (if i < 792 then (if i < 785 then (if i < 781 then (if i < 779 then decide (6 ≤ count773 b) else (if i < 780 then decide (7 ≤ count773 b) else decide (8 ≤ count773 b))) else (if i < 783 then (if i < 782 then decide (9 ≤ count773 b) else decide (10 ≤ count773 b)) else (if i < 784 then decide (11 ≤ count773 b) else decide (12 ≤ count773 b)))) else (if i < 788 then (if i < 786 then decide (13 ≤ count773 b) else (if i < 787 then decide (14 ≤ count773 b) else decide (15 ≤ count773 b))) else (if i < 790 then (if i < 789 then decide (16 ≤ count773 b) else decide (17 ≤ count773 b)) else (if i < 791 then decide (18 ≤ count773 b) else decide (19 ≤ count773 b))))) else (if i < 799 then (if i < 795 then (if i < 793 then decide (20 ≤ count773 b) else (if i < 794 then decide (21 ≤ count773 b) else decide (22 ≤ count773 b))) else (if i < 797 then (if i < 796 then decide (23 ≤ count773 b) else decide (24 ≤ count773 b)) else (if i < 798 then decide (25 ≤ count773 b) else decide (26 ≤ count773 b)))) else (if i < 802 then (if i < 800 then decide (27 ≤ count773 b) else (if i < 801 then decide (28 ≤ count773 b) else decide (29 ≤ count773 b))) else (if i < 804 then (if i < 803 then decide (30 ≤ count773 b) else decide (31 ≤ count773 b)) else (if i < 805 then decide (32 ≤ count773 b) else decide (1 ≤ count805 b)))))) else (if i < 820 then (if i < 813 then (if i < 809 then (if i < 807 then decide (2 ≤ count805 b) else (if i < 808 then decide (3 ≤ count805 b) else decide (4 ≤ count805 b))) else (if i < 811 then (if i < 810 then decide (5 ≤ count805 b) else decide (6 ≤ count805 b)) else (if i < 812 then decide (7 ≤ count805 b) else decide (8 ≤ count805 b)))) else (if i < 816 then (if i < 814 then decide (9 ≤ count805 b) else (if i < 815 then decide (10 ≤ count805 b) else decide (11 ≤ count805 b))) else (if i < 818 then (if i < 817 then decide (12 ≤ count805 b) else decide (13 ≤ count805 b)) else (if i < 819 then decide (14 ≤ count805 b) else decide (15 ≤ count805 b))))) else (if i < 827 then (if i < 823 then (if i < 821 then decide (16 ≤ count805 b) else (if i < 822 then decide (17 ≤ count805 b) else decide (18 ≤ count805 b))) else (if i < 825 then (if i < 824 then decide (19 ≤ count805 b) else decide (20 ≤ count805 b)) else (if i < 826 then decide (21 ≤ count805 b) else decide (22 ≤ count805 b)))) else (if i < 830 then (if i < 828 then decide (23 ≤ count805 b) else (if i < 829 then decide (24 ≤ count805 b) else decide (25 ≤ count805 b))) else (if i < 832 then (if i < 831 then decide (26 ≤ count805 b) else decide (27 ≤ count805 b)) else (if i < 833 then decide (28 ≤ count805 b) else decide (29 ≤ count805 b))))))) else (if i < 862 then (if i < 848 then (if i < 841 then (if i < 837 then (if i < 835 then decide (30 ≤ count805 b) else (if i < 836 then decide (31 ≤ count805 b) else decide (32 ≤ count805 b))) else (if i < 839 then (if i < 838 then decide (33 ≤ count805 b) else decide (34 ≤ count805 b)) else (if i < 840 then decide (35 ≤ count805 b) else decide (36 ≤ count805 b)))) else (if i < 844 then (if i < 842 then decide (37 ≤ count805 b) else (if i < 843 then decide (38 ≤ count805 b) else decide (39 ≤ count805 b))) else (if i < 846 then (if i < 845 then decide (40 ≤ count805 b) else decide (41 ≤ count805 b)) else (if i < 847 then decide (42 ≤ count805 b) else decide (1 ≤ count847 b))))) else (if i < 855 then (if i < 851 then (if i < 849 then decide (2 ≤ count847 b) else (if i < 850 then decide (1 ≤ count849 b) else decide (2 ≤ count849 b))) else (if i < 853 then (if i < 852 then decide (1 ≤ count851 b) else decide (2 ≤ count851 b)) else (if i < 854 then decide (3 ≤ count851 b) else decide (4 ≤ count851 b)))) else (if i < 858 then (if i < 856 then decide (1 ≤ count855 b) else (if i < 857 then decide (2 ≤ count855 b) else decide (1 ≤ count857 b))) else (if i < 860 then (if i < 859 then decide (2 ≤ count857 b) else decide (1 ≤ count859 b)) else (if i < 861 then decide (2 ≤ count859 b) else decide (3 ≤ count859 b)))))) else (if i < 876 then (if i < 869 then (if i < 865 then (if i < 863 then decide (4 ≤ count859 b) else (if i < 864 then decide (1 ≤ count863 b) else decide (2 ≤ count863 b))) else (if i < 867 then (if i < 866 then decide (3 ≤ count863 b) else decide (4 ≤ count863 b)) else (if i < 868 then decide (5 ≤ count863 b) else decide (6 ≤ count863 b)))) else (if i < 872 then (if i < 870 then decide (7 ≤ count863 b) else (if i < 871 then decide (8 ≤ count863 b) else decide (1 ≤ count871 b))) else (if i < 874 then (if i < 873 then decide (2 ≤ count871 b) else decide (1 ≤ count873 b)) else (if i < 875 then decide (2 ≤ count873 b) else decide (1 ≤ count875 b))))) else (if i < 883 then (if i < 879 then (if i < 877 then decide (2 ≤ count875 b) else (if i < 878 then decide (3 ≤ count875 b) else decide (4 ≤ count875 b))) else (if i < 881 then (if i < 880 then decide (1 ≤ count879 b) else decide (2 ≤ count879 b)) else (if i < 882 then decide (1 ≤ count881 b) else decide (2 ≤ count881 b)))) else (if i < 886 then (if i < 884 then decide (1 ≤ count883 b) else (if i < 885 then decide (2 ≤ count883 b) else decide (3 ≤ count883 b))) else (if i < 888 then (if i < 887 then decide (4 ≤ count883 b) else decide (1 ≤ count887 b)) else (if i < 889 then decide (2 ≤ count887 b) else decide (3 ≤ count887 b))))))))))) else (if i < 1335 then (if i < 1112 then (if i < 1001 then (if i < 945 then (if i < 917 then (if i < 903 then (if i < 896 then (if i < 893 then (if i < 891 then decide (4 ≤ count887 b) else (if i < 892 then decide (5 ≤ count887 b) else decide (6 ≤ count887 b))) else (if i < 894 then decide (7 ≤ count887 b) else (if i < 895 then decide (8 ≤ count887 b) else decide (1 ≤ count895 b)))) else (if i < 899 then (if i < 897 then decide (2 ≤ count895 b) else (if i < 898 then decide (3 ≤ count895 b) else decide (4 ≤ count895 b))) else (if i < 901 then (if i < 900 then decide (5 ≤ count895 b) else decide (6 ≤ count895 b)) else (if i < 902 then decide (7 ≤ count895 b) else decide (8 ≤ count895 b))))) else (if i < 910 then (if i < 906 then (if i < 904 then decide (9 ≤ count895 b) else (if i < 905 then decide (10 ≤ count895 b) else decide (11 ≤ count895 b))) else (if i < 908 then (if i < 907 then decide (12 ≤ count895 b) else decide (13 ≤ count895 b)) else (if i < 909 then decide (14 ≤ count895 b) else decide (15 ≤ count895 b)))) else (if i < 913 then (if i < 911 then decide (16 ≤ count895 b) else (if i < 912 then decide (1 ≤ count911 b) else decide (2 ≤ count911 b))) else (if i < 915 then (if i < 914 then decide (1 ≤ count913 b) else decide (2 ≤ count913 b)) else (if i < 916 then decide (1 ≤ count915 b) else decide (2 ≤ count915 b)))))) else (if i < 931 then (if i < 924 then (if i < 920 then (if i < 918 then decide (3 ≤ count915 b) else (if i < 919 then decide (4 ≤ count915 b) else decide (1 ≤ count919 b))) else (if i < 922 then (if i < 921 then decide (2 ≤ count919 b) else decide (1 ≤ count921 b)) else (if i < 923 then decide (2 ≤ count921 b) else decide (1 ≤ count923 b)))) else (if i < 927 then (if i < 925 then decide (2 ≤ count923 b) else (if i < 926 then decide (3 ≤ count923 b) else decide (4 ≤ count923 b))) else (if i < 929 then (if i < 928 then decide (1 ≤ count927 b) else decide (2 ≤ count927 b)) else (if i < 930 then decide (3 ≤ count927 b) else decide (4 ≤ count927 b))))) else (if i < 938 then (if i < 934 then (if i < 932 then decide (5 ≤ count927 b) else (if i < 933 then decide (6 ≤ count927 b) else decide (7 ≤ count927 b))) else (if i < 936 then (if i < 935 then decide (8 ≤ count927 b) else decide (1 ≤ count935 b)) else (if i < 937 then decide (2 ≤ count935 b) else decide (1 ≤ count937 b)))) else (if i < 941 then (if i < 939 then decide (2 ≤ count937 b) else (if i < 940 then decide (1 ≤ count939 b) else decide (2 ≤ count939 b))) else (if i < 943 then (if i < 942 then decide (3 ≤ count939 b) else decide (4 ≤ count939 b)) else (if i < 944 then decide (1 ≤ count943 b) else decide (2 ≤ count943 b))))))) else (if i < 973 then (if i < 959 then (if i < 952 then (if i < 948 then (if i < 946 then decide (1 ≤ count945 b) else (if i < 947 then decide (2 ≤ count945 b) else decide (1 ≤ count947 b))) else (if i < 950 then (if i < 949 then decide (2 ≤ count947 b) else decide (3 ≤ count947 b)) else (if i < 951 then decide (4 ≤ count947 b) else decide (1 ≤ count951 b)))) else (if i < 955 then (if i < 953 then decide (2 ≤ count951 b) else (if i < 954 then decide (3 ≤ count951 b) else decide (4 ≤ count951 b))) else (if i < 957 then (if i < 956 then decide (5 ≤ count951 b) else decide (6 ≤ count951 b)) else (if i < 958 then decide (7 ≤ count951 b) else decide (8 ≤ count951 b))))) else (if i < 966 then (if i < 962 then (if i < 960 then decide (1 ≤ count959 b) else (if i < 961 then decide (2 ≤ count959 b) else decide (3 ≤ count959 b))) else (if i < 964 then (if i < 963 then decide (4 ≤ count959 b) else decide (5 ≤ count959 b)) else (if i < 965 then decide (6 ≤ count959 b) else decide (7 ≤ count959 b)))) else (if i < 969 then (if i < 967 then decide (8 ≤ count959 b) else (if i < 968 then decide (9 ≤ count959 b) else decide (10 ≤ count959 b))) else (if i < 971 then (if i < 970 then decide (11 ≤ count959 b) else decide (12 ≤ count959 b)) else (if i < 972 then decide (13 ≤ count959 b) else decide (14 ≤ count959 b)))))) else (if i < 987 then (if i < 980 then (if i < 976 then (if i < 974 then decide (15 ≤ count959 b) else (if i < 975 then decide (16 ≤ count959 b) else decide (1 ≤ count975 b))) else (if i < 978 then (if i < 977 then decide (2 ≤ count975 b) else decide (3 ≤ count975 b)) else (if i < 979 then decide (4 ≤ count975 b) else decide (5 ≤ count975 b)))) else (if i < 983 then (if i < 981 then decide (6 ≤ count975 b) else (if i < 982 then decide (7 ≤ count975 b) else decide (8 ≤ count975 b))) else (if i < 985 then (if i < 984 then decide (9 ≤ count975 b) else decide (10 ≤ count975 b)) else (if i < 986 then decide (11 ≤ count975 b) else decide (12 ≤ count975 b))))) else (if i < 994 then (if i < 990 then (if i < 988 then decide (13 ≤ count975 b) else (if i < 989 then decide (14 ≤ count975 b) else decide (15 ≤ count975 b))) else (if i < 992 then (if i < 991 then decide (16 ≤ count975 b) else decide (17 ≤ count975 b)) else (if i < 993 then decide (18 ≤ count975 b) else decide (19 ≤ count975 b)))) else (if i < 997 then (if i < 995 then decide (20 ≤ count975 b) else (if i < 996 then decide (21 ≤ count975 b) else decide (22 ≤ count975 b))) else (if i < 999 then (if i < 998 then decide (23 ≤ count975 b) else decide (24 ≤ count975 b)) else (if i < 1000 then decide (1 ≤ count999 b) else decide (2 ≤ count999 b)))))))) else (if i < 1056 then (if i < 1028 then (if i < 1014 then (if i < 1007 then (if i < 1004 then (if i < 1002 then decide (1 ≤ count1001 b) else (if i < 1003 then decide (2 ≤ count1001 b) else decide (1 ≤ count1003 b))) else (if i < 1005 then decide (2 ≤ count1003 b) else (if i < 1006 then decide (3 ≤ count1003 b) else decide (4 ≤ count1003 b)))) else (if i < 1010 then (if i < 1008 then decide (1 ≤ count1007 b) else (if i < 1009 then decide (2 ≤ count1007 b) else decide (1 ≤ count1009 b))) else (if i < 1012 then (if i < 1011 then decide (2 ≤ count1009 b) else decide (1 ≤ count1011 b)) else (if i < 1013 then decide (2 ≤ count1011 b) else decide (3 ≤ count1011 b))))) else (if i < 1021 then (if i < 1017 then (if i < 1015 then decide (4 ≤ count1011 b) else (if i < 1016 then decide (1 ≤ count1015 b) else decide (2 ≤ count1015 b))) else (if i < 1019 then (if i < 1018 then decide (3 ≤ count1015 b) else decide (4 ≤ count1015 b)) else (if i < 1020 then decide (5 ≤ count1015 b) else decide (6 ≤ count1015 b)))) else (if i < 1024 then (if i < 1022 then decide (7 ≤ count1015 b) else (if i < 1023 then decide (8 ≤ count1015 b) else decide (1 ≤ count1023 b))) else (if i < 1026 then (if i < 1025 then decide (2 ≤ count1023 b) else decide (1 ≤ count1025 b)) else (if i < 1027 then decide (2 ≤ count1025 b) else decide (1 ≤ count1027 b)))))) else (if i < 1042 then (if i < 1035 then (if i < 1031 then (if i < 1029 then decide (2 ≤ count1027 b) else (if i < 1030 then decide (3 ≤ count1027 b) else decide (4 ≤ count1027 b))) else (if i < 1033 then (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b)) else (if i < 1034 then decide (1 ≤ count1033 b) else decide (2 ≤ count1033 b)))) else (if i < 1038 then (if i < 1036 then decide (1 ≤ count1035 b) else (if i < 1037 then decide (2 ≤ count1035 b) else decide (3 ≤ count1035 b))) else (if i < 1040 then (if i < 1039 then decide (4 ≤ count1035 b) else decide (1 ≤ count1039 b)) else (if i < 1041 then decide (2 ≤ count1039 b) else decide (3 ≤ count1039 b))))) else (if i < 1049 then (if i < 1045 then (if i < 1043 then decide (4 ≤ count1039 b) else (if i < 1044 then decide (5 ≤ count1039 b) else decide (6 ≤ count1039 b))) else (if i < 1047 then (if i < 1046 then decide (7 ≤ count1039 b) else decide (8 ≤ count1039 b)) else (if i < 1048 then decide (1 ≤ count1047 b) else decide (2 ≤ count1047 b)))) else (if i < 1052 then (if i < 1050 then decide (3 ≤ count1047 b) else (if i < 1051 then decide (4 ≤ count1047 b) else decide (5 ≤ count1047 b))) else (if i < 1054 then (if i < 1053 then decide (6 ≤ count1047 b) else decide (7 ≤ count1047 b)) else (if i < 1055 then decide (8 ≤ count1047 b) else decide (9 ≤ count1047 b))))))) else (if i < 1084 then (if i < 1070 then (if i < 1063 then (if i < 1059 then (if i < 1057 then decide (10 ≤ count1047 b) else (if i < 1058 then decide (11 ≤ count1047 b) else decide (12 ≤ count1047 b))) else (if i < 1061 then (if i < 1060 then decide (13 ≤ count1047 b) else decide (14 ≤ count1047 b)) else (if i < 1062 then decide (15 ≤ count1047 b) else decide (16 ≤ count1047 b)))) else (if i < 1066 then (if i < 1064 then decide (1 ≤ count1063 b) else (if i < 1065 then decide (2 ≤ count1063 b) else decide (1 ≤ count1065 b))) else (if i < 1068 then (if i < 1067 then decide (2 ≤ count1065 b) else decide (1 ≤ count1067 b)) else (if i < 1069 then decide (2 ≤ count1067 b) else decide (3 ≤ count1067 b))))) else (if i < 1077 then (if i < 1073 then (if i < 1071 then decide (4 ≤ count1067 b) else (if i < 1072 then decide (1 ≤ count1071 b) else decide (2 ≤ count1071 b))) else (if i < 1075 then (if i < 1074 then decide (1 ≤ count1073 b) else decide (2 ≤ count1073 b)) else (if i < 1076 then decide (1 ≤ count1075 b) else decide (2 ≤ count1075 b)))) else (if i < 1080 then (if i < 1078 then decide (3 ≤ count1075 b) else (if i < 1079 then decide (4 ≤ count1075 b) else decide (1 ≤ count1079 b))) else (if i < 1082 then (if i < 1081 then decide (2 ≤ count1079 b) else decide (3 ≤ count1079 b)) else (if i < 1083 then decide (4 ≤ count1079 b) else decide (5 ≤ count1079 b)))))) else (if i < 1098 then (if i < 1091 then (if i < 1087 then (if i < 1085 then decide (6 ≤ count1079 b) else (if i < 1086 then decide (7 ≤ count1079 b) else decide (8 ≤ count1079 b))) else (if i < 1089 then (if i < 1088 then decide (1 ≤ count1087 b) else decide (2 ≤ count1087 b)) else (if i < 1090 then decide (1 ≤ count1089 b) else decide (2 ≤ count1089 b)))) else (if i < 1094 then (if i < 1092 then decide (1 ≤ count1091 b) else (if i < 1093 then decide (2 ≤ count1091 b) else decide (3 ≤ count1091 b))) else (if i < 1096 then (if i < 1095 then decide (4 ≤ count1091 b) else decide (1 ≤ count1095 b)) else (if i < 1097 then decide (2 ≤ count1095 b) else decide (1 ≤ count1097 b))))) else (if i < 1105 then (if i < 1101 then (if i < 1099 then decide (2 ≤ count1097 b) else (if i < 1100 then decide (1 ≤ count1099 b) else decide (2 ≤ count1099 b))) else (if i < 1103 then (if i < 1102 then decide (3 ≤ count1099 b) else decide (4 ≤ count1099 b)) else (if i < 1104 then decide (1 ≤ count1103 b) else decide (2 ≤ count1103 b)))) else (if i < 1108 then (if i < 1106 then decide (3 ≤ count1103 b) else (if i < 1107 then decide (4 ≤ count1103 b) else decide (5 ≤ count1103 b))) else (if i < 1110 then (if i < 1109 then decide (6 ≤ count1103 b) else decide (7 ≤ count1103 b)) else (if i < 1111 then decide (8 ≤ count1103 b) else decide (1 ≤ count1111 b))))))))) else (if i < 1223 then (if i < 1167 then (if i < 1139 then (if i < 1125 then (if i < 1118 then (if i < 1115 then (if i < 1113 then decide (2 ≤ count1111 b) else (if i < 1114 then decide (3 ≤ count1111 b) else decide (4 ≤ count1111 b))) else (if i < 1116 then decide (5 ≤ count1111 b) else (if i < 1117 then decide (6 ≤ count1111 b) else decide (7 ≤ count1111 b)))) else (if i < 1121 then (if i < 1119 then decide (8 ≤ count1111 b) else (if i < 1120 then decide (9 ≤ count1111 b) else decide (10 ≤ count1111 b))) else (if i < 1123 then (if i < 1122 then decide (11 ≤ count1111 b) else decide (12 ≤ count1111 b)) else (if i < 1124 then decide (13 ≤ count1111 b) else decide (14 ≤ count1111 b))))) else (if i < 1132 then (if i < 1128 then (if i < 1126 then decide (15 ≤ count1111 b) else (if i < 1127 then decide (16 ≤ count1111 b) else decide (1 ≤ count1127 b))) else (if i < 1130 then (if i < 1129 then decide (2 ≤ count1127 b) else decide (3 ≤ count1127 b)) else (if i < 1131 then decide (4 ≤ count1127 b) else decide (5 ≤ count1127 b)))) else (if i < 1135 then (if i < 1133 then decide (6 ≤ count1127 b) else (if i < 1134 then decide (7 ≤ count1127 b) else decide (8 ≤ count1127 b))) else (if i < 1137 then (if i < 1136 then decide (9 ≤ count1127 b) else decide (10 ≤ count1127 b)) else (if i < 1138 then decide (11 ≤ count1127 b) else decide (12 ≤ count1127 b)))))) else (if i < 1153 then (if i < 1146 then (if i < 1142 then (if i < 1140 then decide (13 ≤ count1127 b) else (if i < 1141 then decide (14 ≤ count1127 b) else decide (15 ≤ count1127 b))) else (if i < 1144 then (if i < 1143 then decide (16 ≤ count1127 b) else decide (17 ≤ count1127 b)) else (if i < 1145 then decide (18 ≤ count1127 b) else decide (19 ≤ count1127 b)))) else (if i < 1149 then (if i < 1147 then decide (20 ≤ count1127 b) else (if i < 1148 then decide (21 ≤ count1127 b) else decide (22 ≤ count1127 b))) else (if i < 1151 then (if i < 1150 then decide (23 ≤ count1127 b) else decide (24 ≤ count1127 b)) else (if i < 1152 then decide (1 ≤ count1151 b) else decide (2 ≤ count1151 b))))) else (if i < 1160 then (if i < 1156 then (if i < 1154 then decide (3 ≤ count1151 b) else (if i < 1155 then decide (4 ≤ count1151 b) else decide (5 ≤ count1151 b))) else (if i < 1158 then (if i < 1157 then decide (6 ≤ count1151 b) else decide (7 ≤ count1151 b)) else (if i < 1159 then decide (8 ≤ count1151 b) else decide (9 ≤ count1151 b)))) else (if i < 1163 then (if i < 1161 then decide (10 ≤ count1151 b) else (if i < 1162 then decide (11 ≤ count1151 b) else decide (12 ≤ count1151 b))) else (if i < 1165 then (if i < 1164 then decide (13 ≤ count1151 b) else decide (14 ≤ count1151 b)) else (if i < 1166 then decide (15 ≤ count1151 b) else decide (16 ≤ count1151 b))))))) else (if i < 1195 then (if i < 1181 then (if i < 1174 then (if i < 1170 then (if i < 1168 then decide (17 ≤ count1151 b) else (if i < 1169 then decide (18 ≤ count1151 b) else decide (19 ≤ count1151 b))) else (if i < 1172 then (if i < 1171 then decide (20 ≤ count1151 b) else decide (21 ≤ count1151 b)) else (if i < 1173 then decide (22 ≤ count1151 b) else decide (23 ≤ count1151 b)))) else (if i < 1177 then (if i < 1175 then decide (24 ≤ count1151 b) else (if i < 1176 then decide (1 ≤ count1175 b) else decide (2 ≤ count1175 b))) else (if i < 1179 then (if i < 1178 then decide (1 ≤ count1177 b) else decide (2 ≤ count1177 b)) else (if i < 1180 then decide (3 ≤ count1177 b) else decide (1 ≤ count1180 b))))) else (if i < 1188 then (if i < 1184 then (if i < 1182 then decide (2 ≤ count1180 b) else (if i < 1183 then decide (1 ≤ count1182 b) else decide (2 ≤ count1182 b))) else (if i < 1186 then (if i < 1185 then decide (1 ≤ count1184 b) else decide (2 ≤ count1184 b)) else (if i < 1187 then decide (3 ≤ count1184 b) else decide (4 ≤ count1184 b)))) else (if i < 1191 then (if i < 1189 then decide (1 ≤ count1188 b) else (if i < 1190 then decide (2 ≤ count1188 b) else decide (3 ≤ count1188 b))) else (if i < 1193 then (if i < 1192 then decide (4 ≤ count1188 b) else decide (5 ≤ count1188 b)) else (if i < 1194 then decide (6 ≤ count1188 b) else decide (7 ≤ count1188 b)))))) else (if i < 1209 then (if i < 1202 then (if i < 1198 then (if i < 1196 then decide (1 ≤ count1195 b) else (if i < 1197 then decide (2 ≤ count1195 b) else decide (1 ≤ count1197 b))) else (if i < 1200 then (if i < 1199 then decide (2 ≤ count1197 b) else decide (3 ≤ count1197 b)) else (if i < 1201 then decide (1 ≤ count1200 b) else decide (2 ≤ count1200 b)))) else (if i < 1205 then (if i < 1203 then decide (1 ≤ count1202 b) else (if i < 1204 then decide (2 ≤ count1202 b) else decide (1 ≤ count1204 b))) else (if i < 1207 then (if i < 1206 then decide (2 ≤ count1204 b) else decide (3 ≤ count1204 b)) else (if i < 1208 then decide (4 ≤ count1204 b) else decide (1 ≤ count1208 b))))) else (if i < 1216 then (if i < 1212 then (if i < 1210 then decide (2 ≤ count1208 b) else (if i < 1211 then decide (3 ≤ count1208 b) else decide (4 ≤ count1208 b))) else (if i < 1214 then (if i < 1213 then decide (5 ≤ count1208 b) else decide (6 ≤ count1208 b)) else (if i < 1215 then decide (7 ≤ count1208 b) else decide (1 ≤ count1215 b)))) else (if i < 1219 then (if i < 1217 then decide (2 ≤ count1215 b) else (if i < 1218 then decide (3 ≤ count1215 b) else decide (4 ≤ count1215 b))) else (if i < 1221 then (if i < 1220 then decide (5 ≤ count1215 b) else decide (6 ≤ count1215 b)) else (if i < 1222 then decide (7 ≤ count1215 b) else decide (8 ≤ count1215 b)))))))) else (if i < 1279 then (if i < 1251 then (if i < 1237 then (if i < 1230 then (if i < 1226 then (if i < 1224 then decide (9 ≤ count1215 b) else (if i < 1225 then decide (10 ≤ count1215 b) else decide (11 ≤ count1215 b))) else (if i < 1228 then (if i < 1227 then decide (12 ≤ count1215 b) else decide (13 ≤ count1215 b)) else (if i < 1229 then decide (14 ≤ count1215 b) else decide (1 ≤ count1229 b)))) else (if i < 1233 then (if i < 1231 then decide (2 ≤ count1229 b) else (if i < 1232 then decide (1 ≤ count1231 b) else decide (2 ≤ count1231 b))) else (if i < 1235 then (if i < 1234 then decide (3 ≤ count1231 b) else decide (1 ≤ count1234 b)) else (if i < 1236 then decide (2 ≤ count1234 b) else decide (1 ≤ count1236 b))))) else (if i < 1244 then (if i < 1240 then (if i < 1238 then decide (2 ≤ count1236 b) else (if i < 1239 then decide (1 ≤ count1238 b) else decide (2 ≤ count1238 b))) else (if i < 1242 then (if i < 1241 then decide (3 ≤ count1238 b) else decide (4 ≤ count1238 b)) else (if i < 1243 then decide (1 ≤ count1242 b) else decide (2 ≤ count1242 b)))) else (if i < 1247 then (if i < 1245 then decide (3 ≤ count1242 b) else (if i < 1246 then decide (4 ≤ count1242 b) else decide (5 ≤ count1242 b))) else (if i < 1249 then (if i < 1248 then decide (6 ≤ count1242 b) else decide (7 ≤ count1242 b)) else (if i < 1250 then decide (1 ≤ count1249 b) else decide (2 ≤ count1249 b)))))) else (if i < 1265 then (if i < 1258 then (if i < 1254 then (if i < 1252 then decide (1 ≤ count1251 b) else (if i < 1253 then decide (2 ≤ count1251 b) else decide (1 ≤ count1253 b))) else (if i < 1256 then (if i < 1255 then decide (2 ≤ count1253 b) else decide (3 ≤ count1253 b)) else (if i < 1257 then decide (4 ≤ count1253 b) else decide (1 ≤ count1257 b)))) else (if i < 1261 then (if i < 1259 then decide (2 ≤ count1257 b) else (if i < 1260 then decide (1 ≤ count1259 b) else decide (2 ≤ count1259 b))) else (if i < 1263 then (if i < 1262 then decide (1 ≤ count1261 b) else decide (2 ≤ count1261 b)) else (if i < 1264 then decide (3 ≤ count1261 b) else decide (4 ≤ count1261 b))))) else (if i < 1272 then (if i < 1268 then (if i < 1266 then decide (1 ≤ count1265 b) else (if i < 1267 then decide (2 ≤ count1265 b) else decide (3 ≤ count1265 b))) else (if i < 1270 then (if i < 1269 then decide (4 ≤ count1265 b) else decide (5 ≤ count1265 b)) else (if i < 1271 then decide (6 ≤ count1265 b) else decide (7 ≤ count1265 b)))) else (if i < 1275 then (if i < 1273 then decide (8 ≤ count1265 b) else (if i < 1274 then decide (1 ≤ count1273 b) else decide (2 ≤ count1273 b))) else (if i < 1277 then (if i < 1276 then decide (3 ≤ count1273 b) else decide (4 ≤ count1273 b)) else (if i < 1278 then decide (5 ≤ count1273 b) else decide (6 ≤ count1273 b))))))) else (if i < 1307 then (if i < 1293 then (if i < 1286 then (if i < 1282 then (if i < 1280 then decide (7 ≤ count1273 b) else (if i < 1281 then decide (8 ≤ count1273 b) else decide (9 ≤ count1273 b))) else (if i < 1284 then (if i < 1283 then decide (10 ≤ count1273 b) else decide (11 ≤ count1273 b)) else (if i < 1285 then decide (12 ≤ count1273 b) else decide (13 ≤ count1273 b)))) else (if i < 1289 then (if i < 1287 then decide (14 ≤ count1273 b) else (if i < 1288 then decide (15 ≤ count1273 b) else decide (1 ≤ count1288 b))) else (if i < 1291 then (if i < 1290 then decide (2 ≤ count1288 b) else decide (3 ≤ count1288 b)) else (if i < 1292 then decide (4 ≤ count1288 b) else decide (5 ≤ count1288 b))))) else (if i < 1300 then (if i < 1296 then (if i < 1294 then decide (6 ≤ count1288 b) else (if i < 1295 then decide (7 ≤ count1288 b) else decide (8 ≤ count1288 b))) else (if i < 1298 then (if i < 1297 then decide (9 ≤ count1288 b) else decide (10 ≤ count1288 b)) else (if i < 1299 then decide (11 ≤ count1288 b) else decide (12 ≤ count1288 b)))) else (if i < 1303 then (if i < 1301 then decide (13 ≤ count1288 b) else (if i < 1302 then decide (14 ≤ count1288 b) else decide (15 ≤ count1288 b))) else (if i < 1305 then (if i < 1304 then decide (16 ≤ count1288 b) else decide (17 ≤ count1288 b)) else (if i < 1306 then decide (18 ≤ count1288 b) else decide (19 ≤ count1288 b)))))) else (if i < 1321 then (if i < 1314 then (if i < 1310 then (if i < 1308 then decide (20 ≤ count1288 b) else (if i < 1309 then decide (21 ≤ count1288 b) else decide (22 ≤ count1288 b))) else (if i < 1312 then (if i < 1311 then decide (23 ≤ count1288 b) else decide (24 ≤ count1288 b)) else (if i < 1313 then decide (25 ≤ count1288 b) else decide (26 ≤ count1288 b)))) else (if i < 1317 then (if i < 1315 then decide (27 ≤ count1288 b) else (if i < 1316 then decide (28 ≤ count1288 b) else decide (29 ≤ count1288 b))) else (if i < 1319 then (if i < 1318 then decide (1 ≤ count1317 b) else decide (2 ≤ count1317 b)) else (if i < 1320 then decide (1 ≤ count1319 b) else decide (2 ≤ count1319 b))))) else (if i < 1328 then (if i < 1324 then (if i < 1322 then decide (3 ≤ count1319 b) else (if i < 1323 then decide (1 ≤ count1322 b) else decide (2 ≤ count1322 b))) else (if i < 1326 then (if i < 1325 then decide (1 ≤ count1324 b) else decide (2 ≤ count1324 b)) else (if i < 1327 then decide (1 ≤ count1326 b) else decide (2 ≤ count1326 b)))) else (if i < 1331 then (if i < 1329 then decide (3 ≤ count1326 b) else (if i < 1330 then decide (4 ≤ count1326 b) else decide (1 ≤ count1330 b))) else (if i < 1333 then (if i < 1332 then decide (2 ≤ count1330 b) else decide (3 ≤ count1330 b)) else (if i < 1334 then decide (4 ≤ count1330 b) else decide (5 ≤ count1330 b)))))))))) else (if i < 1558 then (if i < 1446 then (if i < 1390 then (if i < 1362 then (if i < 1348 then (if i < 1341 then (if i < 1338 then (if i < 1336 then decide (6 ≤ count1330 b) else (if i < 1337 then decide (7 ≤ count1330 b) else decide (1 ≤ count1337 b))) else (if i < 1339 then decide (2 ≤ count1337 b) else (if i < 1340 then decide (1 ≤ count1339 b) else decide (2 ≤ count1339 b)))) else (if i < 1344 then (if i < 1342 then decide (3 ≤ count1339 b) else (if i < 1343 then decide (1 ≤ count1342 b) else decide (2 ≤ count1342 b))) else (if i < 1346 then (if i < 1345 then decide (1 ≤ count1344 b) else decide (2 ≤ count1344 b)) else (if i < 1347 then decide (1 ≤ count1346 b) else decide (2 ≤ count1346 b))))) else (if i < 1355 then (if i < 1351 then (if i < 1349 then decide (3 ≤ count1346 b) else (if i < 1350 then decide (4 ≤ count1346 b) else decide (1 ≤ count1350 b))) else (if i < 1353 then (if i < 1352 then decide (2 ≤ count1350 b) else decide (3 ≤ count1350 b)) else (if i < 1354 then decide (4 ≤ count1350 b) else decide (5 ≤ count1350 b)))) else (if i < 1358 then (if i < 1356 then decide (6 ≤ count1350 b) else (if i < 1357 then decide (7 ≤ count1350 b) else decide (1 ≤ count1357 b))) else (if i < 1360 then (if i < 1359 then decide (2 ≤ count1357 b) else decide (3 ≤ count1357 b)) else (if i < 1361 then decide (4 ≤ count1357 b) else decide (5 ≤ count1357 b)))))) else (if i < 1376 then (if i < 1369 then (if i < 1365 then (if i < 1363 then decide (6 ≤ count1357 b) else (if i < 1364 then decide (7 ≤ count1357 b) else decide (8 ≤ count1357 b))) else (if i < 1367 then (if i < 1366 then decide (9 ≤ count1357 b) else decide (10 ≤ count1357 b)) else (if i < 1368 then decide (11 ≤ count1357 b) else decide (12 ≤ count1357 b)))) else (if i < 1372 then (if i < 1370 then decide (13 ≤ count1357 b) else (if i < 1371 then decide (14 ≤ count1357 b) else decide (1 ≤ count1371 b))) else (if i < 1374 then (if i < 1373 then decide (2 ≤ count1371 b) else decide (1 ≤ count1373 b)) else (if i < 1375 then decide (2 ≤ count1373 b) else decide (3 ≤ count1373 b))))) else (if i < 1383 then (if i < 1379 then (if i < 1377 then decide (1 ≤ count1376 b) else (if i < 1378 then decide (2 ≤ count1376 b) else decide (1 ≤ count1378 b))) else (if i < 1381 then (if i < 1380 then decide (2 ≤ count1378 b) else decide (1 ≤ count1380 b)) else (if i < 1382 then decide (2 ≤ count1380 b) else decide (3 ≤ count1380 b)))) else (if i < 1386 then (if i < 1384 then decide (4 ≤ count1380 b) else (if i < 1385 then decide (1 ≤ count1384 b) else decide (2 ≤ count1384 b))) else (if i < 1388 then (if i < 1387 then decide (3 ≤ count1384 b) else decide (4 ≤ count1384 b)) else (if i < 1389 then decide (5 ≤ count1384 b) else decide (6 ≤ count1384 b))))))) else (if i < 1418 then (if i < 1404 then (if i < 1397 then (if i < 1393 then (if i < 1391 then decide (7 ≤ count1384 b) else (if i < 1392 then decide (1 ≤ count1391 b) else decide (2 ≤ count1391 b))) else (if i < 1395 then (if i < 1394 then decide (1 ≤ count1393 b) else decide (2 ≤ count1393 b)) else (if i < 1396 then decide (1 ≤ count1395 b) else decide (2 ≤ count1395 b)))) else (if i < 1400 then (if i < 1398 then decide (3 ≤ count1395 b) else (if i < 1399 then decide (4 ≤ count1395 b) else decide (1 ≤ count1399 b))) else (if i < 1402 then (if i < 1401 then decide (2 ≤ count1399 b) else decide (1 ≤ count1401 b)) else (if i < 1403 then decide (2 ≤ count1401 b) else decide (1 ≤ count1403 b))))) else (if i < 1411 then (if i < 1407 then (if i < 1405 then decide (2 ≤ count1403 b) else (if i < 1406 then decide (3 ≤ count1403 b) else decide (4 ≤ count1403 b))) else (if i < 1409 then (if i < 1408 then decide (1 ≤ count1407 b) else decide (2 ≤ count1407 b)) else (if i < 1410 then decide (3 ≤ count1407 b) else decide (4 ≤ count1407 b)))) else (if i < 1414 then (if i < 1412 then decide (5 ≤ count1407 b) else (if i < 1413 then decide (6 ≤ count1407 b) else decide (7 ≤ count1407 b))) else (if i < 1416 then (if i < 1415 then decide (8 ≤ count1407 b) else decide (1 ≤ count1415 b)) else (if i < 1417 then decide (2 ≤ count1415 b) else decide (3 ≤ count1415 b)))))) else (if i < 1432 then (if i < 1425 then (if i < 1421 then (if i < 1419 then decide (4 ≤ count1415 b) else (if i < 1420 then decide (5 ≤ count1415 b) else decide (6 ≤ count1415 b))) else (if i < 1423 then (if i < 1422 then decide (7 ≤ count1415 b) else decide (8 ≤ count1415 b)) else (if i < 1424 then decide (9 ≤ count1415 b) else decide (10 ≤ count1415 b)))) else (if i < 1428 then (if i < 1426 then decide (11 ≤ count1415 b) else (if i < 1427 then decide (12 ≤ count1415 b) else decide (13 ≤ count1415 b))) else (if i < 1430 then (if i < 1429 then decide (14 ≤ count1415 b) else decide (15 ≤ count1415 b)) else (if i < 1431 then decide (1 ≤ count1430 b) else decide (2 ≤ count1430 b))))) else (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (3 ≤ count1430 b) else (if i < 1434 then decide (4 ≤ count1430 b) else decide (5 ≤ count1430 b))) else (if i < 1437 then (if i < 1436 then decide (6 ≤ count1430 b) else decide (7 ≤ count1430 b)) else (if i < 1438 then decide (8 ≤ count1430 b) else decide (9 ≤ count1430 b)))) else (if i < 1442 then (if i < 1440 then decide (10 ≤ count1430 b) else (if i < 1441 then decide (11 ≤ count1430 b) else decide (12 ≤ count1430 b))) else (if i < 1444 then (if i < 1443 then decide (13 ≤ count1430 b) else decide (14 ≤ count1430 b)) else (if i < 1445 then decide (15 ≤ count1430 b) else decide (16 ≤ count1430 b)))))))) else (if i < 1502 then (if i < 1474 then (if i < 1460 then (if i < 1453 then (if i < 1449 then (if i < 1447 then decide (17 ≤ count1430 b) else (if i < 1448 then decide (18 ≤ count1430 b) else decide (19 ≤ count1430 b))) else (if i < 1451 then (if i < 1450 then decide (20 ≤ count1430 b) else decide (21 ≤ count1430 b)) else (if i < 1452 then decide (22 ≤ count1430 b) else decide (23 ≤ count1430 b)))) else (if i < 1456 then (if i < 1454 then decide (24 ≤ count1430 b) else (if i < 1455 then decide (25 ≤ count1430 b) else decide (26 ≤ count1430 b))) else (if i < 1458 then (if i < 1457 then decide (27 ≤ count1430 b) else decide (28 ≤ count1430 b)) else (if i < 1459 then decide (29 ≤ count1430 b) else decide (1 ≤ count1459 b))))) else (if i < 1467 then (if i < 1463 then (if i < 1461 then decide (2 ≤ count1459 b) else (if i < 1462 then decide (3 ≤ count1459 b) else decide (4 ≤ count1459 b))) else (if i < 1465 then (if i < 1464 then decide (5 ≤ count1459 b) else decide (6 ≤ count1459 b)) else (if i < 1466 then decide (7 ≤ count1459 b) else decide (8 ≤ count1459 b)))) else (if i < 1470 then (if i < 1468 then decide (9 ≤ count1459 b) else (if i < 1469 then decide (10 ≤ count1459 b) else decide (11 ≤ count1459 b))) else (if i < 1472 then (if i < 1471 then decide (12 ≤ count1459 b) else decide (13 ≤ count1459 b)) else (if i < 1473 then decide (14 ≤ count1459 b) else decide (15 ≤ count1459 b)))))) else (if i < 1488 then (if i < 1481 then (if i < 1477 then (if i < 1475 then decide (16 ≤ count1459 b) else (if i < 1476 then decide (17 ≤ count1459 b) else decide (18 ≤ count1459 b))) else (if i < 1479 then (if i < 1478 then decide (19 ≤ count1459 b) else decide (20 ≤ count1459 b)) else (if i < 1480 then decide (21 ≤ count1459 b) else decide (22 ≤ count1459 b)))) else (if i < 1484 then (if i < 1482 then decide (23 ≤ count1459 b) else (if i < 1483 then decide (24 ≤ count1459 b) else decide (25 ≤ count1459 b))) else (if i < 1486 then (if i < 1485 then decide (26 ≤ count1459 b) else decide (27 ≤ count1459 b)) else (if i < 1487 then decide (28 ≤ count1459 b) else decide (29 ≤ count1459 b))))) else (if i < 1495 then (if i < 1491 then (if i < 1489 then decide (30 ≤ count1459 b) else (if i < 1490 then decide (31 ≤ count1459 b) else decide (32 ≤ count1459 b))) else (if i < 1493 then (if i < 1492 then decide (33 ≤ count1459 b) else decide (34 ≤ count1459 b)) else (if i < 1494 then decide (35 ≤ count1459 b) else decide (36 ≤ count1459 b)))) else (if i < 1498 then (if i < 1496 then decide (37 ≤ count1459 b) else (if i < 1497 then decide (38 ≤ count1459 b) else decide (39 ≤ count1459 b))) else (if i < 1500 then (if i < 1499 then decide (40 ≤ count1459 b) else decide (41 ≤ count1459 b)) else (if i < 1501 then decide (42 ≤ count1459 b) else decide (1 ≤ count1501 b))))))) else (if i < 1530 then (if i < 1516 then (if i < 1509 then (if i < 1505 then (if i < 1503 then decide (2 ≤ count1501 b) else (if i < 1504 then decide (1 ≤ count1503 b) else decide (2 ≤ count1503 b))) else (if i < 1507 then (if i < 1506 then decide (3 ≤ count1503 b) else decide (1 ≤ count1506 b)) else (if i < 1508 then decide (2 ≤ count1506 b) else decide (1 ≤ count1508 b)))) else (if i < 1512 then (if i < 1510 then decide (2 ≤ count1508 b) else (if i < 1511 then decide (1 ≤ count1510 b) else decide (2 ≤ count1510 b))) else (if i < 1514 then (if i < 1513 then decide (3 ≤ count1510 b) else decide (4 ≤ count1510 b)) else (if i < 1515 then decide (1 ≤ count1514 b) else decide (2 ≤ count1514 b))))) else (if i < 1523 then (if i < 1519 then (if i < 1517 then decide (3 ≤ count1514 b) else (if i < 1518 then decide (4 ≤ count1514 b) else decide (5 ≤ count1514 b))) else (if i < 1521 then (if i < 1520 then decide (6 ≤ count1514 b) else decide (7 ≤ count1514 b)) else (if i < 1522 then decide (1 ≤ count1521 b) else decide (2 ≤ count1521 b)))) else (if i < 1526 then (if i < 1524 then decide (1 ≤ count1523 b) else (if i < 1525 then decide (2 ≤ count1523 b) else decide (3 ≤ count1523 b))) else (if i < 1528 then (if i < 1527 then decide (1 ≤ count1526 b) else decide (2 ≤ count1526 b)) else (if i < 1529 then decide (1 ≤ count1528 b) else decide (2 ≤ count1528 b)))))) else (if i < 1544 then (if i < 1537 then (if i < 1533 then (if i < 1531 then decide (1 ≤ count1530 b) else (if i < 1532 then decide (2 ≤ count1530 b) else decide (3 ≤ count1530 b))) else (if i < 1535 then (if i < 1534 then decide (4 ≤ count1530 b) else decide (1 ≤ count1534 b)) else (if i < 1536 then decide (2 ≤ count1534 b) else decide (3 ≤ count1534 b)))) else (if i < 1540 then (if i < 1538 then decide (4 ≤ count1534 b) else (if i < 1539 then decide (5 ≤ count1534 b) else decide (6 ≤ count1534 b))) else (if i < 1542 then (if i < 1541 then decide (7 ≤ count1534 b) else decide (1 ≤ count1541 b)) else (if i < 1543 then decide (2 ≤ count1541 b) else decide (3 ≤ count1541 b))))) else (if i < 1551 then (if i < 1547 then (if i < 1545 then decide (4 ≤ count1541 b) else (if i < 1546 then decide (5 ≤ count1541 b) else decide (6 ≤ count1541 b))) else (if i < 1549 then (if i < 1548 then decide (7 ≤ count1541 b) else decide (8 ≤ count1541 b)) else (if i < 1550 then decide (9 ≤ count1541 b) else decide (10 ≤ count1541 b)))) else (if i < 1554 then (if i < 1552 then decide (11 ≤ count1541 b) else (if i < 1553 then decide (12 ≤ count1541 b) else decide (13 ≤ count1541 b))) else (if i < 1556 then (if i < 1555 then decide (14 ≤ count1541 b) else decide (1 ≤ count1555 b)) else (if i < 1557 then decide (2 ≤ count1555 b) else decide (1 ≤ count1557 b))))))))) else (if i < 1669 then (if i < 1613 then (if i < 1585 then (if i < 1571 then (if i < 1564 then (if i < 1561 then (if i < 1559 then decide (2 ≤ count1557 b) else (if i < 1560 then decide (3 ≤ count1557 b) else decide (1 ≤ count1560 b))) else (if i < 1562 then decide (2 ≤ count1560 b) else (if i < 1563 then decide (1 ≤ count1562 b) else decide (2 ≤ count1562 b)))) else (if i < 1567 then (if i < 1565 then decide (1 ≤ count1564 b) else (if i < 1566 then decide (2 ≤ count1564 b) else decide (3 ≤ count1564 b))) else (if i < 1569 then (if i < 1568 then decide (4 ≤ count1564 b) else decide (1 ≤ count1568 b)) else (if i < 1570 then decide (2 ≤ count1568 b) else decide (3 ≤ count1568 b))))) else (if i < 1578 then (if i < 1574 then (if i < 1572 then decide (4 ≤ count1568 b) else (if i < 1573 then decide (5 ≤ count1568 b) else decide (6 ≤ count1568 b))) else (if i < 1576 then (if i < 1575 then decide (7 ≤ count1568 b) else decide (1 ≤ count1575 b)) else (if i < 1577 then decide (2 ≤ count1575 b) else decide (1 ≤ count1577 b)))) else (if i < 1581 then (if i < 1579 then decide (2 ≤ count1577 b) else (if i < 1580 then decide (1 ≤ count1579 b) else decide (2 ≤ count1579 b))) else (if i < 1583 then (if i < 1582 then decide (3 ≤ count1579 b) else decide (4 ≤ count1579 b)) else (if i < 1584 then decide (1 ≤ count1583 b) else decide (2 ≤ count1583 b)))))) else (if i < 1599 then (if i < 1592 then (if i < 1588 then (if i < 1586 then decide (1 ≤ count1585 b) else (if i < 1587 then decide (2 ≤ count1585 b) else decide (1 ≤ count1587 b))) else (if i < 1590 then (if i < 1589 then decide (2 ≤ count1587 b) else decide (3 ≤ count1587 b)) else (if i < 1591 then decide (4 ≤ count1587 b) else decide (1 ≤ count1591 b)))) else (if i < 1595 then (if i < 1593 then decide (2 ≤ count1591 b) else (if i < 1594 then decide (3 ≤ count1591 b) else decide (4 ≤ count1591 b))) else (if i < 1597 then (if i < 1596 then decide (5 ≤ count1591 b) else decide (6 ≤ count1591 b)) else (if i < 1598 then decide (7 ≤ count1591 b) else decide (8 ≤ count1591 b))))) else (if i < 1606 then (if i < 1602 then (if i < 1600 then decide (1 ≤ count1599 b) else (if i < 1601 then decide (2 ≤ count1599 b) else decide (3 ≤ count1599 b))) else (if i < 1604 then (if i < 1603 then decide (4 ≤ count1599 b) else decide (5 ≤ count1599 b)) else (if i < 1605 then decide (6 ≤ count1599 b) else decide (7 ≤ count1599 b)))) else (if i < 1609 then (if i < 1607 then decide (8 ≤ count1599 b) else (if i < 1608 then decide (9 ≤ count1599 b) else decide (10 ≤ count1599 b))) else (if i < 1611 then (if i < 1610 then decide (11 ≤ count1599 b) else decide (12 ≤ count1599 b)) else (if i < 1612 then decide (13 ≤ count1599 b) else decide (14 ≤ count1599 b))))))) else (if i < 1641 then (if i < 1627 then (if i < 1620 then (if i < 1616 then (if i < 1614 then decide (15 ≤ count1599 b) else (if i < 1615 then decide (1 ≤ count1614 b) else decide (2 ≤ count1614 b))) else (if i < 1618 then (if i < 1617 then decide (3 ≤ count1614 b) else decide (4 ≤ count1614 b)) else (if i < 1619 then decide (5 ≤ count1614 b) else decide (6 ≤ count1614 b)))) else (if i < 1623 then (if i < 1621 then decide (7 ≤ count1614 b) else (if i < 1622 then decide (8 ≤ count1614 b) else decide (9 ≤ count1614 b))) else (if i < 1625 then (if i < 1624 then decide (10 ≤ count1614 b) else decide (11 ≤ count1614 b)) else (if i < 1626 then decide (12 ≤ count1614 b) else decide (13 ≤ count1614 b))))) else (if i < 1634 then (if i < 1630 then (if i < 1628 then decide (14 ≤ count1614 b) else (if i < 1629 then decide (15 ≤ count1614 b) else decide (16 ≤ count1614 b))) else (if i < 1632 then (if i < 1631 then decide (17 ≤ count1614 b) else decide (18 ≤ count1614 b)) else (if i < 1633 then decide (1 ≤ count1632 b) else decide (2 ≤ count1632 b)))) else (if i < 1637 then (if i < 1635 then decide (1 ≤ count1634 b) else (if i < 1636 then decide (2 ≤ count1634 b) else decide (3 ≤ count1634 b))) else (if i < 1639 then (if i < 1638 then decide (1 ≤ count1637 b) else decide (2 ≤ count1637 b)) else (if i < 1640 then decide (1 ≤ count1639 b) else decide (2 ≤ count1639 b)))))) else (if i < 1655 then (if i < 1648 then (if i < 1644 then (if i < 1642 then decide (1 ≤ count1641 b) else (if i < 1643 then decide (2 ≤ count1641 b) else decide (3 ≤ count1641 b))) else (if i < 1646 then (if i < 1645 then decide (4 ≤ count1641 b) else decide (1 ≤ count1645 b)) else (if i < 1647 then decide (2 ≤ count1645 b) else decide (3 ≤ count1645 b)))) else (if i < 1651 then (if i < 1649 then decide (4 ≤ count1645 b) else (if i < 1650 then decide (5 ≤ count1645 b) else decide (6 ≤ count1645 b))) else (if i < 1653 then (if i < 1652 then decide (7 ≤ count1645 b) else decide (1 ≤ count1652 b)) else (if i < 1654 then decide (2 ≤ count1652 b) else decide (1 ≤ count1654 b))))) else (if i < 1662 then (if i < 1658 then (if i < 1656 then decide (2 ≤ count1654 b) else (if i < 1657 then decide (3 ≤ count1654 b) else decide (1 ≤ count1657 b))) else (if i < 1660 then (if i < 1659 then decide (2 ≤ count1657 b) else decide (1 ≤ count1659 b)) else (if i < 1661 then decide (2 ≤ count1659 b) else decide (1 ≤ count1661 b)))) else (if i < 1665 then (if i < 1663 then decide (2 ≤ count1661 b) else (if i < 1664 then decide (3 ≤ count1661 b) else decide (4 ≤ count1661 b))) else (if i < 1667 then (if i < 1666 then decide (1 ≤ count1665 b) else decide (2 ≤ count1665 b)) else (if i < 1668 then decide (3 ≤ count1665 b) else decide (4 ≤ count1665 b)))))))) else (if i < 1725 then (if i < 1697 then (if i < 1683 then (if i < 1676 then (if i < 1672 then (if i < 1670 then decide (5 ≤ count1665 b) else (if i < 1671 then decide (6 ≤ count1665 b) else decide (7 ≤ count1665 b))) else (if i < 1674 then (if i < 1673 then decide (1 ≤ count1672 b) else decide (2 ≤ count1672 b)) else (if i < 1675 then decide (3 ≤ count1672 b) else decide (4 ≤ count1672 b)))) else (if i < 1679 then (if i < 1677 then decide (5 ≤ count1672 b) else (if i < 1678 then decide (6 ≤ count1672 b) else decide (7 ≤ count1672 b))) else (if i < 1681 then (if i < 1680 then decide (8 ≤ count1672 b) else decide (9 ≤ count1672 b)) else (if i < 1682 then decide (10 ≤ count1672 b) else decide (11 ≤ count1672 b))))) else (if i < 1690 then (if i < 1686 then (if i < 1684 then decide (12 ≤ count1672 b) else (if i < 1685 then decide (13 ≤ count1672 b) else decide (14 ≤ count1672 b))) else (if i < 1688 then (if i < 1687 then decide (1 ≤ count1686 b) else decide (2 ≤ count1686 b)) else (if i < 1689 then decide (1 ≤ count1688 b) else decide (2 ≤ count1688 b)))) else (if i < 1693 then (if i < 1691 then decide (3 ≤ count1688 b) else (if i < 1692 then decide (1 ≤ count1691 b) else decide (2 ≤ count1691 b))) else (if i < 1695 then (if i < 1694 then decide (1 ≤ count1693 b) else decide (2 ≤ count1693 b)) else (if i < 1696 then decide (1 ≤ count1695 b) else decide (2 ≤ count1695 b)))))) else (if i < 1711 then (if i < 1704 then (if i < 1700 then (if i < 1698 then decide (3 ≤ count1695 b) else (if i < 1699 then decide (4 ≤ count1695 b) else decide (1 ≤ count1699 b))) else (if i < 1702 then (if i < 1701 then decide (2 ≤ count1699 b) else decide (3 ≤ count1699 b)) else (if i < 1703 then decide (4 ≤ count1699 b) else decide (5 ≤ count1699 b)))) else (if i < 1707 then (if i < 1705 then decide (6 ≤ count1699 b) else (if i < 1706 then decide (7 ≤ count1699 b) else decide (1 ≤ count1706 b))) else (if i < 1709 then (if i < 1708 then decide (2 ≤ count1706 b) else decide (1 ≤ count1708 b)) else (if i < 1710 then decide (2 ≤ count1708 b) else decide (1 ≤ count1710 b))))) else (if i < 1718 then (if i < 1714 then (if i < 1712 then decide (2 ≤ count1710 b) else (if i < 1713 then decide (3 ≤ count1710 b) else decide (4 ≤ count1710 b))) else (if i < 1716 then (if i < 1715 then decide (1 ≤ count1714 b) else decide (2 ≤ count1714 b)) else (if i < 1717 then decide (1 ≤ count1716 b) else decide (2 ≤ count1716 b)))) else (if i < 1721 then (if i < 1719 then decide (1 ≤ count1718 b) else (if i < 1720 then decide (2 ≤ count1718 b) else decide (3 ≤ count1718 b))) else (if i < 1723 then (if i < 1722 then decide (4 ≤ count1718 b) else decide (1 ≤ count1722 b)) else (if i < 1724 then decide (2 ≤ count1722 b) else decide (3 ≤ count1722 b))))))) else (if i < 1753 then (if i < 1739 then (if i < 1732 then (if i < 1728 then (if i < 1726 then decide (4 ≤ count1722 b) else (if i < 1727 then decide (5 ≤ count1722 b) else decide (6 ≤ count1722 b))) else (if i < 1730 then (if i < 1729 then decide (7 ≤ count1722 b) else decide (8 ≤ count1722 b)) else (if i < 1731 then decide (1 ≤ count1730 b) else decide (2 ≤ count1730 b)))) else (if i < 1735 then (if i < 1733 then decide (3 ≤ count1730 b) else (if i < 1734 then decide (4 ≤ count1730 b) else decide (5 ≤ count1730 b))) else (if i < 1737 then (if i < 1736 then decide (6 ≤ count1730 b) else decide (7 ≤ count1730 b)) else (if i < 1738 then decide (8 ≤ count1730 b) else decide (9 ≤ count1730 b))))) else (if i < 1746 then (if i < 1742 then (if i < 1740 then decide (10 ≤ count1730 b) else (if i < 1741 then decide (11 ≤ count1730 b) else decide (12 ≤ count1730 b))) else (if i < 1744 then (if i < 1743 then decide (13 ≤ count1730 b) else decide (14 ≤ count1730 b)) else (if i < 1745 then decide (15 ≤ count1730 b) else decide (1 ≤ count1745 b)))) else (if i < 1749 then (if i < 1747 then decide (2 ≤ count1745 b) else (if i < 1748 then decide (3 ≤ count1745 b) else decide (4 ≤ count1745 b))) else (if i < 1751 then (if i < 1750 then decide (5 ≤ count1745 b) else decide (6 ≤ count1745 b)) else (if i < 1752 then decide (7 ≤ count1745 b) else decide (8 ≤ count1745 b)))))) else (if i < 1767 then (if i < 1760 then (if i < 1756 then (if i < 1754 then decide (9 ≤ count1745 b) else (if i < 1755 then decide (10 ≤ count1745 b) else decide (11 ≤ count1745 b))) else (if i < 1758 then (if i < 1757 then decide (12 ≤ count1745 b) else decide (13 ≤ count1745 b)) else (if i < 1759 then decide (14 ≤ count1745 b) else decide (15 ≤ count1745 b)))) else (if i < 1763 then (if i < 1761 then decide (16 ≤ count1745 b) else (if i < 1762 then decide (17 ≤ count1745 b) else decide (18 ≤ count1745 b))) else (if i < 1765 then (if i < 1764 then decide (1 ≤ count1763 b) else decide (2 ≤ count1763 b)) else (if i < 1766 then decide (3 ≤ count1763 b) else decide (4 ≤ count1763 b))))) else (if i < 1774 then (if i < 1770 then (if i < 1768 then decide (5 ≤ count1763 b) else (if i < 1769 then decide (6 ≤ count1763 b) else decide (7 ≤ count1763 b))) else (if i < 1772 then (if i < 1771 then decide (8 ≤ count1763 b) else decide (9 ≤ count1763 b)) else (if i < 1773 then decide (10 ≤ count1763 b) else decide (11 ≤ count1763 b)))) else (if i < 1777 then (if i < 1775 then decide (12 ≤ count1763 b) else (if i < 1776 then decide (13 ≤ count1763 b) else decide (14 ≤ count1763 b))) else (if i < 1779 then (if i < 1778 then decide (15 ≤ count1763 b) else decide (16 ≤ count1763 b)) else (if i < 1780 then decide (17 ≤ count1763 b) else decide (18 ≤ count1763 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (89 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (93 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (125 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (127 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (257 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (258 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (261 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (262 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (263 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (264 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (265 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (267 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (268 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (271 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (272 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (275 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (276 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (279 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (281 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (282 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (285 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (287 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (288 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (290 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (293 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (295 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (297 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (299 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (300 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (302 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (304 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (305 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (307 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (308 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (310 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (312 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (314 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (317 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (318 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (319 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (320 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (323 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (324 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (327 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (329 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (333 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (336 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (338 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (344 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (345 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (353 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (355 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (356 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (358 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (360 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (368 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (370 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (376 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (377 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (378 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (379 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (380 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (384 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (385 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (386 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (388 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (390 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (391 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (392 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (393 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (396 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (399 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (402 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (404 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (407 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (409 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (410 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (412 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (413 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (415 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (416 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (419 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (420 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (423 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (425 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (426 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (427 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (429 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (430 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (432 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (433 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (435 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (436 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (437 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (438 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (440 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (442 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (443 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (445 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (446 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (448 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (454 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (455 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (460 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (461 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (470 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (472 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (476 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (481 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (482 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (485 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (486 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (488 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (489 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (492 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (496 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (498 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (500 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (504 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (506 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (508 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (BallClauseLogic.Endpoint q (89 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (BallClauseLogic.Endpoint q (93 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (BallClauseLogic.Endpoint q (120 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (BallClauseLogic.Endpoint q (125 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (BallClauseLogic.Endpoint q (127 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (257 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (258 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (262 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (263 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (271 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (275 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (285 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (288 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (290 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (293 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (295 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (297 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (299 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (300 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (302 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (304 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (305 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (307 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (308 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (310 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (312 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (314 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (317 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (318 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (319 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (323 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (324 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (327 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (329 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (336 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (338 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (344 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (353 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (355 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (356 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (358 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (360 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (368 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (370 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (376 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (377 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (378 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (379 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (380 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (388 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (390 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (391 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (392 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (393 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (396 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (399 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (402 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (404 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (410 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (413 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (415 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (416 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (419 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (420 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (423 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (425 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (426 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (427 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (429 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (430 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (432 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (433 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (435 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (436 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (437 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (438 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (440 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (442 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (443 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (445 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (446 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (448 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (454 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (455 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (460 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (461 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (470 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (472 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (476 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (481 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (482 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (485 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (486 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (488 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (489 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (492 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (496 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (498 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (500 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (504 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (506 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (508 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (1 ≤ count245 (baseVal q)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (1 ≤ count247 (baseVal q)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (1 ≤ count249 (baseVal q)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (1 ≤ count251 (baseVal q)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (2 ≤ count251 (baseVal q)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (1 ≤ count253 (baseVal q)) := rfl
theorem value254 (q : Snake 81) : valuation q 254 = decide (2 ≤ count253 (baseVal q)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value256 (q : Snake 81) : valuation q 256 = decide (2 ≤ count255 (baseVal q)) := rfl
theorem value259 (q : Snake 81) : valuation q 259 = decide (1 ≤ count259 (baseVal q)) := rfl
theorem value261 (q : Snake 81) : valuation q 261 = decide (1 ≤ count261 (baseVal q)) := rfl
theorem value263 (q : Snake 81) : valuation q 263 = decide (1 ≤ count263 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value269 (q : Snake 81) : valuation q 269 = decide (1 ≤ count269 (baseVal q)) := rfl
theorem value270 (q : Snake 81) : valuation q 270 = decide (2 ≤ count269 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value272 (q : Snake 81) : valuation q 272 = decide (2 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value284 (q : Snake 81) : valuation q 284 = decide (2 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value290 (q : Snake 81) : valuation q 290 = decide (2 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value298 (q : Snake 81) : valuation q 298 = decide (2 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value300 (q : Snake 81) : valuation q 300 = decide (2 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value302 (q : Snake 81) : valuation q 302 = decide (2 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value322 (q : Snake 81) : valuation q 322 = decide (2 ≤ count321 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value326 (q : Snake 81) : valuation q 326 = decide (2 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value328 (q : Snake 81) : valuation q 328 = decide (2 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value330 (q : Snake 81) : valuation q 330 = decide (2 ≤ count329 (baseVal q)) := rfl
theorem value331 (q : Snake 81) : valuation q 331 = decide (1 ≤ count331 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value337 (q : Snake 81) : valuation q 337 = decide (1 ≤ count337 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value347 (q : Snake 81) : valuation q 347 = decide (1 ≤ count347 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value360 (q : Snake 81) : valuation q 360 = decide (2 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value362 (q : Snake 81) : valuation q 362 = decide (2 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
theorem value365 (q : Snake 81) : valuation q 365 = decide (1 ≤ count365 (baseVal q)) := rfl
theorem value369 (q : Snake 81) : valuation q 369 = decide (1 ≤ count369 (baseVal q)) := rfl
theorem value371 (q : Snake 81) : valuation q 371 = decide (1 ≤ count371 (baseVal q)) := rfl
theorem value373 (q : Snake 81) : valuation q 373 = decide (1 ≤ count373 (baseVal q)) := rfl
theorem value377 (q : Snake 81) : valuation q 377 = decide (1 ≤ count377 (baseVal q)) := rfl
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value382 (q : Snake 81) : valuation q 382 = decide (2 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value385 (q : Snake 81) : valuation q 385 = decide (1 ≤ count385 (baseVal q)) := rfl
theorem value386 (q : Snake 81) : valuation q 386 = decide (2 ≤ count385 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value388 (q : Snake 81) : valuation q 388 = decide (2 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value408 (q : Snake 81) : valuation q 408 = decide (2 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value416 (q : Snake 81) : valuation q 416 = decide (2 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value418 (q : Snake 81) : valuation q 418 = decide (2 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value420 (q : Snake 81) : valuation q 420 = decide (2 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value423 (q : Snake 81) : valuation q 423 = decide (1 ≤ count423 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value432 (q : Snake 81) : valuation q 432 = decide (2 ≤ count431 (baseVal q)) := rfl
theorem value439 (q : Snake 81) : valuation q 439 = decide (1 ≤ count439 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value444 (q : Snake 81) : valuation q 444 = decide (2 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value446 (q : Snake 81) : valuation q 446 = decide (2 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value448 (q : Snake 81) : valuation q 448 = decide (2 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 (baseVal q)) := rfl
theorem value480 (q : Snake 81) : valuation q 480 = decide (2 ≤ count479 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value482 (q : Snake 81) : valuation q 482 = decide (2 ≤ count481 (baseVal q)) := rfl
theorem value484 (q : Snake 81) : valuation q 484 = decide (2 ≤ count483 (baseVal q)) := rfl
theorem value1501 (q : Snake 81) : valuation q 1501 = decide (1 ≤ count1501 (baseVal q)) := rfl
theorem value1502 (q : Snake 81) : valuation q 1502 = decide (2 ≤ count1501 (baseVal q)) := rfl
theorem value1503 (q : Snake 81) : valuation q 1503 = decide (1 ≤ count1503 (baseVal q)) := rfl
theorem value1504 (q : Snake 81) : valuation q 1504 = decide (2 ≤ count1503 (baseVal q)) := rfl
theorem value1505 (q : Snake 81) : valuation q 1505 = decide (3 ≤ count1503 (baseVal q)) := rfl
theorem value1506 (q : Snake 81) : valuation q 1506 = decide (1 ≤ count1506 (baseVal q)) := rfl
theorem value1507 (q : Snake 81) : valuation q 1507 = decide (2 ≤ count1506 (baseVal q)) := rfl
theorem value1508 (q : Snake 81) : valuation q 1508 = decide (1 ≤ count1508 (baseVal q)) := rfl
theorem value1509 (q : Snake 81) : valuation q 1509 = decide (2 ≤ count1508 (baseVal q)) := rfl
theorem value1510 (q : Snake 81) : valuation q 1510 = decide (1 ≤ count1510 (baseVal q)) := rfl
theorem value1511 (q : Snake 81) : valuation q 1511 = decide (2 ≤ count1510 (baseVal q)) := rfl
theorem value1512 (q : Snake 81) : valuation q 1512 = decide (3 ≤ count1510 (baseVal q)) := rfl
theorem value1513 (q : Snake 81) : valuation q 1513 = decide (4 ≤ count1510 (baseVal q)) := rfl
theorem value1514 (q : Snake 81) : valuation q 1514 = decide (1 ≤ count1514 (baseVal q)) := rfl
theorem value1515 (q : Snake 81) : valuation q 1515 = decide (2 ≤ count1514 (baseVal q)) := rfl
theorem value1516 (q : Snake 81) : valuation q 1516 = decide (3 ≤ count1514 (baseVal q)) := rfl
theorem value1517 (q : Snake 81) : valuation q 1517 = decide (4 ≤ count1514 (baseVal q)) := rfl
theorem value1518 (q : Snake 81) : valuation q 1518 = decide (5 ≤ count1514 (baseVal q)) := rfl
theorem value1519 (q : Snake 81) : valuation q 1519 = decide (6 ≤ count1514 (baseVal q)) := rfl
theorem value1521 (q : Snake 81) : valuation q 1521 = decide (1 ≤ count1521 (baseVal q)) := rfl
theorem value1522 (q : Snake 81) : valuation q 1522 = decide (2 ≤ count1521 (baseVal q)) := rfl
theorem value1523 (q : Snake 81) : valuation q 1523 = decide (1 ≤ count1523 (baseVal q)) := rfl
theorem value1524 (q : Snake 81) : valuation q 1524 = decide (2 ≤ count1523 (baseVal q)) := rfl
theorem value1525 (q : Snake 81) : valuation q 1525 = decide (3 ≤ count1523 (baseVal q)) := rfl
theorem value1526 (q : Snake 81) : valuation q 1526 = decide (1 ≤ count1526 (baseVal q)) := rfl
theorem value1527 (q : Snake 81) : valuation q 1527 = decide (2 ≤ count1526 (baseVal q)) := rfl
theorem value1528 (q : Snake 81) : valuation q 1528 = decide (1 ≤ count1528 (baseVal q)) := rfl
theorem value1529 (q : Snake 81) : valuation q 1529 = decide (2 ≤ count1528 (baseVal q)) := rfl
theorem value1530 (q : Snake 81) : valuation q 1530 = decide (1 ≤ count1530 (baseVal q)) := rfl
theorem value1531 (q : Snake 81) : valuation q 1531 = decide (2 ≤ count1530 (baseVal q)) := rfl
theorem value1532 (q : Snake 81) : valuation q 1532 = decide (3 ≤ count1530 (baseVal q)) := rfl
theorem value1533 (q : Snake 81) : valuation q 1533 = decide (4 ≤ count1530 (baseVal q)) := rfl
theorem value1534 (q : Snake 81) : valuation q 1534 = decide (1 ≤ count1534 (baseVal q)) := rfl
theorem value1535 (q : Snake 81) : valuation q 1535 = decide (2 ≤ count1534 (baseVal q)) := rfl
theorem value1536 (q : Snake 81) : valuation q 1536 = decide (3 ≤ count1534 (baseVal q)) := rfl
theorem value1537 (q : Snake 81) : valuation q 1537 = decide (4 ≤ count1534 (baseVal q)) := rfl
theorem value1538 (q : Snake 81) : valuation q 1538 = decide (5 ≤ count1534 (baseVal q)) := rfl
theorem value1539 (q : Snake 81) : valuation q 1539 = decide (6 ≤ count1534 (baseVal q)) := rfl
theorem value1541 (q : Snake 81) : valuation q 1541 = decide (1 ≤ count1541 (baseVal q)) := rfl
theorem value1542 (q : Snake 81) : valuation q 1542 = decide (2 ≤ count1541 (baseVal q)) := rfl
theorem value1543 (q : Snake 81) : valuation q 1543 = decide (3 ≤ count1541 (baseVal q)) := rfl
theorem value1544 (q : Snake 81) : valuation q 1544 = decide (4 ≤ count1541 (baseVal q)) := rfl
theorem value1545 (q : Snake 81) : valuation q 1545 = decide (5 ≤ count1541 (baseVal q)) := rfl
theorem value1546 (q : Snake 81) : valuation q 1546 = decide (6 ≤ count1541 (baseVal q)) := rfl
theorem value1547 (q : Snake 81) : valuation q 1547 = decide (7 ≤ count1541 (baseVal q)) := rfl
theorem value1548 (q : Snake 81) : valuation q 1548 = decide (8 ≤ count1541 (baseVal q)) := rfl
theorem value1549 (q : Snake 81) : valuation q 1549 = decide (9 ≤ count1541 (baseVal q)) := rfl
theorem value1555 (q : Snake 81) : valuation q 1555 = decide (1 ≤ count1555 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (2 ≤ count1555 (baseVal q)) := rfl
theorem value1557 (q : Snake 81) : valuation q 1557 = decide (1 ≤ count1557 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (2 ≤ count1557 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (3 ≤ count1557 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (1 ≤ count1560 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (2 ≤ count1560 (baseVal q)) := rfl
theorem value1562 (q : Snake 81) : valuation q 1562 = decide (1 ≤ count1562 (baseVal q)) := rfl
theorem value1563 (q : Snake 81) : valuation q 1563 = decide (2 ≤ count1562 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1566 (q : Snake 81) : valuation q 1566 = decide (3 ≤ count1564 (baseVal q)) := rfl
theorem value1568 (q : Snake 81) : valuation q 1568 = decide (1 ≤ count1568 (baseVal q)) := rfl
theorem value1569 (q : Snake 81) : valuation q 1569 = decide (2 ≤ count1568 (baseVal q)) := rfl
theorem value1570 (q : Snake 81) : valuation q 1570 = decide (3 ≤ count1568 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (4 ≤ count1568 (baseVal q)) := rfl
theorem value1575 (q : Snake 81) : valuation q 1575 = decide (1 ≤ count1575 (baseVal q)) := rfl
theorem value1577 (q : Snake 81) : valuation q 1577 = decide (1 ≤ count1577 (baseVal q)) := rfl
theorem value1578 (q : Snake 81) : valuation q 1578 = decide (2 ≤ count1577 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (1 ≤ count1579 (baseVal q)) := rfl
theorem value1580 (q : Snake 81) : valuation q 1580 = decide (2 ≤ count1579 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (1 ≤ count1583 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (2 ≤ count1583 (baseVal q)) := rfl
theorem value1585 (q : Snake 81) : valuation q 1585 = decide (1 ≤ count1585 (baseVal q)) := rfl
theorem value1586 (q : Snake 81) : valuation q 1586 = decide (2 ≤ count1585 (baseVal q)) := rfl
theorem value1587 (q : Snake 81) : valuation q 1587 = decide (1 ≤ count1587 (baseVal q)) := rfl
theorem value1588 (q : Snake 81) : valuation q 1588 = decide (2 ≤ count1587 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (3 ≤ count1587 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (4 ≤ count1587 (baseVal q)) := rfl
theorem value1591 (q : Snake 81) : valuation q 1591 = decide (1 ≤ count1591 (baseVal q)) := rfl
theorem value1592 (q : Snake 81) : valuation q 1592 = decide (2 ≤ count1591 (baseVal q)) := rfl
theorem value1593 (q : Snake 81) : valuation q 1593 = decide (3 ≤ count1591 (baseVal q)) := rfl
theorem value1594 (q : Snake 81) : valuation q 1594 = decide (4 ≤ count1591 (baseVal q)) := rfl
theorem value1595 (q : Snake 81) : valuation q 1595 = decide (5 ≤ count1591 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (1 ≤ count1599 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (2 ≤ count1599 (baseVal q)) := rfl
theorem value1601 (q : Snake 81) : valuation q 1601 = decide (3 ≤ count1599 (baseVal q)) := rfl
theorem value1602 (q : Snake 81) : valuation q 1602 = decide (4 ≤ count1599 (baseVal q)) := rfl
theorem value1603 (q : Snake 81) : valuation q 1603 = decide (5 ≤ count1599 (baseVal q)) := rfl
theorem value1604 (q : Snake 81) : valuation q 1604 = decide (6 ≤ count1599 (baseVal q)) := rfl
theorem value1617 (q : Snake 81) : valuation q 1617 = decide (4 ≤ count1614 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (5 ≤ count1614 (baseVal q)) := rfl
theorem value1619 (q : Snake 81) : valuation q 1619 = decide (6 ≤ count1614 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (7 ≤ count1614 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (8 ≤ count1614 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (9 ≤ count1614 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (10 ≤ count1614 (baseVal q)) := rfl
theorem value1632 (q : Snake 81) : valuation q 1632 = decide (1 ≤ count1632 (baseVal q)) := rfl
theorem value1633 (q : Snake 81) : valuation q 1633 = decide (2 ≤ count1632 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (1 ≤ count1634 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (2 ≤ count1634 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (3 ≤ count1634 (baseVal q)) := rfl
theorem value1637 (q : Snake 81) : valuation q 1637 = decide (1 ≤ count1637 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (2 ≤ count1637 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (1 ≤ count1639 (baseVal q)) := rfl
theorem value1640 (q : Snake 81) : valuation q 1640 = decide (2 ≤ count1639 (baseVal q)) := rfl
theorem value1641 (q : Snake 81) : valuation q 1641 = decide (1 ≤ count1641 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (2 ≤ count1641 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (3 ≤ count1641 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (4 ≤ count1641 (baseVal q)) := rfl
theorem value1645 (q : Snake 81) : valuation q 1645 = decide (1 ≤ count1645 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (2 ≤ count1645 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (3 ≤ count1645 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (4 ≤ count1645 (baseVal q)) := rfl
theorem value1649 (q : Snake 81) : valuation q 1649 = decide (5 ≤ count1645 (baseVal q)) := rfl
theorem value1650 (q : Snake 81) : valuation q 1650 = decide (6 ≤ count1645 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (7 ≤ count1645 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (1 ≤ count1652 (baseVal q)) := rfl
theorem value1653 (q : Snake 81) : valuation q 1653 = decide (2 ≤ count1652 (baseVal q)) := rfl
theorem value1654 (q : Snake 81) : valuation q 1654 = decide (1 ≤ count1654 (baseVal q)) := rfl
theorem value1655 (q : Snake 81) : valuation q 1655 = decide (2 ≤ count1654 (baseVal q)) := rfl
theorem value1656 (q : Snake 81) : valuation q 1656 = decide (3 ≤ count1654 (baseVal q)) := rfl
theorem value1657 (q : Snake 81) : valuation q 1657 = decide (1 ≤ count1657 (baseVal q)) := rfl
theorem value1658 (q : Snake 81) : valuation q 1658 = decide (2 ≤ count1657 (baseVal q)) := rfl
theorem value1659 (q : Snake 81) : valuation q 1659 = decide (1 ≤ count1659 (baseVal q)) := rfl
theorem value1660 (q : Snake 81) : valuation q 1660 = decide (2 ≤ count1659 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (1 ≤ count1661 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (2 ≤ count1661 (baseVal q)) := rfl
theorem value1663 (q : Snake 81) : valuation q 1663 = decide (3 ≤ count1661 (baseVal q)) := rfl
theorem value1664 (q : Snake 81) : valuation q 1664 = decide (4 ≤ count1661 (baseVal q)) := rfl
theorem value1665 (q : Snake 81) : valuation q 1665 = decide (1 ≤ count1665 (baseVal q)) := rfl
theorem value1666 (q : Snake 81) : valuation q 1666 = decide (2 ≤ count1665 (baseVal q)) := rfl
theorem value1667 (q : Snake 81) : valuation q 1667 = decide (3 ≤ count1665 (baseVal q)) := rfl
theorem value1668 (q : Snake 81) : valuation q 1668 = decide (4 ≤ count1665 (baseVal q)) := rfl
theorem value1669 (q : Snake 81) : valuation q 1669 = decide (5 ≤ count1665 (baseVal q)) := rfl
theorem value1670 (q : Snake 81) : valuation q 1670 = decide (6 ≤ count1665 (baseVal q)) := rfl
theorem value1672 (q : Snake 81) : valuation q 1672 = decide (1 ≤ count1672 (baseVal q)) := rfl
theorem value1673 (q : Snake 81) : valuation q 1673 = decide (2 ≤ count1672 (baseVal q)) := rfl
theorem value1674 (q : Snake 81) : valuation q 1674 = decide (3 ≤ count1672 (baseVal q)) := rfl
theorem value1675 (q : Snake 81) : valuation q 1675 = decide (4 ≤ count1672 (baseVal q)) := rfl
theorem value1676 (q : Snake 81) : valuation q 1676 = decide (5 ≤ count1672 (baseVal q)) := rfl
theorem value1677 (q : Snake 81) : valuation q 1677 = decide (6 ≤ count1672 (baseVal q)) := rfl
theorem value1678 (q : Snake 81) : valuation q 1678 = decide (7 ≤ count1672 (baseVal q)) := rfl
theorem value1679 (q : Snake 81) : valuation q 1679 = decide (8 ≤ count1672 (baseVal q)) := rfl
theorem value1680 (q : Snake 81) : valuation q 1680 = decide (9 ≤ count1672 (baseVal q)) := rfl
theorem value1681 (q : Snake 81) : valuation q 1681 = decide (10 ≤ count1672 (baseVal q)) := rfl
theorem value1686 (q : Snake 81) : valuation q 1686 = decide (1 ≤ count1686 (baseVal q)) := rfl
theorem value1687 (q : Snake 81) : valuation q 1687 = decide (2 ≤ count1686 (baseVal q)) := rfl
theorem value1688 (q : Snake 81) : valuation q 1688 = decide (1 ≤ count1688 (baseVal q)) := rfl
theorem value1689 (q : Snake 81) : valuation q 1689 = decide (2 ≤ count1688 (baseVal q)) := rfl
theorem value1690 (q : Snake 81) : valuation q 1690 = decide (3 ≤ count1688 (baseVal q)) := rfl
theorem value1691 (q : Snake 81) : valuation q 1691 = decide (1 ≤ count1691 (baseVal q)) := rfl
theorem value1692 (q : Snake 81) : valuation q 1692 = decide (2 ≤ count1691 (baseVal q)) := rfl
theorem value1693 (q : Snake 81) : valuation q 1693 = decide (1 ≤ count1693 (baseVal q)) := rfl
theorem value1694 (q : Snake 81) : valuation q 1694 = decide (2 ≤ count1693 (baseVal q)) := rfl
theorem value1695 (q : Snake 81) : valuation q 1695 = decide (1 ≤ count1695 (baseVal q)) := rfl
theorem value1696 (q : Snake 81) : valuation q 1696 = decide (2 ≤ count1695 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (3 ≤ count1695 (baseVal q)) := rfl
theorem value1698 (q : Snake 81) : valuation q 1698 = decide (4 ≤ count1695 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (1 ≤ count1699 (baseVal q)) := rfl
theorem value1700 (q : Snake 81) : valuation q 1700 = decide (2 ≤ count1699 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (3 ≤ count1699 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (4 ≤ count1699 (baseVal q)) := rfl
theorem value1703 (q : Snake 81) : valuation q 1703 = decide (5 ≤ count1699 (baseVal q)) := rfl
theorem value1704 (q : Snake 81) : valuation q 1704 = decide (6 ≤ count1699 (baseVal q)) := rfl
theorem value1706 (q : Snake 81) : valuation q 1706 = decide (1 ≤ count1706 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (2 ≤ count1706 (baseVal q)) := rfl
theorem value1708 (q : Snake 81) : valuation q 1708 = decide (1 ≤ count1708 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (1 ≤ count1710 (baseVal q)) := rfl
theorem value1711 (q : Snake 81) : valuation q 1711 = decide (2 ≤ count1710 (baseVal q)) := rfl
theorem value1712 (q : Snake 81) : valuation q 1712 = decide (3 ≤ count1710 (baseVal q)) := rfl
theorem value1714 (q : Snake 81) : valuation q 1714 = decide (1 ≤ count1714 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (2 ≤ count1714 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (1 ≤ count1716 (baseVal q)) := rfl
theorem value1717 (q : Snake 81) : valuation q 1717 = decide (2 ≤ count1716 (baseVal q)) := rfl
theorem value1718 (q : Snake 81) : valuation q 1718 = decide (1 ≤ count1718 (baseVal q)) := rfl
theorem value1719 (q : Snake 81) : valuation q 1719 = decide (2 ≤ count1718 (baseVal q)) := rfl
theorem value1720 (q : Snake 81) : valuation q 1720 = decide (3 ≤ count1718 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (4 ≤ count1718 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (1 ≤ count1722 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (2 ≤ count1722 (baseVal q)) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (3 ≤ count1722 (baseVal q)) := rfl
theorem value1725 (q : Snake 81) : valuation q 1725 = decide (4 ≤ count1722 (baseVal q)) := rfl
theorem value1726 (q : Snake 81) : valuation q 1726 = decide (5 ≤ count1722 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (1 ≤ count1730 (baseVal q)) := rfl
theorem value1731 (q : Snake 81) : valuation q 1731 = decide (2 ≤ count1730 (baseVal q)) := rfl
theorem value1732 (q : Snake 81) : valuation q 1732 = decide (3 ≤ count1730 (baseVal q)) := rfl
theorem value1733 (q : Snake 81) : valuation q 1733 = decide (4 ≤ count1730 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (5 ≤ count1730 (baseVal q)) := rfl
theorem value1735 (q : Snake 81) : valuation q 1735 = decide (6 ≤ count1730 (baseVal q)) := rfl
theorem value1736 (q : Snake 81) : valuation q 1736 = decide (7 ≤ count1730 (baseVal q)) := rfl
theorem value1737 (q : Snake 81) : valuation q 1737 = decide (8 ≤ count1730 (baseVal q)) := rfl
theorem value1752 (q : Snake 81) : valuation q 1752 = decide (8 ≤ count1745 (baseVal q)) := rfl
theorem value1753 (q : Snake 81) : valuation q 1753 = decide (9 ≤ count1745 (baseVal q)) := rfl
theorem value1754 (q : Snake 81) : valuation q 1754 = decide (10 ≤ count1745 (baseVal q)) := rfl
theorem value1755 (q : Snake 81) : valuation q 1755 = decide (11 ≤ count1745 (baseVal q)) := rfl
theorem value1756 (q : Snake 81) : valuation q 1756 = decide (12 ≤ count1745 (baseVal q)) := rfl
theorem value1757 (q : Snake 81) : valuation q 1757 = decide (13 ≤ count1745 (baseVal q)) := rfl
theorem value1758 (q : Snake 81) : valuation q 1758 = decide (14 ≤ count1745 (baseVal q)) := rfl
theorem value1780 (q : Snake 81) : valuation q 1780 = decide (18 ≤ count1763 (baseVal q)) := rfl
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
theorem meaningNeg117 (b : Nat → Bool) : literal (valuationOf b) (-117) = decide (1 ≤ countLit b [-117]) := by
  change literal b (-117) = decide (1 ≤ countLit b [-117])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-117) <;> decide
theorem meaningNeg114 (b : Nat → Bool) : literal (valuationOf b) (-114) = decide (1 ≤ countLit b [-114]) := by
  change literal b (-114) = decide (1 ≤ countLit b [-114])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-114) <;> decide
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
theorem meaningNeg108 (b : Nat → Bool) : literal (valuationOf b) (-108) = decide (1 ≤ countLit b [-108]) := by
  change literal b (-108) = decide (1 ≤ countLit b [-108])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-108) <;> decide
theorem meaningNeg105 (b : Nat → Bool) : literal (valuationOf b) (-105) = decide (1 ≤ countLit b [-105]) := by
  change literal b (-105) = decide (1 ≤ countLit b [-105])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-105) <;> decide
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
theorem meaningNeg77 (b : Nat → Bool) : literal (valuationOf b) (-77) = decide (1 ≤ countLit b [-77]) := by
  change literal b (-77) = decide (1 ≤ countLit b [-77])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-77) <;> decide
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
theorem meaningNeg25 (b : Nat → Bool) : literal (valuationOf b) (-25) = decide (1 ≤ countLit b [-25]) := by
  change literal b (-25) = decide (1 ≤ countLit b [-25])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-25) <;> decide
theorem meaningNeg22 (b : Nat → Bool) : literal (valuationOf b) (-22) = decide (1 ≤ countLit b [-22]) := by
  change literal b (-22) = decide (1 ≤ countLit b [-22])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-22) <;> decide
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
theorem meaningNeg12 (b : Nat → Bool) : literal (valuationOf b) (-12) = decide (1 ≤ countLit b [-12]) := by
  change literal b (-12) = decide (1 ≤ countLit b [-12])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-12) <;> decide
theorem meaningNeg9 (b : Nat → Bool) : literal (valuationOf b) (-9) = decide (1 ≤ countLit b [-9]) := by
  change literal b (-9) = decide (1 ≤ countLit b [-9])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-9) <;> decide
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
theorem meaning125 (b : Nat → Bool) : literal (valuationOf b) (125) = decide (1 ≤ countLit b [125]) := by
  change literal b (125) = decide (1 ≤ countLit b [125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (125) <;> decide
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
theorem meaning133 (b : Nat → Bool) : literal (valuationOf b) (133) = decide (1 ≤ countLit b [133]) := by
  change literal b (133) = decide (1 ≤ countLit b [133])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (133) <;> decide
theorem meaning135 (b : Nat → Bool) : literal (valuationOf b) (135) = decide (1 ≤ countLit b [135]) := by
  change literal b (135) = decide (1 ≤ countLit b [135])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (135) <;> decide
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
theorem meaning145 (b : Nat → Bool) : literal (valuationOf b) (145) = decide (1 ≤ countLit b [145]) := by
  change literal b (145) = decide (1 ≤ countLit b [145])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (145) <;> decide
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
theorem meaning159 (b : Nat → Bool) : literal (valuationOf b) (159) = decide (1 ≤ countLit b [159]) := by
  change literal b (159) = decide (1 ≤ countLit b [159])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (159) <;> decide
theorem meaning161 (b : Nat → Bool) : literal (valuationOf b) (161) = decide (1 ≤ countLit b [161]) := by
  change literal b (161) = decide (1 ≤ countLit b [161])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (161) <;> decide
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
theorem meaning178 (b : Nat → Bool) : literal (valuationOf b) (178) = decide (1 ≤ countLit b [178]) := by
  change literal b (178) = decide (1 ≤ countLit b [178])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (178) <;> decide
theorem meaning182 (b : Nat → Bool) : literal (valuationOf b) (182) = decide (1 ≤ countLit b [182]) := by
  change literal b (182) = decide (1 ≤ countLit b [182])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (182) <;> decide
theorem meaning183 (b : Nat → Bool) : literal (valuationOf b) (183) = decide (1 ≤ countLit b [183]) := by
  change literal b (183) = decide (1 ≤ countLit b [183])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (183) <;> decide
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
theorem meaning190 (b : Nat → Bool) : literal (valuationOf b) (190) = decide (1 ≤ countLit b [190]) := by
  change literal b (190) = decide (1 ≤ countLit b [190])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (190) <;> decide
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
theorem meaning207 (b : Nat → Bool) : literal (valuationOf b) (207) = decide (1 ≤ countLit b [207]) := by
  change literal b (207) = decide (1 ≤ countLit b [207])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (207) <;> decide
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
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) (215) = decide (1 ≤ countLit b [215]) := by
  change literal b (215) = decide (1 ≤ countLit b [215])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (215) <;> decide
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
theorem meaning220 (b : Nat → Bool) : literal (valuationOf b) (220) = decide (1 ≤ countLit b [220]) := by
  change literal b (220) = decide (1 ≤ countLit b [220])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (220) <;> decide
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
theorem meaning229 (b : Nat → Bool) : literal (valuationOf b) (229) = decide (1 ≤ countLit b [229]) := by
  change literal b (229) = decide (1 ≤ countLit b [229])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (229) <;> decide
theorem meaning231 (b : Nat → Bool) : literal (valuationOf b) (231) = decide (1 ≤ countLit b [231]) := by
  change literal b (231) = decide (1 ≤ countLit b [231])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (231) <;> decide
theorem meaning234 (b : Nat → Bool) : literal (valuationOf b) (234) = decide (1 ≤ countLit b [234]) := by
  change literal b (234) = decide (1 ≤ countLit b [234])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (234) <;> decide
theorem meaning235 (b : Nat → Bool) : literal (valuationOf b) (235) = decide (1 ≤ countLit b [235]) := by
  change literal b (235) = decide (1 ≤ countLit b [235])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (235) <;> decide
theorem meaning237 (b : Nat → Bool) : literal (valuationOf b) (237) = decide (1 ≤ countLit b [237]) := by
  change literal b (237) = decide (1 ≤ countLit b [237])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (237) <;> decide
theorem meaning238 (b : Nat → Bool) : literal (valuationOf b) (238) = decide (1 ≤ countLit b [238]) := by
  change literal b (238) = decide (1 ≤ countLit b [238])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (238) <;> decide
theorem meaning240 (b : Nat → Bool) : literal (valuationOf b) (240) = decide (1 ≤ countLit b [240]) := by
  change literal b (240) = decide (1 ≤ countLit b [240])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (240) <;> decide
theorem meaning241 (b : Nat → Bool) : literal (valuationOf b) (241) = decide (1 ≤ countLit b [241]) := by
  change literal b (241) = decide (1 ≤ countLit b [241])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (241) <;> decide
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) (242) = decide (1 ≤ countLit b [242]) := by
  change literal b (242) = decide (1 ≤ countLit b [242])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (242) <;> decide
theorem meaning245 (b : Nat → Bool) : literal (valuationOf b) 245 = decide (1 ≤ count245 b) := rfl
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) 247 = decide (1 ≤ count247 b) := rfl
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) 249 = decide (1 ≤ count249 b) := rfl
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) 251 = decide (1 ≤ count251 b) := rfl
theorem meaning252 (b : Nat → Bool) : literal (valuationOf b) 252 = decide (2 ≤ count251 b) := rfl
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) 253 = decide (1 ≤ count253 b) := rfl
theorem meaning254 (b : Nat → Bool) : literal (valuationOf b) 254 = decide (2 ≤ count253 b) := rfl
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning256 (b : Nat → Bool) : literal (valuationOf b) 256 = decide (2 ≤ count255 b) := rfl
theorem meaning259 (b : Nat → Bool) : literal (valuationOf b) 259 = decide (1 ≤ count259 b) := rfl
theorem meaning261 (b : Nat → Bool) : literal (valuationOf b) 261 = decide (1 ≤ count261 b) := rfl
theorem meaning263 (b : Nat → Bool) : literal (valuationOf b) 263 = decide (1 ≤ count263 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning269 (b : Nat → Bool) : literal (valuationOf b) 269 = decide (1 ≤ count269 b) := rfl
theorem meaning270 (b : Nat → Bool) : literal (valuationOf b) 270 = decide (2 ≤ count269 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning272 (b : Nat → Bool) : literal (valuationOf b) 272 = decide (2 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning284 (b : Nat → Bool) : literal (valuationOf b) 284 = decide (2 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning290 (b : Nat → Bool) : literal (valuationOf b) 290 = decide (2 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning298 (b : Nat → Bool) : literal (valuationOf b) 298 = decide (2 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning300 (b : Nat → Bool) : literal (valuationOf b) 300 = decide (2 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning302 (b : Nat → Bool) : literal (valuationOf b) 302 = decide (2 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning322 (b : Nat → Bool) : literal (valuationOf b) 322 = decide (2 ≤ count321 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning326 (b : Nat → Bool) : literal (valuationOf b) 326 = decide (2 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning328 (b : Nat → Bool) : literal (valuationOf b) 328 = decide (2 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning330 (b : Nat → Bool) : literal (valuationOf b) 330 = decide (2 ≤ count329 b) := rfl
theorem meaning331 (b : Nat → Bool) : literal (valuationOf b) 331 = decide (1 ≤ count331 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning337 (b : Nat → Bool) : literal (valuationOf b) 337 = decide (1 ≤ count337 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning347 (b : Nat → Bool) : literal (valuationOf b) 347 = decide (1 ≤ count347 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning360 (b : Nat → Bool) : literal (valuationOf b) 360 = decide (2 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning362 (b : Nat → Bool) : literal (valuationOf b) 362 = decide (2 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
theorem meaning365 (b : Nat → Bool) : literal (valuationOf b) 365 = decide (1 ≤ count365 b) := rfl
theorem meaning369 (b : Nat → Bool) : literal (valuationOf b) 369 = decide (1 ≤ count369 b) := rfl
theorem meaning371 (b : Nat → Bool) : literal (valuationOf b) 371 = decide (1 ≤ count371 b) := rfl
theorem meaning373 (b : Nat → Bool) : literal (valuationOf b) 373 = decide (1 ≤ count373 b) := rfl
theorem meaning377 (b : Nat → Bool) : literal (valuationOf b) 377 = decide (1 ≤ count377 b) := rfl
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning382 (b : Nat → Bool) : literal (valuationOf b) 382 = decide (2 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning385 (b : Nat → Bool) : literal (valuationOf b) 385 = decide (1 ≤ count385 b) := rfl
theorem meaning386 (b : Nat → Bool) : literal (valuationOf b) 386 = decide (2 ≤ count385 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning388 (b : Nat → Bool) : literal (valuationOf b) 388 = decide (2 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning408 (b : Nat → Bool) : literal (valuationOf b) 408 = decide (2 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning416 (b : Nat → Bool) : literal (valuationOf b) 416 = decide (2 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning418 (b : Nat → Bool) : literal (valuationOf b) 418 = decide (2 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning420 (b : Nat → Bool) : literal (valuationOf b) 420 = decide (2 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning423 (b : Nat → Bool) : literal (valuationOf b) 423 = decide (1 ≤ count423 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning432 (b : Nat → Bool) : literal (valuationOf b) 432 = decide (2 ≤ count431 b) := rfl
theorem meaning439 (b : Nat → Bool) : literal (valuationOf b) 439 = decide (1 ≤ count439 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning444 (b : Nat → Bool) : literal (valuationOf b) 444 = decide (2 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning446 (b : Nat → Bool) : literal (valuationOf b) 446 = decide (2 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning448 (b : Nat → Bool) : literal (valuationOf b) 448 = decide (2 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning479 (b : Nat → Bool) : literal (valuationOf b) 479 = decide (1 ≤ count479 b) := rfl
theorem meaning480 (b : Nat → Bool) : literal (valuationOf b) 480 = decide (2 ≤ count479 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning482 (b : Nat → Bool) : literal (valuationOf b) 482 = decide (2 ≤ count481 b) := rfl
theorem meaning484 (b : Nat → Bool) : literal (valuationOf b) 484 = decide (2 ≤ count483 b) := rfl
theorem meaning1501 (b : Nat → Bool) : literal (valuationOf b) 1501 = decide (1 ≤ count1501 b) := rfl
theorem meaning1502 (b : Nat → Bool) : literal (valuationOf b) 1502 = decide (2 ≤ count1501 b) := rfl
theorem meaning1503 (b : Nat → Bool) : literal (valuationOf b) 1503 = decide (1 ≤ count1503 b) := rfl
theorem meaning1504 (b : Nat → Bool) : literal (valuationOf b) 1504 = decide (2 ≤ count1503 b) := rfl
theorem meaning1505 (b : Nat → Bool) : literal (valuationOf b) 1505 = decide (3 ≤ count1503 b) := rfl
theorem meaning1506 (b : Nat → Bool) : literal (valuationOf b) 1506 = decide (1 ≤ count1506 b) := rfl
theorem meaning1507 (b : Nat → Bool) : literal (valuationOf b) 1507 = decide (2 ≤ count1506 b) := rfl
theorem meaning1508 (b : Nat → Bool) : literal (valuationOf b) 1508 = decide (1 ≤ count1508 b) := rfl
theorem meaning1509 (b : Nat → Bool) : literal (valuationOf b) 1509 = decide (2 ≤ count1508 b) := rfl
theorem meaning1510 (b : Nat → Bool) : literal (valuationOf b) 1510 = decide (1 ≤ count1510 b) := rfl
theorem meaning1511 (b : Nat → Bool) : literal (valuationOf b) 1511 = decide (2 ≤ count1510 b) := rfl
theorem meaning1512 (b : Nat → Bool) : literal (valuationOf b) 1512 = decide (3 ≤ count1510 b) := rfl
theorem meaning1513 (b : Nat → Bool) : literal (valuationOf b) 1513 = decide (4 ≤ count1510 b) := rfl
theorem meaning1514 (b : Nat → Bool) : literal (valuationOf b) 1514 = decide (1 ≤ count1514 b) := rfl
theorem meaning1515 (b : Nat → Bool) : literal (valuationOf b) 1515 = decide (2 ≤ count1514 b) := rfl
theorem meaning1516 (b : Nat → Bool) : literal (valuationOf b) 1516 = decide (3 ≤ count1514 b) := rfl
theorem meaning1517 (b : Nat → Bool) : literal (valuationOf b) 1517 = decide (4 ≤ count1514 b) := rfl
theorem meaning1518 (b : Nat → Bool) : literal (valuationOf b) 1518 = decide (5 ≤ count1514 b) := rfl
theorem meaning1519 (b : Nat → Bool) : literal (valuationOf b) 1519 = decide (6 ≤ count1514 b) := rfl
theorem meaning1521 (b : Nat → Bool) : literal (valuationOf b) 1521 = decide (1 ≤ count1521 b) := rfl
theorem meaning1522 (b : Nat → Bool) : literal (valuationOf b) 1522 = decide (2 ≤ count1521 b) := rfl
theorem meaning1523 (b : Nat → Bool) : literal (valuationOf b) 1523 = decide (1 ≤ count1523 b) := rfl
theorem meaning1524 (b : Nat → Bool) : literal (valuationOf b) 1524 = decide (2 ≤ count1523 b) := rfl
theorem meaning1525 (b : Nat → Bool) : literal (valuationOf b) 1525 = decide (3 ≤ count1523 b) := rfl
theorem meaning1526 (b : Nat → Bool) : literal (valuationOf b) 1526 = decide (1 ≤ count1526 b) := rfl
theorem meaning1527 (b : Nat → Bool) : literal (valuationOf b) 1527 = decide (2 ≤ count1526 b) := rfl
theorem meaning1528 (b : Nat → Bool) : literal (valuationOf b) 1528 = decide (1 ≤ count1528 b) := rfl
theorem meaning1529 (b : Nat → Bool) : literal (valuationOf b) 1529 = decide (2 ≤ count1528 b) := rfl
theorem meaning1530 (b : Nat → Bool) : literal (valuationOf b) 1530 = decide (1 ≤ count1530 b) := rfl
theorem meaning1531 (b : Nat → Bool) : literal (valuationOf b) 1531 = decide (2 ≤ count1530 b) := rfl
theorem meaning1532 (b : Nat → Bool) : literal (valuationOf b) 1532 = decide (3 ≤ count1530 b) := rfl
theorem meaning1533 (b : Nat → Bool) : literal (valuationOf b) 1533 = decide (4 ≤ count1530 b) := rfl
theorem meaning1534 (b : Nat → Bool) : literal (valuationOf b) 1534 = decide (1 ≤ count1534 b) := rfl
theorem meaning1535 (b : Nat → Bool) : literal (valuationOf b) 1535 = decide (2 ≤ count1534 b) := rfl
theorem meaning1536 (b : Nat → Bool) : literal (valuationOf b) 1536 = decide (3 ≤ count1534 b) := rfl
theorem meaning1537 (b : Nat → Bool) : literal (valuationOf b) 1537 = decide (4 ≤ count1534 b) := rfl
theorem meaning1538 (b : Nat → Bool) : literal (valuationOf b) 1538 = decide (5 ≤ count1534 b) := rfl
theorem meaning1539 (b : Nat → Bool) : literal (valuationOf b) 1539 = decide (6 ≤ count1534 b) := rfl
theorem meaning1541 (b : Nat → Bool) : literal (valuationOf b) 1541 = decide (1 ≤ count1541 b) := rfl
theorem meaning1542 (b : Nat → Bool) : literal (valuationOf b) 1542 = decide (2 ≤ count1541 b) := rfl
theorem meaning1543 (b : Nat → Bool) : literal (valuationOf b) 1543 = decide (3 ≤ count1541 b) := rfl
theorem meaning1544 (b : Nat → Bool) : literal (valuationOf b) 1544 = decide (4 ≤ count1541 b) := rfl
theorem meaning1545 (b : Nat → Bool) : literal (valuationOf b) 1545 = decide (5 ≤ count1541 b) := rfl
theorem meaning1546 (b : Nat → Bool) : literal (valuationOf b) 1546 = decide (6 ≤ count1541 b) := rfl
theorem meaning1547 (b : Nat → Bool) : literal (valuationOf b) 1547 = decide (7 ≤ count1541 b) := rfl
theorem meaning1548 (b : Nat → Bool) : literal (valuationOf b) 1548 = decide (8 ≤ count1541 b) := rfl
theorem meaning1549 (b : Nat → Bool) : literal (valuationOf b) 1549 = decide (9 ≤ count1541 b) := rfl
theorem meaning1555 (b : Nat → Bool) : literal (valuationOf b) 1555 = decide (1 ≤ count1555 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (2 ≤ count1555 b) := rfl
theorem meaning1557 (b : Nat → Bool) : literal (valuationOf b) 1557 = decide (1 ≤ count1557 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (2 ≤ count1557 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (3 ≤ count1557 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (1 ≤ count1560 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (2 ≤ count1560 b) := rfl
theorem meaning1562 (b : Nat → Bool) : literal (valuationOf b) 1562 = decide (1 ≤ count1562 b) := rfl
theorem meaning1563 (b : Nat → Bool) : literal (valuationOf b) 1563 = decide (2 ≤ count1562 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1566 (b : Nat → Bool) : literal (valuationOf b) 1566 = decide (3 ≤ count1564 b) := rfl
theorem meaning1568 (b : Nat → Bool) : literal (valuationOf b) 1568 = decide (1 ≤ count1568 b) := rfl
theorem meaning1569 (b : Nat → Bool) : literal (valuationOf b) 1569 = decide (2 ≤ count1568 b) := rfl
theorem meaning1570 (b : Nat → Bool) : literal (valuationOf b) 1570 = decide (3 ≤ count1568 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (4 ≤ count1568 b) := rfl
theorem meaning1575 (b : Nat → Bool) : literal (valuationOf b) 1575 = decide (1 ≤ count1575 b) := rfl
theorem meaning1577 (b : Nat → Bool) : literal (valuationOf b) 1577 = decide (1 ≤ count1577 b) := rfl
theorem meaning1578 (b : Nat → Bool) : literal (valuationOf b) 1578 = decide (2 ≤ count1577 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (1 ≤ count1579 b) := rfl
theorem meaning1580 (b : Nat → Bool) : literal (valuationOf b) 1580 = decide (2 ≤ count1579 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (1 ≤ count1583 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (2 ≤ count1583 b) := rfl
theorem meaning1585 (b : Nat → Bool) : literal (valuationOf b) 1585 = decide (1 ≤ count1585 b) := rfl
theorem meaning1586 (b : Nat → Bool) : literal (valuationOf b) 1586 = decide (2 ≤ count1585 b) := rfl
theorem meaning1587 (b : Nat → Bool) : literal (valuationOf b) 1587 = decide (1 ≤ count1587 b) := rfl
theorem meaning1588 (b : Nat → Bool) : literal (valuationOf b) 1588 = decide (2 ≤ count1587 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (3 ≤ count1587 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (4 ≤ count1587 b) := rfl
theorem meaning1591 (b : Nat → Bool) : literal (valuationOf b) 1591 = decide (1 ≤ count1591 b) := rfl
theorem meaning1592 (b : Nat → Bool) : literal (valuationOf b) 1592 = decide (2 ≤ count1591 b) := rfl
theorem meaning1593 (b : Nat → Bool) : literal (valuationOf b) 1593 = decide (3 ≤ count1591 b) := rfl
theorem meaning1594 (b : Nat → Bool) : literal (valuationOf b) 1594 = decide (4 ≤ count1591 b) := rfl
theorem meaning1595 (b : Nat → Bool) : literal (valuationOf b) 1595 = decide (5 ≤ count1591 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (1 ≤ count1599 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (2 ≤ count1599 b) := rfl
theorem meaning1601 (b : Nat → Bool) : literal (valuationOf b) 1601 = decide (3 ≤ count1599 b) := rfl
theorem meaning1602 (b : Nat → Bool) : literal (valuationOf b) 1602 = decide (4 ≤ count1599 b) := rfl
theorem meaning1603 (b : Nat → Bool) : literal (valuationOf b) 1603 = decide (5 ≤ count1599 b) := rfl
theorem meaning1604 (b : Nat → Bool) : literal (valuationOf b) 1604 = decide (6 ≤ count1599 b) := rfl
theorem meaning1617 (b : Nat → Bool) : literal (valuationOf b) 1617 = decide (4 ≤ count1614 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (5 ≤ count1614 b) := rfl
theorem meaning1619 (b : Nat → Bool) : literal (valuationOf b) 1619 = decide (6 ≤ count1614 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (7 ≤ count1614 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (8 ≤ count1614 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (9 ≤ count1614 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (10 ≤ count1614 b) := rfl
theorem meaning1632 (b : Nat → Bool) : literal (valuationOf b) 1632 = decide (1 ≤ count1632 b) := rfl
theorem meaning1633 (b : Nat → Bool) : literal (valuationOf b) 1633 = decide (2 ≤ count1632 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (1 ≤ count1634 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (2 ≤ count1634 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (3 ≤ count1634 b) := rfl
theorem meaning1637 (b : Nat → Bool) : literal (valuationOf b) 1637 = decide (1 ≤ count1637 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (2 ≤ count1637 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (1 ≤ count1639 b) := rfl
theorem meaning1640 (b : Nat → Bool) : literal (valuationOf b) 1640 = decide (2 ≤ count1639 b) := rfl
theorem meaning1641 (b : Nat → Bool) : literal (valuationOf b) 1641 = decide (1 ≤ count1641 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (2 ≤ count1641 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (3 ≤ count1641 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (4 ≤ count1641 b) := rfl
theorem meaning1645 (b : Nat → Bool) : literal (valuationOf b) 1645 = decide (1 ≤ count1645 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (2 ≤ count1645 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (3 ≤ count1645 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (4 ≤ count1645 b) := rfl
theorem meaning1649 (b : Nat → Bool) : literal (valuationOf b) 1649 = decide (5 ≤ count1645 b) := rfl
theorem meaning1650 (b : Nat → Bool) : literal (valuationOf b) 1650 = decide (6 ≤ count1645 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (7 ≤ count1645 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (1 ≤ count1652 b) := rfl
theorem meaning1653 (b : Nat → Bool) : literal (valuationOf b) 1653 = decide (2 ≤ count1652 b) := rfl
theorem meaning1654 (b : Nat → Bool) : literal (valuationOf b) 1654 = decide (1 ≤ count1654 b) := rfl
theorem meaning1655 (b : Nat → Bool) : literal (valuationOf b) 1655 = decide (2 ≤ count1654 b) := rfl
theorem meaning1656 (b : Nat → Bool) : literal (valuationOf b) 1656 = decide (3 ≤ count1654 b) := rfl
theorem meaning1657 (b : Nat → Bool) : literal (valuationOf b) 1657 = decide (1 ≤ count1657 b) := rfl
theorem meaning1658 (b : Nat → Bool) : literal (valuationOf b) 1658 = decide (2 ≤ count1657 b) := rfl
theorem meaning1659 (b : Nat → Bool) : literal (valuationOf b) 1659 = decide (1 ≤ count1659 b) := rfl
theorem meaning1660 (b : Nat → Bool) : literal (valuationOf b) 1660 = decide (2 ≤ count1659 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (1 ≤ count1661 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (2 ≤ count1661 b) := rfl
theorem meaning1663 (b : Nat → Bool) : literal (valuationOf b) 1663 = decide (3 ≤ count1661 b) := rfl
theorem meaning1664 (b : Nat → Bool) : literal (valuationOf b) 1664 = decide (4 ≤ count1661 b) := rfl
theorem meaning1665 (b : Nat → Bool) : literal (valuationOf b) 1665 = decide (1 ≤ count1665 b) := rfl
theorem meaning1666 (b : Nat → Bool) : literal (valuationOf b) 1666 = decide (2 ≤ count1665 b) := rfl
theorem meaning1667 (b : Nat → Bool) : literal (valuationOf b) 1667 = decide (3 ≤ count1665 b) := rfl
theorem meaning1668 (b : Nat → Bool) : literal (valuationOf b) 1668 = decide (4 ≤ count1665 b) := rfl
theorem meaning1669 (b : Nat → Bool) : literal (valuationOf b) 1669 = decide (5 ≤ count1665 b) := rfl
theorem meaning1670 (b : Nat → Bool) : literal (valuationOf b) 1670 = decide (6 ≤ count1665 b) := rfl
theorem meaning1672 (b : Nat → Bool) : literal (valuationOf b) 1672 = decide (1 ≤ count1672 b) := rfl
theorem meaning1673 (b : Nat → Bool) : literal (valuationOf b) 1673 = decide (2 ≤ count1672 b) := rfl
theorem meaning1674 (b : Nat → Bool) : literal (valuationOf b) 1674 = decide (3 ≤ count1672 b) := rfl
theorem meaning1675 (b : Nat → Bool) : literal (valuationOf b) 1675 = decide (4 ≤ count1672 b) := rfl
theorem meaning1676 (b : Nat → Bool) : literal (valuationOf b) 1676 = decide (5 ≤ count1672 b) := rfl
theorem meaning1677 (b : Nat → Bool) : literal (valuationOf b) 1677 = decide (6 ≤ count1672 b) := rfl
theorem meaning1678 (b : Nat → Bool) : literal (valuationOf b) 1678 = decide (7 ≤ count1672 b) := rfl
theorem meaning1679 (b : Nat → Bool) : literal (valuationOf b) 1679 = decide (8 ≤ count1672 b) := rfl
theorem meaning1680 (b : Nat → Bool) : literal (valuationOf b) 1680 = decide (9 ≤ count1672 b) := rfl
theorem meaning1681 (b : Nat → Bool) : literal (valuationOf b) 1681 = decide (10 ≤ count1672 b) := rfl
theorem meaning1686 (b : Nat → Bool) : literal (valuationOf b) 1686 = decide (1 ≤ count1686 b) := rfl
theorem meaning1687 (b : Nat → Bool) : literal (valuationOf b) 1687 = decide (2 ≤ count1686 b) := rfl
theorem meaning1688 (b : Nat → Bool) : literal (valuationOf b) 1688 = decide (1 ≤ count1688 b) := rfl
theorem meaning1689 (b : Nat → Bool) : literal (valuationOf b) 1689 = decide (2 ≤ count1688 b) := rfl
theorem meaning1690 (b : Nat → Bool) : literal (valuationOf b) 1690 = decide (3 ≤ count1688 b) := rfl
theorem meaning1691 (b : Nat → Bool) : literal (valuationOf b) 1691 = decide (1 ≤ count1691 b) := rfl
theorem meaning1692 (b : Nat → Bool) : literal (valuationOf b) 1692 = decide (2 ≤ count1691 b) := rfl
theorem meaning1693 (b : Nat → Bool) : literal (valuationOf b) 1693 = decide (1 ≤ count1693 b) := rfl
theorem meaning1694 (b : Nat → Bool) : literal (valuationOf b) 1694 = decide (2 ≤ count1693 b) := rfl
theorem meaning1695 (b : Nat → Bool) : literal (valuationOf b) 1695 = decide (1 ≤ count1695 b) := rfl
theorem meaning1696 (b : Nat → Bool) : literal (valuationOf b) 1696 = decide (2 ≤ count1695 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (3 ≤ count1695 b) := rfl
theorem meaning1698 (b : Nat → Bool) : literal (valuationOf b) 1698 = decide (4 ≤ count1695 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (1 ≤ count1699 b) := rfl
theorem meaning1700 (b : Nat → Bool) : literal (valuationOf b) 1700 = decide (2 ≤ count1699 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (3 ≤ count1699 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (4 ≤ count1699 b) := rfl
theorem meaning1703 (b : Nat → Bool) : literal (valuationOf b) 1703 = decide (5 ≤ count1699 b) := rfl
theorem meaning1704 (b : Nat → Bool) : literal (valuationOf b) 1704 = decide (6 ≤ count1699 b) := rfl
theorem meaning1706 (b : Nat → Bool) : literal (valuationOf b) 1706 = decide (1 ≤ count1706 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (2 ≤ count1706 b) := rfl
theorem meaning1708 (b : Nat → Bool) : literal (valuationOf b) 1708 = decide (1 ≤ count1708 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (1 ≤ count1710 b) := rfl
theorem meaning1711 (b : Nat → Bool) : literal (valuationOf b) 1711 = decide (2 ≤ count1710 b) := rfl
theorem meaning1712 (b : Nat → Bool) : literal (valuationOf b) 1712 = decide (3 ≤ count1710 b) := rfl
theorem meaning1714 (b : Nat → Bool) : literal (valuationOf b) 1714 = decide (1 ≤ count1714 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (2 ≤ count1714 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (1 ≤ count1716 b) := rfl
theorem meaning1717 (b : Nat → Bool) : literal (valuationOf b) 1717 = decide (2 ≤ count1716 b) := rfl
theorem meaning1718 (b : Nat → Bool) : literal (valuationOf b) 1718 = decide (1 ≤ count1718 b) := rfl
theorem meaning1719 (b : Nat → Bool) : literal (valuationOf b) 1719 = decide (2 ≤ count1718 b) := rfl
theorem meaning1720 (b : Nat → Bool) : literal (valuationOf b) 1720 = decide (3 ≤ count1718 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (4 ≤ count1718 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (1 ≤ count1722 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (2 ≤ count1722 b) := rfl
theorem meaning1724 (b : Nat → Bool) : literal (valuationOf b) 1724 = decide (3 ≤ count1722 b) := rfl
theorem meaning1725 (b : Nat → Bool) : literal (valuationOf b) 1725 = decide (4 ≤ count1722 b) := rfl
theorem meaning1726 (b : Nat → Bool) : literal (valuationOf b) 1726 = decide (5 ≤ count1722 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (1 ≤ count1730 b) := rfl
theorem meaning1731 (b : Nat → Bool) : literal (valuationOf b) 1731 = decide (2 ≤ count1730 b) := rfl
theorem meaning1732 (b : Nat → Bool) : literal (valuationOf b) 1732 = decide (3 ≤ count1730 b) := rfl
theorem meaning1733 (b : Nat → Bool) : literal (valuationOf b) 1733 = decide (4 ≤ count1730 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (5 ≤ count1730 b) := rfl
theorem meaning1735 (b : Nat → Bool) : literal (valuationOf b) 1735 = decide (6 ≤ count1730 b) := rfl
theorem meaning1736 (b : Nat → Bool) : literal (valuationOf b) 1736 = decide (7 ≤ count1730 b) := rfl
theorem meaning1737 (b : Nat → Bool) : literal (valuationOf b) 1737 = decide (8 ≤ count1730 b) := rfl
theorem meaning1752 (b : Nat → Bool) : literal (valuationOf b) 1752 = decide (8 ≤ count1745 b) := rfl
theorem meaning1753 (b : Nat → Bool) : literal (valuationOf b) 1753 = decide (9 ≤ count1745 b) := rfl
theorem meaning1754 (b : Nat → Bool) : literal (valuationOf b) 1754 = decide (10 ≤ count1745 b) := rfl
theorem meaning1755 (b : Nat → Bool) : literal (valuationOf b) 1755 = decide (11 ≤ count1745 b) := rfl
theorem meaning1756 (b : Nat → Bool) : literal (valuationOf b) 1756 = decide (12 ≤ count1745 b) := rfl
theorem meaning1757 (b : Nat → Bool) : literal (valuationOf b) 1757 = decide (13 ≤ count1745 b) := rfl
theorem meaning1758 (b : Nat → Bool) : literal (valuationOf b) 1758 = decide (14 ≤ count1745 b) := rfl
theorem meaning1780 (b : Nat → Bool) : literal (valuationOf b) 1780 = decide (18 ≤ count1763 b) := rfl
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
end Snake9.Regrowth.E112254
