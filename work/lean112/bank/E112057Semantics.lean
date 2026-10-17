import E112057Data
namespace Snake9.Regrowth.E112057
noncomputable section
local instance propDec (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
def baseVal (q : Snake 81) (i : Nat) : Bool := (if i < 127 then (if i < 63 then (if i < 31 then (if i < 15 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then decide (InPath q (0 : Vertex)) else decide (InPath q (1 : Vertex)))) else (if i < 5 then (if i < 4 then decide (InPath q (2 : Vertex)) else decide (InPath q (5 : Vertex))) else (if i < 6 then decide (InPath q (8 : Vertex)) else decide (InPath q (10 : Vertex))))) else (if i < 11 then (if i < 9 then (if i < 8 then decide (InPath q (12 : Vertex)) else decide (InPath q (14 : Vertex))) else (if i < 10 then decide (InPath q (15 : Vertex)) else decide (InPath q (17 : Vertex)))) else (if i < 13 then (if i < 12 then decide (InPath q (18 : Vertex)) else decide (InPath q (19 : Vertex))) else (if i < 14 then decide (InPath q (21 : Vertex)) else decide (InPath q (22 : Vertex)))))) else (if i < 23 then (if i < 19 then (if i < 17 then (if i < 16 then decide (InPath q (23 : Vertex)) else decide (InPath q (25 : Vertex))) else (if i < 18 then decide (InPath q (27 : Vertex)) else decide (InPath q (28 : Vertex)))) else (if i < 21 then (if i < 20 then decide (InPath q (29 : Vertex)) else decide (InPath q (31 : Vertex))) else (if i < 22 then decide (InPath q (67 : Vertex)) else decide (InPath q (68 : Vertex))))) else (if i < 27 then (if i < 25 then (if i < 24 then decide (InPath q (69 : Vertex)) else decide (InPath q (70 : Vertex))) else (if i < 26 then decide (InPath q (71 : Vertex)) else decide (InPath q (72 : Vertex)))) else (if i < 29 then (if i < 28 then decide (InPath q (73 : Vertex)) else decide (InPath q (75 : Vertex))) else (if i < 30 then decide (InPath q (79 : Vertex)) else decide (InPath q (80 : Vertex))))))) else (if i < 47 then (if i < 39 then (if i < 35 then (if i < 33 then (if i < 32 then decide (InPath q (82 : Vertex)) else decide (InPath q (84 : Vertex))) else (if i < 34 then decide (InPath q (85 : Vertex)) else decide (InPath q (88 : Vertex)))) else (if i < 37 then (if i < 36 then decide (InPath q (90 : Vertex)) else decide (InPath q (92 : Vertex))) else (if i < 38 then decide (InPath q (94 : Vertex)) else decide (InPath q (131 : Vertex))))) else (if i < 43 then (if i < 41 then (if i < 40 then decide (InPath q (132 : Vertex)) else decide (InPath q (133 : Vertex))) else (if i < 42 then decide (InPath q (134 : Vertex)) else decide (InPath q (135 : Vertex)))) else (if i < 45 then (if i < 44 then decide (InPath q (136 : Vertex)) else decide (InPath q (137 : Vertex))) else (if i < 46 then decide (InPath q (138 : Vertex)) else decide (InPath q (139 : Vertex)))))) else (if i < 55 then (if i < 51 then (if i < 49 then (if i < 48 then decide (InPath q (141 : Vertex)) else decide (InPath q (144 : Vertex))) else (if i < 50 then decide (InPath q (148 : Vertex)) else decide (InPath q (149 : Vertex)))) else (if i < 53 then (if i < 52 then decide (InPath q (150 : Vertex)) else decide (InPath q (151 : Vertex))) else (if i < 54 then decide (InPath q (152 : Vertex)) else decide (InPath q (154 : Vertex))))) else (if i < 59 then (if i < 57 then (if i < 56 then decide (InPath q (158 : Vertex)) else decide (InPath q (192 : Vertex))) else (if i < 58 then decide (InPath q (193 : Vertex)) else decide (InPath q (194 : Vertex)))) else (if i < 61 then (if i < 60 then decide (InPath q (197 : Vertex)) else decide (InPath q (202 : Vertex))) else (if i < 62 then decide (InPath q (204 : Vertex)) else decide (InPath q (206 : Vertex)))))))) else (if i < 95 then (if i < 79 then (if i < 71 then (if i < 67 then (if i < 65 then (if i < 64 then decide (InPath q (208 : Vertex)) else decide (InPath q (222 : Vertex))) else (if i < 66 then decide (InPath q (228 : Vertex)) else decide (InPath q (229 : Vertex)))) else (if i < 69 then (if i < 68 then decide (InPath q (245 : Vertex)) else decide (InPath q (259 : Vertex))) else (if i < 70 then decide (InPath q (260 : Vertex)) else decide (InPath q (261 : Vertex))))) else (if i < 75 then (if i < 73 then (if i < 72 then decide (InPath q (262 : Vertex)) else decide (InPath q (263 : Vertex))) else (if i < 74 then decide (InPath q (264 : Vertex)) else decide (InPath q (265 : Vertex)))) else (if i < 77 then (if i < 76 then decide (InPath q (267 : Vertex)) else decide (InPath q (268 : Vertex))) else (if i < 78 then decide (InPath q (269 : Vertex)) else decide (InPath q (271 : Vertex)))))) else (if i < 87 then (if i < 83 then (if i < 81 then (if i < 80 then decide (InPath q (272 : Vertex)) else decide (InPath q (274 : Vertex))) else (if i < 82 then decide (InPath q (276 : Vertex)) else decide (InPath q (277 : Vertex)))) else (if i < 85 then (if i < 84 then decide (InPath q (278 : Vertex)) else decide (InPath q (279 : Vertex))) else (if i < 86 then decide (InPath q (280 : Vertex)) else decide (InPath q (281 : Vertex))))) else (if i < 91 then (if i < 89 then (if i < 88 then decide (InPath q (282 : Vertex)) else decide (InPath q (283 : Vertex))) else (if i < 90 then decide (InPath q (284 : Vertex)) else decide (InPath q (287 : Vertex)))) else (if i < 93 then (if i < 92 then decide (InPath q (320 : Vertex)) else decide (InPath q (321 : Vertex))) else (if i < 94 then decide (InPath q (322 : Vertex)) else decide (InPath q (323 : Vertex))))))) else (if i < 111 then (if i < 103 then (if i < 99 then (if i < 97 then (if i < 96 then decide (InPath q (325 : Vertex)) else decide (InPath q (330 : Vertex))) else (if i < 98 then decide (InPath q (332 : Vertex)) else decide (InPath q (333 : Vertex)))) else (if i < 101 then (if i < 100 then decide (InPath q (334 : Vertex)) else decide (InPath q (336 : Vertex))) else (if i < 102 then decide (InPath q (337 : Vertex)) else decide (InPath q (342 : Vertex))))) else (if i < 107 then (if i < 105 then (if i < 104 then decide (InPath q (343 : Vertex)) else decide (InPath q (345 : Vertex))) else (if i < 106 then decide (InPath q (347 : Vertex)) else decide (InPath q (348 : Vertex)))) else (if i < 109 then (if i < 108 then decide (InPath q (350 : Vertex)) else decide (InPath q (351 : Vertex))) else (if i < 110 then decide (InPath q (384 : Vertex)) else decide (InPath q (385 : Vertex)))))) else (if i < 119 then (if i < 115 then (if i < 113 then (if i < 112 then decide (InPath q (386 : Vertex)) else decide (InPath q (389 : Vertex))) else (if i < 114 then decide (InPath q (394 : Vertex)) else decide (InPath q (396 : Vertex)))) else (if i < 117 then (if i < 116 then decide (InPath q (397 : Vertex)) else decide (InPath q (398 : Vertex))) else (if i < 118 then decide (InPath q (400 : Vertex)) else decide (InPath q (401 : Vertex))))) else (if i < 123 then (if i < 121 then (if i < 120 then decide (InPath q (403 : Vertex)) else decide (InPath q (406 : Vertex))) else (if i < 122 then decide (InPath q (407 : Vertex)) else decide (InPath q (409 : Vertex)))) else (if i < 125 then (if i < 124 then decide (InPath q (411 : Vertex)) else decide (InPath q (412 : Vertex))) else (if i < 126 then decide (InPath q (414 : Vertex)) else decide (InPath q (415 : Vertex))))))))) else (if i < 191 then (if i < 159 then (if i < 143 then (if i < 135 then (if i < 131 then (if i < 129 then (if i < 128 then decide (InPath q (485 : Vertex)) else decide (BallClauseLogic.Endpoint q (0 : Vertex))) else (if i < 130 then decide (BallClauseLogic.Endpoint q (1 : Vertex)) else decide (BallClauseLogic.Endpoint q (2 : Vertex)))) else (if i < 133 then (if i < 132 then decide (BallClauseLogic.Endpoint q (5 : Vertex)) else decide (BallClauseLogic.Endpoint q (8 : Vertex))) else (if i < 134 then decide (BallClauseLogic.Endpoint q (10 : Vertex)) else decide (BallClauseLogic.Endpoint q (12 : Vertex))))) else (if i < 139 then (if i < 137 then (if i < 136 then decide (BallClauseLogic.Endpoint q (14 : Vertex)) else decide (BallClauseLogic.Endpoint q (15 : Vertex))) else (if i < 138 then decide (BallClauseLogic.Endpoint q (17 : Vertex)) else decide (BallClauseLogic.Endpoint q (18 : Vertex)))) else (if i < 141 then (if i < 140 then decide (BallClauseLogic.Endpoint q (19 : Vertex)) else decide (BallClauseLogic.Endpoint q (21 : Vertex))) else (if i < 142 then decide (BallClauseLogic.Endpoint q (22 : Vertex)) else decide (BallClauseLogic.Endpoint q (23 : Vertex)))))) else (if i < 151 then (if i < 147 then (if i < 145 then (if i < 144 then decide (BallClauseLogic.Endpoint q (25 : Vertex)) else decide (BallClauseLogic.Endpoint q (27 : Vertex))) else (if i < 146 then decide (BallClauseLogic.Endpoint q (28 : Vertex)) else decide (BallClauseLogic.Endpoint q (29 : Vertex)))) else (if i < 149 then (if i < 148 then decide (BallClauseLogic.Endpoint q (31 : Vertex)) else decide (BallClauseLogic.Endpoint q (67 : Vertex))) else (if i < 150 then decide (BallClauseLogic.Endpoint q (68 : Vertex)) else decide (BallClauseLogic.Endpoint q (69 : Vertex))))) else (if i < 155 then (if i < 153 then (if i < 152 then decide (BallClauseLogic.Endpoint q (70 : Vertex)) else decide (BallClauseLogic.Endpoint q (71 : Vertex))) else (if i < 154 then decide (BallClauseLogic.Endpoint q (72 : Vertex)) else decide (BallClauseLogic.Endpoint q (73 : Vertex)))) else (if i < 157 then (if i < 156 then decide (BallClauseLogic.Endpoint q (75 : Vertex)) else decide (BallClauseLogic.Endpoint q (79 : Vertex))) else (if i < 158 then decide (BallClauseLogic.Endpoint q (80 : Vertex)) else decide (BallClauseLogic.Endpoint q (82 : Vertex))))))) else (if i < 175 then (if i < 167 then (if i < 163 then (if i < 161 then (if i < 160 then decide (BallClauseLogic.Endpoint q (84 : Vertex)) else decide (BallClauseLogic.Endpoint q (85 : Vertex))) else (if i < 162 then decide (BallClauseLogic.Endpoint q (88 : Vertex)) else decide (BallClauseLogic.Endpoint q (90 : Vertex)))) else (if i < 165 then (if i < 164 then decide (BallClauseLogic.Endpoint q (92 : Vertex)) else decide (BallClauseLogic.Endpoint q (94 : Vertex))) else (if i < 166 then decide (BallClauseLogic.Endpoint q (131 : Vertex)) else decide (BallClauseLogic.Endpoint q (132 : Vertex))))) else (if i < 171 then (if i < 169 then (if i < 168 then decide (BallClauseLogic.Endpoint q (133 : Vertex)) else decide (BallClauseLogic.Endpoint q (134 : Vertex))) else (if i < 170 then decide (BallClauseLogic.Endpoint q (135 : Vertex)) else decide (BallClauseLogic.Endpoint q (136 : Vertex)))) else (if i < 173 then (if i < 172 then decide (BallClauseLogic.Endpoint q (137 : Vertex)) else decide (BallClauseLogic.Endpoint q (138 : Vertex))) else (if i < 174 then decide (BallClauseLogic.Endpoint q (139 : Vertex)) else decide (BallClauseLogic.Endpoint q (141 : Vertex)))))) else (if i < 183 then (if i < 179 then (if i < 177 then (if i < 176 then decide (BallClauseLogic.Endpoint q (144 : Vertex)) else decide (BallClauseLogic.Endpoint q (148 : Vertex))) else (if i < 178 then decide (BallClauseLogic.Endpoint q (149 : Vertex)) else decide (BallClauseLogic.Endpoint q (150 : Vertex)))) else (if i < 181 then (if i < 180 then decide (BallClauseLogic.Endpoint q (151 : Vertex)) else decide (BallClauseLogic.Endpoint q (152 : Vertex))) else (if i < 182 then decide (BallClauseLogic.Endpoint q (154 : Vertex)) else decide (BallClauseLogic.Endpoint q (158 : Vertex))))) else (if i < 187 then (if i < 185 then (if i < 184 then decide (BallClauseLogic.Endpoint q (192 : Vertex)) else decide (BallClauseLogic.Endpoint q (193 : Vertex))) else (if i < 186 then decide (BallClauseLogic.Endpoint q (194 : Vertex)) else decide (BallClauseLogic.Endpoint q (197 : Vertex)))) else (if i < 189 then (if i < 188 then decide (BallClauseLogic.Endpoint q (202 : Vertex)) else decide (BallClauseLogic.Endpoint q (204 : Vertex))) else (if i < 190 then decide (BallClauseLogic.Endpoint q (206 : Vertex)) else decide (BallClauseLogic.Endpoint q (208 : Vertex)))))))) else (if i < 223 then (if i < 207 then (if i < 199 then (if i < 195 then (if i < 193 then (if i < 192 then decide (BallClauseLogic.Endpoint q (222 : Vertex)) else decide (BallClauseLogic.Endpoint q (228 : Vertex))) else (if i < 194 then decide (BallClauseLogic.Endpoint q (229 : Vertex)) else decide (BallClauseLogic.Endpoint q (245 : Vertex)))) else (if i < 197 then (if i < 196 then decide (BallClauseLogic.Endpoint q (259 : Vertex)) else decide (BallClauseLogic.Endpoint q (260 : Vertex))) else (if i < 198 then decide (BallClauseLogic.Endpoint q (261 : Vertex)) else decide (BallClauseLogic.Endpoint q (262 : Vertex))))) else (if i < 203 then (if i < 201 then (if i < 200 then decide (BallClauseLogic.Endpoint q (263 : Vertex)) else decide (BallClauseLogic.Endpoint q (264 : Vertex))) else (if i < 202 then decide (BallClauseLogic.Endpoint q (265 : Vertex)) else decide (BallClauseLogic.Endpoint q (267 : Vertex)))) else (if i < 205 then (if i < 204 then decide (BallClauseLogic.Endpoint q (268 : Vertex)) else decide (BallClauseLogic.Endpoint q (269 : Vertex))) else (if i < 206 then decide (BallClauseLogic.Endpoint q (271 : Vertex)) else decide (BallClauseLogic.Endpoint q (272 : Vertex)))))) else (if i < 215 then (if i < 211 then (if i < 209 then (if i < 208 then decide (BallClauseLogic.Endpoint q (274 : Vertex)) else decide (BallClauseLogic.Endpoint q (276 : Vertex))) else (if i < 210 then decide (BallClauseLogic.Endpoint q (277 : Vertex)) else decide (BallClauseLogic.Endpoint q (278 : Vertex)))) else (if i < 213 then (if i < 212 then decide (BallClauseLogic.Endpoint q (279 : Vertex)) else decide (BallClauseLogic.Endpoint q (280 : Vertex))) else (if i < 214 then decide (BallClauseLogic.Endpoint q (281 : Vertex)) else decide (BallClauseLogic.Endpoint q (282 : Vertex))))) else (if i < 219 then (if i < 217 then (if i < 216 then decide (BallClauseLogic.Endpoint q (283 : Vertex)) else decide (BallClauseLogic.Endpoint q (284 : Vertex))) else (if i < 218 then decide (BallClauseLogic.Endpoint q (287 : Vertex)) else decide (BallClauseLogic.Endpoint q (320 : Vertex)))) else (if i < 221 then (if i < 220 then decide (BallClauseLogic.Endpoint q (321 : Vertex)) else decide (BallClauseLogic.Endpoint q (322 : Vertex))) else (if i < 222 then decide (BallClauseLogic.Endpoint q (323 : Vertex)) else decide (BallClauseLogic.Endpoint q (325 : Vertex))))))) else (if i < 239 then (if i < 231 then (if i < 227 then (if i < 225 then (if i < 224 then decide (BallClauseLogic.Endpoint q (330 : Vertex)) else decide (BallClauseLogic.Endpoint q (332 : Vertex))) else (if i < 226 then decide (BallClauseLogic.Endpoint q (333 : Vertex)) else decide (BallClauseLogic.Endpoint q (334 : Vertex)))) else (if i < 229 then (if i < 228 then decide (BallClauseLogic.Endpoint q (336 : Vertex)) else decide (BallClauseLogic.Endpoint q (337 : Vertex))) else (if i < 230 then decide (BallClauseLogic.Endpoint q (342 : Vertex)) else decide (BallClauseLogic.Endpoint q (343 : Vertex))))) else (if i < 235 then (if i < 233 then (if i < 232 then decide (BallClauseLogic.Endpoint q (345 : Vertex)) else decide (BallClauseLogic.Endpoint q (347 : Vertex))) else (if i < 234 then decide (BallClauseLogic.Endpoint q (348 : Vertex)) else decide (BallClauseLogic.Endpoint q (350 : Vertex)))) else (if i < 237 then (if i < 236 then decide (BallClauseLogic.Endpoint q (351 : Vertex)) else decide (BallClauseLogic.Endpoint q (384 : Vertex))) else (if i < 238 then decide (BallClauseLogic.Endpoint q (385 : Vertex)) else decide (BallClauseLogic.Endpoint q (386 : Vertex)))))) else (if i < 247 then (if i < 243 then (if i < 241 then (if i < 240 then decide (BallClauseLogic.Endpoint q (389 : Vertex)) else decide (BallClauseLogic.Endpoint q (394 : Vertex))) else (if i < 242 then decide (BallClauseLogic.Endpoint q (396 : Vertex)) else decide (BallClauseLogic.Endpoint q (397 : Vertex)))) else (if i < 245 then (if i < 244 then decide (BallClauseLogic.Endpoint q (398 : Vertex)) else decide (BallClauseLogic.Endpoint q (400 : Vertex))) else (if i < 246 then decide (BallClauseLogic.Endpoint q (401 : Vertex)) else decide (BallClauseLogic.Endpoint q (403 : Vertex))))) else (if i < 251 then (if i < 249 then (if i < 248 then decide (BallClauseLogic.Endpoint q (406 : Vertex)) else decide (BallClauseLogic.Endpoint q (407 : Vertex))) else (if i < 250 then decide (BallClauseLogic.Endpoint q (409 : Vertex)) else decide (BallClauseLogic.Endpoint q (411 : Vertex)))) else (if i < 253 then (if i < 252 then decide (BallClauseLogic.Endpoint q (412 : Vertex)) else decide (BallClauseLogic.Endpoint q (414 : Vertex))) else (if i < 254 then decide (BallClauseLogic.Endpoint q (415 : Vertex)) else decide (BallClauseLogic.Endpoint q (485 : Vertex))))))))))
def countLit (b : Nat → Bool) (xs : List Int) : Nat := xs.countP (literal b)
def count255 (b : Nat → Bool) : Nat := countLit b [129, 130]
def count257 (b : Nat → Bool) : Nat := countLit b [128, 129, 130]
def count259 (b : Nat → Bool) : Nat := countLit b [131, 132]
def count261 (b : Nat → Bool) : Nat := countLit b [133, 134]
def count263 (b : Nat → Bool) : Nat := countLit b [131, 132, 133, 134]
def count265 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134]
def count267 (b : Nat → Bool) : Nat := countLit b [135, 136]
def count269 (b : Nat → Bool) : Nat := countLit b [137, 138]
def count271 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138]
def count273 (b : Nat → Bool) : Nat := countLit b [139, 140]
def count275 (b : Nat → Bool) : Nat := countLit b [141, 142]
def count277 (b : Nat → Bool) : Nat := countLit b [139, 140, 141, 142]
def count279 (b : Nat → Bool) : Nat := countLit b [135, 136, 137, 138, 139, 140, 141, 142]
def count281 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142]
def count283 (b : Nat → Bool) : Nat := countLit b [143, 144]
def count285 (b : Nat → Bool) : Nat := countLit b [145, 146]
def count287 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146]
def count289 (b : Nat → Bool) : Nat := countLit b [147, 148]
def count291 (b : Nat → Bool) : Nat := countLit b [149, 150]
def count293 (b : Nat → Bool) : Nat := countLit b [147, 148, 149, 150]
def count295 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150]
def count297 (b : Nat → Bool) : Nat := countLit b [151, 152]
def count299 (b : Nat → Bool) : Nat := countLit b [153, 154]
def count301 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154]
def count303 (b : Nat → Bool) : Nat := countLit b [155, 156]
def count305 (b : Nat → Bool) : Nat := countLit b [157, 158]
def count307 (b : Nat → Bool) : Nat := countLit b [155, 156, 157, 158]
def count309 (b : Nat → Bool) : Nat := countLit b [151, 152, 153, 154, 155, 156, 157, 158]
def count311 (b : Nat → Bool) : Nat := countLit b [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count313 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158]
def count315 (b : Nat → Bool) : Nat := countLit b [159, 160]
def count317 (b : Nat → Bool) : Nat := countLit b [161, 162]
def count319 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162]
def count321 (b : Nat → Bool) : Nat := countLit b [163, 164]
def count323 (b : Nat → Bool) : Nat := countLit b [165, 166]
def count325 (b : Nat → Bool) : Nat := countLit b [163, 164, 165, 166]
def count327 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166]
def count329 (b : Nat → Bool) : Nat := countLit b [167, 168]
def count331 (b : Nat → Bool) : Nat := countLit b [169, 170]
def count333 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170]
def count335 (b : Nat → Bool) : Nat := countLit b [171, 172]
def count337 (b : Nat → Bool) : Nat := countLit b [173, 174]
def count339 (b : Nat → Bool) : Nat := countLit b [171, 172, 173, 174]
def count341 (b : Nat → Bool) : Nat := countLit b [167, 168, 169, 170, 171, 172, 173, 174]
def count343 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]
def count345 (b : Nat → Bool) : Nat := countLit b [175, 176]
def count347 (b : Nat → Bool) : Nat := countLit b [177, 178]
def count349 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178]
def count351 (b : Nat → Bool) : Nat := countLit b [179, 180]
def count353 (b : Nat → Bool) : Nat := countLit b [181, 182]
def count355 (b : Nat → Bool) : Nat := countLit b [179, 180, 181, 182]
def count357 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182]
def count359 (b : Nat → Bool) : Nat := countLit b [183, 184]
def count361 (b : Nat → Bool) : Nat := countLit b [185, 186]
def count363 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186]
def count365 (b : Nat → Bool) : Nat := countLit b [187, 188]
def count367 (b : Nat → Bool) : Nat := countLit b [189, 190]
def count369 (b : Nat → Bool) : Nat := countLit b [187, 188, 189, 190]
def count371 (b : Nat → Bool) : Nat := countLit b [183, 184, 185, 186, 187, 188, 189, 190]
def count373 (b : Nat → Bool) : Nat := countLit b [175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count375 (b : Nat → Bool) : Nat := countLit b [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count377 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190]
def count379 (b : Nat → Bool) : Nat := countLit b [192, 193]
def count381 (b : Nat → Bool) : Nat := countLit b [191, 192, 193]
def count383 (b : Nat → Bool) : Nat := countLit b [194, 195]
def count385 (b : Nat → Bool) : Nat := countLit b [196, 197]
def count387 (b : Nat → Bool) : Nat := countLit b [194, 195, 196, 197]
def count389 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197]
def count391 (b : Nat → Bool) : Nat := countLit b [198, 199]
def count393 (b : Nat → Bool) : Nat := countLit b [200, 201]
def count395 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201]
def count397 (b : Nat → Bool) : Nat := countLit b [202, 203]
def count399 (b : Nat → Bool) : Nat := countLit b [204, 205]
def count401 (b : Nat → Bool) : Nat := countLit b [202, 203, 204, 205]
def count403 (b : Nat → Bool) : Nat := countLit b [198, 199, 200, 201, 202, 203, 204, 205]
def count405 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205]
def count407 (b : Nat → Bool) : Nat := countLit b [206, 207]
def count409 (b : Nat → Bool) : Nat := countLit b [208, 209]
def count411 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209]
def count413 (b : Nat → Bool) : Nat := countLit b [210, 211]
def count415 (b : Nat → Bool) : Nat := countLit b [212, 213]
def count417 (b : Nat → Bool) : Nat := countLit b [210, 211, 212, 213]
def count419 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209, 210, 211, 212, 213]
def count421 (b : Nat → Bool) : Nat := countLit b [214, 215]
def count423 (b : Nat → Bool) : Nat := countLit b [216, 217]
def count425 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217]
def count427 (b : Nat → Bool) : Nat := countLit b [218, 219]
def count429 (b : Nat → Bool) : Nat := countLit b [220, 221]
def count431 (b : Nat → Bool) : Nat := countLit b [218, 219, 220, 221]
def count433 (b : Nat → Bool) : Nat := countLit b [214, 215, 216, 217, 218, 219, 220, 221]
def count435 (b : Nat → Bool) : Nat := countLit b [206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]
def count437 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221]
def count439 (b : Nat → Bool) : Nat := countLit b [222, 223]
def count441 (b : Nat → Bool) : Nat := countLit b [224, 225]
def count443 (b : Nat → Bool) : Nat := countLit b [222, 223, 224, 225]
def count445 (b : Nat → Bool) : Nat := countLit b [226, 227]
def count447 (b : Nat → Bool) : Nat := countLit b [228, 229]
def count449 (b : Nat → Bool) : Nat := countLit b [226, 227, 228, 229]
def count451 (b : Nat → Bool) : Nat := countLit b [222, 223, 224, 225, 226, 227, 228, 229]
def count453 (b : Nat → Bool) : Nat := countLit b [230, 231]
def count455 (b : Nat → Bool) : Nat := countLit b [232, 233]
def count457 (b : Nat → Bool) : Nat := countLit b [230, 231, 232, 233]
def count459 (b : Nat → Bool) : Nat := countLit b [234, 235]
def count461 (b : Nat → Bool) : Nat := countLit b [236, 237]
def count463 (b : Nat → Bool) : Nat := countLit b [234, 235, 236, 237]
def count465 (b : Nat → Bool) : Nat := countLit b [230, 231, 232, 233, 234, 235, 236, 237]
def count467 (b : Nat → Bool) : Nat := countLit b [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237]
def count469 (b : Nat → Bool) : Nat := countLit b [238, 239]
def count471 (b : Nat → Bool) : Nat := countLit b [240, 241]
def count473 (b : Nat → Bool) : Nat := countLit b [238, 239, 240, 241]
def count475 (b : Nat → Bool) : Nat := countLit b [242, 243]
def count477 (b : Nat → Bool) : Nat := countLit b [244, 245]
def count479 (b : Nat → Bool) : Nat := countLit b [242, 243, 244, 245]
def count481 (b : Nat → Bool) : Nat := countLit b [238, 239, 240, 241, 242, 243, 244, 245]
def count483 (b : Nat → Bool) : Nat := countLit b [246, 247]
def count485 (b : Nat → Bool) : Nat := countLit b [248, 249]
def count487 (b : Nat → Bool) : Nat := countLit b [246, 247, 248, 249]
def count489 (b : Nat → Bool) : Nat := countLit b [250, 251]
def count491 (b : Nat → Bool) : Nat := countLit b [252, 253]
def count493 (b : Nat → Bool) : Nat := countLit b [250, 251, 252, 253]
def count495 (b : Nat → Bool) : Nat := countLit b [246, 247, 248, 249, 250, 251, 252, 253]
def count497 (b : Nat → Bool) : Nat := countLit b [238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]
def count499 (b : Nat → Bool) : Nat := countLit b [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]
def count501 (b : Nat → Bool) : Nat := countLit b [191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]
def count503 (b : Nat → Bool) : Nat := countLit b [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253]
def count505 (b : Nat → Bool) : Nat := countLit b [1, 4]
def count507 (b : Nat → Bool) : Nat := countLit b [6, 7]
def count509 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7]
def count513 (b : Nat → Bool) : Nat := countLit b [9, 10]
def count515 (b : Nat → Bool) : Nat := countLit b [11, 15]
def count517 (b : Nat → Bool) : Nat := countLit b [9, 10, 11, 15]
def count521 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15]
def count529 (b : Nat → Bool) : Nat := countLit b [17, 19]
def count531 (b : Nat → Bool) : Nat := countLit b [22, 25]
def count533 (b : Nat → Bool) : Nat := countLit b [17, 19, 22, 25]
def count537 (b : Nat → Bool) : Nat := countLit b [26, 28]
def count539 (b : Nat → Bool) : Nat := countLit b [30, 33]
def count541 (b : Nat → Bool) : Nat := countLit b [26, 28, 30, 33]
def count545 (b : Nat → Bool) : Nat := countLit b [17, 19, 22, 25, 26, 28, 30, 33]
def count553 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15, 17, 19, 22, 25, 26, 28, 30, 33]
def count569 (b : Nat → Bool) : Nat := countLit b [35, 36]
def count571 (b : Nat → Bool) : Nat := countLit b [39, 42]
def count573 (b : Nat → Bool) : Nat := countLit b [35, 36, 39, 42]
def count577 (b : Nat → Bool) : Nat := countLit b [43, 46]
def count579 (b : Nat → Bool) : Nat := countLit b [47, 48]
def count581 (b : Nat → Bool) : Nat := countLit b [43, 46, 47, 48]
def count585 (b : Nat → Bool) : Nat := countLit b [35, 36, 39, 42, 43, 46, 47, 48]
def count593 (b : Nat → Bool) : Nat := countLit b [50, 51]
def count595 (b : Nat → Bool) : Nat := countLit b [54, 56]
def count597 (b : Nat → Bool) : Nat := countLit b [50, 51, 54, 56]
def count601 (b : Nat → Bool) : Nat := countLit b [59, 60]
def count603 (b : Nat → Bool) : Nat := countLit b [61, 64]
def count605 (b : Nat → Bool) : Nat := countLit b [59, 60, 61, 64]
def count609 (b : Nat → Bool) : Nat := countLit b [50, 51, 54, 56, 59, 60, 61, 64]
def count617 (b : Nat → Bool) : Nat := countLit b [35, 36, 39, 42, 43, 46, 47, 48, 50, 51, 54, 56, 59, 60, 61, 64]
def count633 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15, 17, 19, 22, 25, 26, 28, 30, 33, 35, 36, 39, 42, 43, 46, 47, 48, 50, 51, 54, 56, 59, 60, 61, 64]
def count665 (b : Nat → Bool) : Nat := countLit b [65, 67]
def count667 (b : Nat → Bool) : Nat := countLit b [69, 72]
def count669 (b : Nat → Bool) : Nat := countLit b [65, 67, 69, 72]
def count673 (b : Nat → Bool) : Nat := countLit b [73, 75]
def count675 (b : Nat → Bool) : Nat := countLit b [77, 79]
def count677 (b : Nat → Bool) : Nat := countLit b [73, 75, 77, 79]
def count681 (b : Nat → Bool) : Nat := countLit b [65, 67, 69, 72, 73, 75, 77, 79]
def count689 (b : Nat → Bool) : Nat := countLit b [82, 83]
def count691 (b : Nat → Bool) : Nat := countLit b [86, 87]
def count693 (b : Nat → Bool) : Nat := countLit b [82, 83, 86, 87]
def count697 (b : Nat → Bool) : Nat := countLit b [89, 90]
def count699 (b : Nat → Bool) : Nat := countLit b [91, 94]
def count701 (b : Nat → Bool) : Nat := countLit b [89, 90, 91, 94]
def count705 (b : Nat → Bool) : Nat := countLit b [82, 83, 86, 87, 89, 90, 91, 94]
def count713 (b : Nat → Bool) : Nat := countLit b [65, 67, 69, 72, 73, 75, 77, 79, 82, 83, 86, 87, 89, 90, 91, 94]
def count729 (b : Nat → Bool) : Nat := countLit b [95, 96]
def count731 (b : Nat → Bool) : Nat := countLit b [97, 101]
def count733 (b : Nat → Bool) : Nat := countLit b [95, 96, 97, 101]
def count737 (b : Nat → Bool) : Nat := countLit b [103, 105]
def count739 (b : Nat → Bool) : Nat := countLit b [107, 109]
def count741 (b : Nat → Bool) : Nat := countLit b [103, 105, 107, 109]
def count745 (b : Nat → Bool) : Nat := countLit b [95, 96, 97, 101, 103, 105, 107, 109]
def count753 (b : Nat → Bool) : Nat := countLit b [112, 113]
def count755 (b : Nat → Bool) : Nat := countLit b [114, 118]
def count757 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 118]
def count761 (b : Nat → Bool) : Nat := countLit b [121, 123]
def count763 (b : Nat → Bool) : Nat := countLit b [125, 127]
def count765 (b : Nat → Bool) : Nat := countLit b [121, 123, 125, 127]
def count769 (b : Nat → Bool) : Nat := countLit b [112, 113, 114, 118, 121, 123, 125, 127]
def count777 (b : Nat → Bool) : Nat := countLit b [95, 96, 97, 101, 103, 105, 107, 109, 112, 113, 114, 118, 121, 123, 125, 127]
def count793 (b : Nat → Bool) : Nat := countLit b [65, 67, 69, 72, 73, 75, 77, 79, 82, 83, 86, 87, 89, 90, 91, 94, 95, 96, 97, 101, 103, 105, 107, 109, 112, 113, 114, 118, 121, 123, 125, 127]
def count825 (b : Nat → Bool) : Nat := countLit b [1, 4, 6, 7, 9, 10, 11, 15, 17, 19, 22, 25, 26, 28, 30, 33, 35, 36, 39, 42, 43, 46, 47, 48, 50, 51, 54, 56, 59, 60, 61, 64, 65, 67, 69, 72, 73, 75, 77, 79, 82, 83, 86, 87, 89, 90, 91, 94, 95, 96, 97, 101, 103, 105, 107, 109, 112, 113, 114, 118, 121, 123, 125, 127]
def count867 (b : Nat → Bool) : Nat := countLit b [-1, -4]
def count869 (b : Nat → Bool) : Nat := countLit b [-6, -7]
def count871 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7]
def count875 (b : Nat → Bool) : Nat := countLit b [-9, -10]
def count877 (b : Nat → Bool) : Nat := countLit b [-11, -15]
def count879 (b : Nat → Bool) : Nat := countLit b [-9, -10, -11, -15]
def count883 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15]
def count891 (b : Nat → Bool) : Nat := countLit b [-17, -19]
def count893 (b : Nat → Bool) : Nat := countLit b [-22, -25]
def count895 (b : Nat → Bool) : Nat := countLit b [-17, -19, -22, -25]
def count899 (b : Nat → Bool) : Nat := countLit b [-26, -28]
def count901 (b : Nat → Bool) : Nat := countLit b [-30, -33]
def count903 (b : Nat → Bool) : Nat := countLit b [-26, -28, -30, -33]
def count907 (b : Nat → Bool) : Nat := countLit b [-17, -19, -22, -25, -26, -28, -30, -33]
def count915 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33]
def count931 (b : Nat → Bool) : Nat := countLit b [-35, -36]
def count933 (b : Nat → Bool) : Nat := countLit b [-39, -42]
def count935 (b : Nat → Bool) : Nat := countLit b [-35, -36, -39, -42]
def count939 (b : Nat → Bool) : Nat := countLit b [-43, -46]
def count941 (b : Nat → Bool) : Nat := countLit b [-47, -48]
def count943 (b : Nat → Bool) : Nat := countLit b [-43, -46, -47, -48]
def count947 (b : Nat → Bool) : Nat := countLit b [-35, -36, -39, -42, -43, -46, -47, -48]
def count955 (b : Nat → Bool) : Nat := countLit b [-50, -51]
def count957 (b : Nat → Bool) : Nat := countLit b [-54, -56]
def count959 (b : Nat → Bool) : Nat := countLit b [-50, -51, -54, -56]
def count963 (b : Nat → Bool) : Nat := countLit b [-59, -60]
def count965 (b : Nat → Bool) : Nat := countLit b [-61, -64]
def count967 (b : Nat → Bool) : Nat := countLit b [-59, -60, -61, -64]
def count971 (b : Nat → Bool) : Nat := countLit b [-50, -51, -54, -56, -59, -60, -61, -64]
def count979 (b : Nat → Bool) : Nat := countLit b [-35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]
def count995 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64]
def count1019 (b : Nat → Bool) : Nat := countLit b [-65, -67]
def count1021 (b : Nat → Bool) : Nat := countLit b [-69, -72]
def count1023 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69, -72]
def count1027 (b : Nat → Bool) : Nat := countLit b [-73, -75]
def count1029 (b : Nat → Bool) : Nat := countLit b [-77, -79]
def count1031 (b : Nat → Bool) : Nat := countLit b [-73, -75, -77, -79]
def count1035 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69, -72, -73, -75, -77, -79]
def count1043 (b : Nat → Bool) : Nat := countLit b [-82, -83]
def count1045 (b : Nat → Bool) : Nat := countLit b [-86, -87]
def count1047 (b : Nat → Bool) : Nat := countLit b [-82, -83, -86, -87]
def count1051 (b : Nat → Bool) : Nat := countLit b [-89, -90]
def count1053 (b : Nat → Bool) : Nat := countLit b [-91, -94]
def count1055 (b : Nat → Bool) : Nat := countLit b [-89, -90, -91, -94]
def count1059 (b : Nat → Bool) : Nat := countLit b [-82, -83, -86, -87, -89, -90, -91, -94]
def count1067 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]
def count1083 (b : Nat → Bool) : Nat := countLit b [-95, -96]
def count1085 (b : Nat → Bool) : Nat := countLit b [-97, -101]
def count1087 (b : Nat → Bool) : Nat := countLit b [-95, -96, -97, -101]
def count1091 (b : Nat → Bool) : Nat := countLit b [-103, -105]
def count1093 (b : Nat → Bool) : Nat := countLit b [-107, -109]
def count1095 (b : Nat → Bool) : Nat := countLit b [-103, -105, -107, -109]
def count1099 (b : Nat → Bool) : Nat := countLit b [-95, -96, -97, -101, -103, -105, -107, -109]
def count1107 (b : Nat → Bool) : Nat := countLit b [-112, -113]
def count1109 (b : Nat → Bool) : Nat := countLit b [-114, -118]
def count1111 (b : Nat → Bool) : Nat := countLit b [-112, -113, -114, -118]
def count1115 (b : Nat → Bool) : Nat := countLit b [-121, -123]
def count1117 (b : Nat → Bool) : Nat := countLit b [-125, -127]
def count1119 (b : Nat → Bool) : Nat := countLit b [-121, -123, -125, -127]
def count1123 (b : Nat → Bool) : Nat := countLit b [-112, -113, -114, -118, -121, -123, -125, -127]
def count1131 (b : Nat → Bool) : Nat := countLit b [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]
def count1147 (b : Nat → Bool) : Nat := countLit b [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]
def count1171 (b : Nat → Bool) : Nat := countLit b [-1, -4, -6, -7, -9, -10, -11, -15, -17, -19, -22, -25, -26, -28, -30, -33, -35, -36, -39, -42, -43, -46, -47, -48, -50, -51, -54, -56, -59, -60, -61, -64, -65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94, -95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]
def count1195 (b : Nat → Bool) : Nat := countLit b [3, 5]
def count1197 (b : Nat → Bool) : Nat := countLit b [2, 3, 5]
def count1200 (b : Nat → Bool) : Nat := countLit b [8, 12]
def count1202 (b : Nat → Bool) : Nat := countLit b [13, 14]
def count1204 (b : Nat → Bool) : Nat := countLit b [8, 12, 13, 14]
def count1208 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14]
def count1215 (b : Nat → Bool) : Nat := countLit b [16, 18]
def count1217 (b : Nat → Bool) : Nat := countLit b [20, 21]
def count1219 (b : Nat → Bool) : Nat := countLit b [16, 18, 20, 21]
def count1223 (b : Nat → Bool) : Nat := countLit b [23, 24]
def count1225 (b : Nat → Bool) : Nat := countLit b [27, 29]
def count1227 (b : Nat → Bool) : Nat := countLit b [23, 24, 27, 29]
def count1231 (b : Nat → Bool) : Nat := countLit b [16, 18, 20, 21, 23, 24, 27, 29]
def count1239 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14, 16, 18, 20, 21, 23, 24, 27, 29]
def count1254 (b : Nat → Bool) : Nat := countLit b [31, 32]
def count1256 (b : Nat → Bool) : Nat := countLit b [34, 37]
def count1258 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37]
def count1262 (b : Nat → Bool) : Nat := countLit b [38, 40]
def count1264 (b : Nat → Bool) : Nat := countLit b [41, 44]
def count1266 (b : Nat → Bool) : Nat := countLit b [38, 40, 41, 44]
def count1270 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37, 38, 40, 41, 44]
def count1278 (b : Nat → Bool) : Nat := countLit b [45, 49]
def count1280 (b : Nat → Bool) : Nat := countLit b [52, 53]
def count1282 (b : Nat → Bool) : Nat := countLit b [45, 49, 52, 53]
def count1286 (b : Nat → Bool) : Nat := countLit b [55, 57]
def count1288 (b : Nat → Bool) : Nat := countLit b [58, 62]
def count1290 (b : Nat → Bool) : Nat := countLit b [55, 57, 58, 62]
def count1294 (b : Nat → Bool) : Nat := countLit b [45, 49, 52, 53, 55, 57, 58, 62]
def count1302 (b : Nat → Bool) : Nat := countLit b [31, 32, 34, 37, 38, 40, 41, 44, 45, 49, 52, 53, 55, 57, 58, 62]
def count1318 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14, 16, 18, 20, 21, 23, 24, 27, 29, 31, 32, 34, 37, 38, 40, 41, 44, 45, 49, 52, 53, 55, 57, 58, 62]
def count1349 (b : Nat → Bool) : Nat := countLit b [63, 66]
def count1351 (b : Nat → Bool) : Nat := countLit b [68, 70]
def count1353 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 70]
def count1357 (b : Nat → Bool) : Nat := countLit b [71, 74]
def count1359 (b : Nat → Bool) : Nat := countLit b [76, 78]
def count1361 (b : Nat → Bool) : Nat := countLit b [71, 74, 76, 78]
def count1365 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 70, 71, 74, 76, 78]
def count1373 (b : Nat → Bool) : Nat := countLit b [80, 81]
def count1375 (b : Nat → Bool) : Nat := countLit b [84, 85]
def count1377 (b : Nat → Bool) : Nat := countLit b [80, 81, 84, 85]
def count1381 (b : Nat → Bool) : Nat := countLit b [88, 92]
def count1383 (b : Nat → Bool) : Nat := countLit b [93, 98]
def count1385 (b : Nat → Bool) : Nat := countLit b [88, 92, 93, 98]
def count1389 (b : Nat → Bool) : Nat := countLit b [80, 81, 84, 85, 88, 92, 93, 98]
def count1397 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 70, 71, 74, 76, 78, 80, 81, 84, 85, 88, 92, 93, 98]
def count1413 (b : Nat → Bool) : Nat := countLit b [99, 100]
def count1415 (b : Nat → Bool) : Nat := countLit b [102, 104]
def count1417 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 104]
def count1421 (b : Nat → Bool) : Nat := countLit b [106, 108]
def count1423 (b : Nat → Bool) : Nat := countLit b [110, 111]
def count1425 (b : Nat → Bool) : Nat := countLit b [106, 108, 110, 111]
def count1429 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 104, 106, 108, 110, 111]
def count1437 (b : Nat → Bool) : Nat := countLit b [115, 116]
def count1439 (b : Nat → Bool) : Nat := countLit b [117, 119]
def count1441 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 119]
def count1445 (b : Nat → Bool) : Nat := countLit b [120, 122]
def count1447 (b : Nat → Bool) : Nat := countLit b [124, 126]
def count1449 (b : Nat → Bool) : Nat := countLit b [120, 122, 124, 126]
def count1453 (b : Nat → Bool) : Nat := countLit b [115, 116, 117, 119, 120, 122, 124, 126]
def count1461 (b : Nat → Bool) : Nat := countLit b [99, 100, 102, 104, 106, 108, 110, 111, 115, 116, 117, 119, 120, 122, 124, 126]
def count1477 (b : Nat → Bool) : Nat := countLit b [63, 66, 68, 70, 71, 74, 76, 78, 80, 81, 84, 85, 88, 92, 93, 98, 99, 100, 102, 104, 106, 108, 110, 111, 115, 116, 117, 119, 120, 122, 124, 126]
def count1509 (b : Nat → Bool) : Nat := countLit b [2, 3, 5, 8, 12, 13, 14, 16, 18, 20, 21, 23, 24, 27, 29, 31, 32, 34, 37, 38, 40, 41, 44, 45, 49, 52, 53, 55, 57, 58, 62, 63, 66, 68, 70, 71, 74, 76, 78, 80, 81, 84, 85, 88, 92, 93, 98, 99, 100, 102, 104, 106, 108, 110, 111, 115, 116, 117, 119, 120, 122, 124, 126]
def count1551 (b : Nat → Bool) : Nat := countLit b [-3, -5]
def count1553 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5]
def count1556 (b : Nat → Bool) : Nat := countLit b [-8, -12]
def count1558 (b : Nat → Bool) : Nat := countLit b [-13, -14]
def count1560 (b : Nat → Bool) : Nat := countLit b [-8, -12, -13, -14]
def count1564 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14]
def count1571 (b : Nat → Bool) : Nat := countLit b [-16, -18]
def count1573 (b : Nat → Bool) : Nat := countLit b [-20, -21]
def count1575 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20, -21]
def count1579 (b : Nat → Bool) : Nat := countLit b [-23, -24]
def count1581 (b : Nat → Bool) : Nat := countLit b [-27, -29]
def count1583 (b : Nat → Bool) : Nat := countLit b [-23, -24, -27, -29]
def count1587 (b : Nat → Bool) : Nat := countLit b [-16, -18, -20, -21, -23, -24, -27, -29]
def count1595 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29]
def count1610 (b : Nat → Bool) : Nat := countLit b [-31, -32]
def count1612 (b : Nat → Bool) : Nat := countLit b [-34, -37]
def count1614 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37]
def count1618 (b : Nat → Bool) : Nat := countLit b [-38, -40]
def count1620 (b : Nat → Bool) : Nat := countLit b [-41, -44]
def count1622 (b : Nat → Bool) : Nat := countLit b [-38, -40, -41, -44]
def count1626 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37, -38, -40, -41, -44]
def count1634 (b : Nat → Bool) : Nat := countLit b [-45, -49]
def count1636 (b : Nat → Bool) : Nat := countLit b [-52, -53]
def count1638 (b : Nat → Bool) : Nat := countLit b [-45, -49, -52, -53]
def count1642 (b : Nat → Bool) : Nat := countLit b [-55, -57]
def count1644 (b : Nat → Bool) : Nat := countLit b [-58, -62]
def count1646 (b : Nat → Bool) : Nat := countLit b [-55, -57, -58, -62]
def count1650 (b : Nat → Bool) : Nat := countLit b [-45, -49, -52, -53, -55, -57, -58, -62]
def count1658 (b : Nat → Bool) : Nat := countLit b [-31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]
def count1674 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]
def count1697 (b : Nat → Bool) : Nat := countLit b [-63, -66]
def count1699 (b : Nat → Bool) : Nat := countLit b [-68, -70]
def count1701 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -70]
def count1705 (b : Nat → Bool) : Nat := countLit b [-71, -74]
def count1707 (b : Nat → Bool) : Nat := countLit b [-76, -78]
def count1709 (b : Nat → Bool) : Nat := countLit b [-71, -74, -76, -78]
def count1713 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -70, -71, -74, -76, -78]
def count1721 (b : Nat → Bool) : Nat := countLit b [-80, -81]
def count1723 (b : Nat → Bool) : Nat := countLit b [-84, -85]
def count1725 (b : Nat → Bool) : Nat := countLit b [-80, -81, -84, -85]
def count1729 (b : Nat → Bool) : Nat := countLit b [-88, -92]
def count1731 (b : Nat → Bool) : Nat := countLit b [-93, -98]
def count1733 (b : Nat → Bool) : Nat := countLit b [-88, -92, -93, -98]
def count1737 (b : Nat → Bool) : Nat := countLit b [-80, -81, -84, -85, -88, -92, -93, -98]
def count1745 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98]
def count1761 (b : Nat → Bool) : Nat := countLit b [-99, -100]
def count1763 (b : Nat → Bool) : Nat := countLit b [-102, -104]
def count1765 (b : Nat → Bool) : Nat := countLit b [-99, -100, -102, -104]
def count1769 (b : Nat → Bool) : Nat := countLit b [-106, -108]
def count1771 (b : Nat → Bool) : Nat := countLit b [-110, -111]
def count1773 (b : Nat → Bool) : Nat := countLit b [-106, -108, -110, -111]
def count1777 (b : Nat → Bool) : Nat := countLit b [-99, -100, -102, -104, -106, -108, -110, -111]
def count1785 (b : Nat → Bool) : Nat := countLit b [-115, -116]
def count1787 (b : Nat → Bool) : Nat := countLit b [-117, -119]
def count1789 (b : Nat → Bool) : Nat := countLit b [-115, -116, -117, -119]
def count1793 (b : Nat → Bool) : Nat := countLit b [-120, -122]
def count1795 (b : Nat → Bool) : Nat := countLit b [-124, -126]
def count1797 (b : Nat → Bool) : Nat := countLit b [-120, -122, -124, -126]
def count1801 (b : Nat → Bool) : Nat := countLit b [-115, -116, -117, -119, -120, -122, -124, -126]
def count1809 (b : Nat → Bool) : Nat := countLit b [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]
def count1825 (b : Nat → Bool) : Nat := countLit b [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]
def count1848 (b : Nat → Bool) : Nat := countLit b [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62, -63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]
def valuationOf (b : Nat → Bool) (i : Nat) : Bool := (if i < 935 then (if i < 467 then (if i < 233 then (if i < 116 then (if i < 58 then (if i < 29 then (if i < 14 then (if i < 7 then (if i < 3 then (if i < 1 then false else (if i < 2 then b 1 else b 2)) else (if i < 5 then (if i < 4 then b 3 else b 4) else (if i < 6 then b 5 else b 6))) else (if i < 10 then (if i < 8 then b 7 else (if i < 9 then b 8 else b 9)) else (if i < 12 then (if i < 11 then b 10 else b 11) else (if i < 13 then b 12 else b 13)))) else (if i < 21 then (if i < 17 then (if i < 15 then b 14 else (if i < 16 then b 15 else b 16)) else (if i < 19 then (if i < 18 then b 17 else b 18) else (if i < 20 then b 19 else b 20))) else (if i < 25 then (if i < 23 then (if i < 22 then b 21 else b 22) else (if i < 24 then b 23 else b 24)) else (if i < 27 then (if i < 26 then b 25 else b 26) else (if i < 28 then b 27 else b 28))))) else (if i < 43 then (if i < 36 then (if i < 32 then (if i < 30 then b 29 else (if i < 31 then b 30 else b 31)) else (if i < 34 then (if i < 33 then b 32 else b 33) else (if i < 35 then b 34 else b 35))) else (if i < 39 then (if i < 37 then b 36 else (if i < 38 then b 37 else b 38)) else (if i < 41 then (if i < 40 then b 39 else b 40) else (if i < 42 then b 41 else b 42)))) else (if i < 50 then (if i < 46 then (if i < 44 then b 43 else (if i < 45 then b 44 else b 45)) else (if i < 48 then (if i < 47 then b 46 else b 47) else (if i < 49 then b 48 else b 49))) else (if i < 54 then (if i < 52 then (if i < 51 then b 50 else b 51) else (if i < 53 then b 52 else b 53)) else (if i < 56 then (if i < 55 then b 54 else b 55) else (if i < 57 then b 56 else b 57)))))) else (if i < 87 then (if i < 72 then (if i < 65 then (if i < 61 then (if i < 59 then b 58 else (if i < 60 then b 59 else b 60)) else (if i < 63 then (if i < 62 then b 61 else b 62) else (if i < 64 then b 63 else b 64))) else (if i < 68 then (if i < 66 then b 65 else (if i < 67 then b 66 else b 67)) else (if i < 70 then (if i < 69 then b 68 else b 69) else (if i < 71 then b 70 else b 71)))) else (if i < 79 then (if i < 75 then (if i < 73 then b 72 else (if i < 74 then b 73 else b 74)) else (if i < 77 then (if i < 76 then b 75 else b 76) else (if i < 78 then b 77 else b 78))) else (if i < 83 then (if i < 81 then (if i < 80 then b 79 else b 80) else (if i < 82 then b 81 else b 82)) else (if i < 85 then (if i < 84 then b 83 else b 84) else (if i < 86 then b 85 else b 86))))) else (if i < 101 then (if i < 94 then (if i < 90 then (if i < 88 then b 87 else (if i < 89 then b 88 else b 89)) else (if i < 92 then (if i < 91 then b 90 else b 91) else (if i < 93 then b 92 else b 93))) else (if i < 97 then (if i < 95 then b 94 else (if i < 96 then b 95 else b 96)) else (if i < 99 then (if i < 98 then b 97 else b 98) else (if i < 100 then b 99 else b 100)))) else (if i < 108 then (if i < 104 then (if i < 102 then b 101 else (if i < 103 then b 102 else b 103)) else (if i < 106 then (if i < 105 then b 104 else b 105) else (if i < 107 then b 106 else b 107))) else (if i < 112 then (if i < 110 then (if i < 109 then b 108 else b 109) else (if i < 111 then b 110 else b 111)) else (if i < 114 then (if i < 113 then b 112 else b 113) else (if i < 115 then b 114 else b 115))))))) else (if i < 174 then (if i < 145 then (if i < 130 then (if i < 123 then (if i < 119 then (if i < 117 then b 116 else (if i < 118 then b 117 else b 118)) else (if i < 121 then (if i < 120 then b 119 else b 120) else (if i < 122 then b 121 else b 122))) else (if i < 126 then (if i < 124 then b 123 else (if i < 125 then b 124 else b 125)) else (if i < 128 then (if i < 127 then b 126 else b 127) else (if i < 129 then b 128 else b 129)))) else (if i < 137 then (if i < 133 then (if i < 131 then b 130 else (if i < 132 then b 131 else b 132)) else (if i < 135 then (if i < 134 then b 133 else b 134) else (if i < 136 then b 135 else b 136))) else (if i < 141 then (if i < 139 then (if i < 138 then b 137 else b 138) else (if i < 140 then b 139 else b 140)) else (if i < 143 then (if i < 142 then b 141 else b 142) else (if i < 144 then b 143 else b 144))))) else (if i < 159 then (if i < 152 then (if i < 148 then (if i < 146 then b 145 else (if i < 147 then b 146 else b 147)) else (if i < 150 then (if i < 149 then b 148 else b 149) else (if i < 151 then b 150 else b 151))) else (if i < 155 then (if i < 153 then b 152 else (if i < 154 then b 153 else b 154)) else (if i < 157 then (if i < 156 then b 155 else b 156) else (if i < 158 then b 157 else b 158)))) else (if i < 166 then (if i < 162 then (if i < 160 then b 159 else (if i < 161 then b 160 else b 161)) else (if i < 164 then (if i < 163 then b 162 else b 163) else (if i < 165 then b 164 else b 165))) else (if i < 170 then (if i < 168 then (if i < 167 then b 166 else b 167) else (if i < 169 then b 168 else b 169)) else (if i < 172 then (if i < 171 then b 170 else b 171) else (if i < 173 then b 172 else b 173)))))) else (if i < 203 then (if i < 188 then (if i < 181 then (if i < 177 then (if i < 175 then b 174 else (if i < 176 then b 175 else b 176)) else (if i < 179 then (if i < 178 then b 177 else b 178) else (if i < 180 then b 179 else b 180))) else (if i < 184 then (if i < 182 then b 181 else (if i < 183 then b 182 else b 183)) else (if i < 186 then (if i < 185 then b 184 else b 185) else (if i < 187 then b 186 else b 187)))) else (if i < 195 then (if i < 191 then (if i < 189 then b 188 else (if i < 190 then b 189 else b 190)) else (if i < 193 then (if i < 192 then b 191 else b 192) else (if i < 194 then b 193 else b 194))) else (if i < 199 then (if i < 197 then (if i < 196 then b 195 else b 196) else (if i < 198 then b 197 else b 198)) else (if i < 201 then (if i < 200 then b 199 else b 200) else (if i < 202 then b 201 else b 202))))) else (if i < 218 then (if i < 210 then (if i < 206 then (if i < 204 then b 203 else (if i < 205 then b 204 else b 205)) else (if i < 208 then (if i < 207 then b 206 else b 207) else (if i < 209 then b 208 else b 209))) else (if i < 214 then (if i < 212 then (if i < 211 then b 210 else b 211) else (if i < 213 then b 212 else b 213)) else (if i < 216 then (if i < 215 then b 214 else b 215) else (if i < 217 then b 216 else b 217)))) else (if i < 225 then (if i < 221 then (if i < 219 then b 218 else (if i < 220 then b 219 else b 220)) else (if i < 223 then (if i < 222 then b 221 else b 222) else (if i < 224 then b 223 else b 224))) else (if i < 229 then (if i < 227 then (if i < 226 then b 225 else b 226) else (if i < 228 then b 227 else b 228)) else (if i < 231 then (if i < 230 then b 229 else b 230) else (if i < 232 then b 231 else b 232)))))))) else (if i < 350 then (if i < 291 then (if i < 262 then (if i < 247 then (if i < 240 then (if i < 236 then (if i < 234 then b 233 else (if i < 235 then b 234 else b 235)) else (if i < 238 then (if i < 237 then b 236 else b 237) else (if i < 239 then b 238 else b 239))) else (if i < 243 then (if i < 241 then b 240 else (if i < 242 then b 241 else b 242)) else (if i < 245 then (if i < 244 then b 243 else b 244) else (if i < 246 then b 245 else b 246)))) else (if i < 254 then (if i < 250 then (if i < 248 then b 247 else (if i < 249 then b 248 else b 249)) else (if i < 252 then (if i < 251 then b 250 else b 251) else (if i < 253 then b 252 else b 253))) else (if i < 258 then (if i < 256 then (if i < 255 then b 254 else decide (1 ≤ count255 b)) else (if i < 257 then decide (2 ≤ count255 b) else decide (1 ≤ count257 b))) else (if i < 260 then (if i < 259 then decide (2 ≤ count257 b) else decide (1 ≤ count259 b)) else (if i < 261 then decide (2 ≤ count259 b) else decide (1 ≤ count261 b)))))) else (if i < 276 then (if i < 269 then (if i < 265 then (if i < 263 then decide (2 ≤ count261 b) else (if i < 264 then decide (1 ≤ count263 b) else decide (2 ≤ count263 b))) else (if i < 267 then (if i < 266 then decide (1 ≤ count265 b) else decide (2 ≤ count265 b)) else (if i < 268 then decide (1 ≤ count267 b) else decide (2 ≤ count267 b)))) else (if i < 272 then (if i < 270 then decide (1 ≤ count269 b) else (if i < 271 then decide (2 ≤ count269 b) else decide (1 ≤ count271 b))) else (if i < 274 then (if i < 273 then decide (2 ≤ count271 b) else decide (1 ≤ count273 b)) else (if i < 275 then decide (2 ≤ count273 b) else decide (1 ≤ count275 b))))) else (if i < 283 then (if i < 279 then (if i < 277 then decide (2 ≤ count275 b) else (if i < 278 then decide (1 ≤ count277 b) else decide (2 ≤ count277 b))) else (if i < 281 then (if i < 280 then decide (1 ≤ count279 b) else decide (2 ≤ count279 b)) else (if i < 282 then decide (1 ≤ count281 b) else decide (2 ≤ count281 b)))) else (if i < 287 then (if i < 285 then (if i < 284 then decide (1 ≤ count283 b) else decide (2 ≤ count283 b)) else (if i < 286 then decide (1 ≤ count285 b) else decide (2 ≤ count285 b))) else (if i < 289 then (if i < 288 then decide (1 ≤ count287 b) else decide (2 ≤ count287 b)) else (if i < 290 then decide (1 ≤ count289 b) else decide (2 ≤ count289 b))))))) else (if i < 320 then (if i < 305 then (if i < 298 then (if i < 294 then (if i < 292 then decide (1 ≤ count291 b) else (if i < 293 then decide (2 ≤ count291 b) else decide (1 ≤ count293 b))) else (if i < 296 then (if i < 295 then decide (2 ≤ count293 b) else decide (1 ≤ count295 b)) else (if i < 297 then decide (2 ≤ count295 b) else decide (1 ≤ count297 b)))) else (if i < 301 then (if i < 299 then decide (2 ≤ count297 b) else (if i < 300 then decide (1 ≤ count299 b) else decide (2 ≤ count299 b))) else (if i < 303 then (if i < 302 then decide (1 ≤ count301 b) else decide (2 ≤ count301 b)) else (if i < 304 then decide (1 ≤ count303 b) else decide (2 ≤ count303 b))))) else (if i < 312 then (if i < 308 then (if i < 306 then decide (1 ≤ count305 b) else (if i < 307 then decide (2 ≤ count305 b) else decide (1 ≤ count307 b))) else (if i < 310 then (if i < 309 then decide (2 ≤ count307 b) else decide (1 ≤ count309 b)) else (if i < 311 then decide (2 ≤ count309 b) else decide (1 ≤ count311 b)))) else (if i < 316 then (if i < 314 then (if i < 313 then decide (2 ≤ count311 b) else decide (1 ≤ count313 b)) else (if i < 315 then decide (2 ≤ count313 b) else decide (1 ≤ count315 b))) else (if i < 318 then (if i < 317 then decide (2 ≤ count315 b) else decide (1 ≤ count317 b)) else (if i < 319 then decide (2 ≤ count317 b) else decide (1 ≤ count319 b)))))) else (if i < 335 then (if i < 327 then (if i < 323 then (if i < 321 then decide (2 ≤ count319 b) else (if i < 322 then decide (1 ≤ count321 b) else decide (2 ≤ count321 b))) else (if i < 325 then (if i < 324 then decide (1 ≤ count323 b) else decide (2 ≤ count323 b)) else (if i < 326 then decide (1 ≤ count325 b) else decide (2 ≤ count325 b)))) else (if i < 331 then (if i < 329 then (if i < 328 then decide (1 ≤ count327 b) else decide (2 ≤ count327 b)) else (if i < 330 then decide (1 ≤ count329 b) else decide (2 ≤ count329 b))) else (if i < 333 then (if i < 332 then decide (1 ≤ count331 b) else decide (2 ≤ count331 b)) else (if i < 334 then decide (1 ≤ count333 b) else decide (2 ≤ count333 b))))) else (if i < 342 then (if i < 338 then (if i < 336 then decide (1 ≤ count335 b) else (if i < 337 then decide (2 ≤ count335 b) else decide (1 ≤ count337 b))) else (if i < 340 then (if i < 339 then decide (2 ≤ count337 b) else decide (1 ≤ count339 b)) else (if i < 341 then decide (2 ≤ count339 b) else decide (1 ≤ count341 b)))) else (if i < 346 then (if i < 344 then (if i < 343 then decide (2 ≤ count341 b) else decide (1 ≤ count343 b)) else (if i < 345 then decide (2 ≤ count343 b) else decide (1 ≤ count345 b))) else (if i < 348 then (if i < 347 then decide (2 ≤ count345 b) else decide (1 ≤ count347 b)) else (if i < 349 then decide (2 ≤ count347 b) else decide (1 ≤ count349 b)))))))) else (if i < 408 then (if i < 379 then (if i < 364 then (if i < 357 then (if i < 353 then (if i < 351 then decide (2 ≤ count349 b) else (if i < 352 then decide (1 ≤ count351 b) else decide (2 ≤ count351 b))) else (if i < 355 then (if i < 354 then decide (1 ≤ count353 b) else decide (2 ≤ count353 b)) else (if i < 356 then decide (1 ≤ count355 b) else decide (2 ≤ count355 b)))) else (if i < 360 then (if i < 358 then decide (1 ≤ count357 b) else (if i < 359 then decide (2 ≤ count357 b) else decide (1 ≤ count359 b))) else (if i < 362 then (if i < 361 then decide (2 ≤ count359 b) else decide (1 ≤ count361 b)) else (if i < 363 then decide (2 ≤ count361 b) else decide (1 ≤ count363 b))))) else (if i < 371 then (if i < 367 then (if i < 365 then decide (2 ≤ count363 b) else (if i < 366 then decide (1 ≤ count365 b) else decide (2 ≤ count365 b))) else (if i < 369 then (if i < 368 then decide (1 ≤ count367 b) else decide (2 ≤ count367 b)) else (if i < 370 then decide (1 ≤ count369 b) else decide (2 ≤ count369 b)))) else (if i < 375 then (if i < 373 then (if i < 372 then decide (1 ≤ count371 b) else decide (2 ≤ count371 b)) else (if i < 374 then decide (1 ≤ count373 b) else decide (2 ≤ count373 b))) else (if i < 377 then (if i < 376 then decide (1 ≤ count375 b) else decide (2 ≤ count375 b)) else (if i < 378 then decide (1 ≤ count377 b) else decide (2 ≤ count377 b)))))) else (if i < 393 then (if i < 386 then (if i < 382 then (if i < 380 then decide (1 ≤ count379 b) else (if i < 381 then decide (2 ≤ count379 b) else decide (1 ≤ count381 b))) else (if i < 384 then (if i < 383 then decide (2 ≤ count381 b) else decide (1 ≤ count383 b)) else (if i < 385 then decide (2 ≤ count383 b) else decide (1 ≤ count385 b)))) else (if i < 389 then (if i < 387 then decide (2 ≤ count385 b) else (if i < 388 then decide (1 ≤ count387 b) else decide (2 ≤ count387 b))) else (if i < 391 then (if i < 390 then decide (1 ≤ count389 b) else decide (2 ≤ count389 b)) else (if i < 392 then decide (1 ≤ count391 b) else decide (2 ≤ count391 b))))) else (if i < 400 then (if i < 396 then (if i < 394 then decide (1 ≤ count393 b) else (if i < 395 then decide (2 ≤ count393 b) else decide (1 ≤ count395 b))) else (if i < 398 then (if i < 397 then decide (2 ≤ count395 b) else decide (1 ≤ count397 b)) else (if i < 399 then decide (2 ≤ count397 b) else decide (1 ≤ count399 b)))) else (if i < 404 then (if i < 402 then (if i < 401 then decide (2 ≤ count399 b) else decide (1 ≤ count401 b)) else (if i < 403 then decide (2 ≤ count401 b) else decide (1 ≤ count403 b))) else (if i < 406 then (if i < 405 then decide (2 ≤ count403 b) else decide (1 ≤ count405 b)) else (if i < 407 then decide (2 ≤ count405 b) else decide (1 ≤ count407 b))))))) else (if i < 437 then (if i < 422 then (if i < 415 then (if i < 411 then (if i < 409 then decide (2 ≤ count407 b) else (if i < 410 then decide (1 ≤ count409 b) else decide (2 ≤ count409 b))) else (if i < 413 then (if i < 412 then decide (1 ≤ count411 b) else decide (2 ≤ count411 b)) else (if i < 414 then decide (1 ≤ count413 b) else decide (2 ≤ count413 b)))) else (if i < 418 then (if i < 416 then decide (1 ≤ count415 b) else (if i < 417 then decide (2 ≤ count415 b) else decide (1 ≤ count417 b))) else (if i < 420 then (if i < 419 then decide (2 ≤ count417 b) else decide (1 ≤ count419 b)) else (if i < 421 then decide (2 ≤ count419 b) else decide (1 ≤ count421 b))))) else (if i < 429 then (if i < 425 then (if i < 423 then decide (2 ≤ count421 b) else (if i < 424 then decide (1 ≤ count423 b) else decide (2 ≤ count423 b))) else (if i < 427 then (if i < 426 then decide (1 ≤ count425 b) else decide (2 ≤ count425 b)) else (if i < 428 then decide (1 ≤ count427 b) else decide (2 ≤ count427 b)))) else (if i < 433 then (if i < 431 then (if i < 430 then decide (1 ≤ count429 b) else decide (2 ≤ count429 b)) else (if i < 432 then decide (1 ≤ count431 b) else decide (2 ≤ count431 b))) else (if i < 435 then (if i < 434 then decide (1 ≤ count433 b) else decide (2 ≤ count433 b)) else (if i < 436 then decide (1 ≤ count435 b) else decide (2 ≤ count435 b)))))) else (if i < 452 then (if i < 444 then (if i < 440 then (if i < 438 then decide (1 ≤ count437 b) else (if i < 439 then decide (2 ≤ count437 b) else decide (1 ≤ count439 b))) else (if i < 442 then (if i < 441 then decide (2 ≤ count439 b) else decide (1 ≤ count441 b)) else (if i < 443 then decide (2 ≤ count441 b) else decide (1 ≤ count443 b)))) else (if i < 448 then (if i < 446 then (if i < 445 then decide (2 ≤ count443 b) else decide (1 ≤ count445 b)) else (if i < 447 then decide (2 ≤ count445 b) else decide (1 ≤ count447 b))) else (if i < 450 then (if i < 449 then decide (2 ≤ count447 b) else decide (1 ≤ count449 b)) else (if i < 451 then decide (2 ≤ count449 b) else decide (1 ≤ count451 b))))) else (if i < 459 then (if i < 455 then (if i < 453 then decide (2 ≤ count451 b) else (if i < 454 then decide (1 ≤ count453 b) else decide (2 ≤ count453 b))) else (if i < 457 then (if i < 456 then decide (1 ≤ count455 b) else decide (2 ≤ count455 b)) else (if i < 458 then decide (1 ≤ count457 b) else decide (2 ≤ count457 b)))) else (if i < 463 then (if i < 461 then (if i < 460 then decide (1 ≤ count459 b) else decide (2 ≤ count459 b)) else (if i < 462 then decide (1 ≤ count461 b) else decide (2 ≤ count461 b))) else (if i < 465 then (if i < 464 then decide (1 ≤ count463 b) else decide (2 ≤ count463 b)) else (if i < 466 then decide (1 ≤ count465 b) else decide (2 ≤ count465 b)))))))))) else (if i < 701 then (if i < 584 then (if i < 525 then (if i < 496 then (if i < 481 then (if i < 474 then (if i < 470 then (if i < 468 then decide (1 ≤ count467 b) else (if i < 469 then decide (2 ≤ count467 b) else decide (1 ≤ count469 b))) else (if i < 472 then (if i < 471 then decide (2 ≤ count469 b) else decide (1 ≤ count471 b)) else (if i < 473 then decide (2 ≤ count471 b) else decide (1 ≤ count473 b)))) else (if i < 477 then (if i < 475 then decide (2 ≤ count473 b) else (if i < 476 then decide (1 ≤ count475 b) else decide (2 ≤ count475 b))) else (if i < 479 then (if i < 478 then decide (1 ≤ count477 b) else decide (2 ≤ count477 b)) else (if i < 480 then decide (1 ≤ count479 b) else decide (2 ≤ count479 b))))) else (if i < 488 then (if i < 484 then (if i < 482 then decide (1 ≤ count481 b) else (if i < 483 then decide (2 ≤ count481 b) else decide (1 ≤ count483 b))) else (if i < 486 then (if i < 485 then decide (2 ≤ count483 b) else decide (1 ≤ count485 b)) else (if i < 487 then decide (2 ≤ count485 b) else decide (1 ≤ count487 b)))) else (if i < 492 then (if i < 490 then (if i < 489 then decide (2 ≤ count487 b) else decide (1 ≤ count489 b)) else (if i < 491 then decide (2 ≤ count489 b) else decide (1 ≤ count491 b))) else (if i < 494 then (if i < 493 then decide (2 ≤ count491 b) else decide (1 ≤ count493 b)) else (if i < 495 then decide (2 ≤ count493 b) else decide (1 ≤ count495 b)))))) else (if i < 510 then (if i < 503 then (if i < 499 then (if i < 497 then decide (2 ≤ count495 b) else (if i < 498 then decide (1 ≤ count497 b) else decide (2 ≤ count497 b))) else (if i < 501 then (if i < 500 then decide (1 ≤ count499 b) else decide (2 ≤ count499 b)) else (if i < 502 then decide (1 ≤ count501 b) else decide (2 ≤ count501 b)))) else (if i < 506 then (if i < 504 then decide (1 ≤ count503 b) else (if i < 505 then decide (2 ≤ count503 b) else decide (1 ≤ count505 b))) else (if i < 508 then (if i < 507 then decide (2 ≤ count505 b) else decide (1 ≤ count507 b)) else (if i < 509 then decide (2 ≤ count507 b) else decide (1 ≤ count509 b))))) else (if i < 517 then (if i < 513 then (if i < 511 then decide (2 ≤ count509 b) else (if i < 512 then decide (3 ≤ count509 b) else decide (4 ≤ count509 b))) else (if i < 515 then (if i < 514 then decide (1 ≤ count513 b) else decide (2 ≤ count513 b)) else (if i < 516 then decide (1 ≤ count515 b) else decide (2 ≤ count515 b)))) else (if i < 521 then (if i < 519 then (if i < 518 then decide (1 ≤ count517 b) else decide (2 ≤ count517 b)) else (if i < 520 then decide (3 ≤ count517 b) else decide (4 ≤ count517 b))) else (if i < 523 then (if i < 522 then decide (1 ≤ count521 b) else decide (2 ≤ count521 b)) else (if i < 524 then decide (3 ≤ count521 b) else decide (4 ≤ count521 b))))))) else (if i < 554 then (if i < 539 then (if i < 532 then (if i < 528 then (if i < 526 then decide (5 ≤ count521 b) else (if i < 527 then decide (6 ≤ count521 b) else decide (7 ≤ count521 b))) else (if i < 530 then (if i < 529 then decide (8 ≤ count521 b) else decide (1 ≤ count529 b)) else (if i < 531 then decide (2 ≤ count529 b) else decide (1 ≤ count531 b)))) else (if i < 535 then (if i < 533 then decide (2 ≤ count531 b) else (if i < 534 then decide (1 ≤ count533 b) else decide (2 ≤ count533 b))) else (if i < 537 then (if i < 536 then decide (3 ≤ count533 b) else decide (4 ≤ count533 b)) else (if i < 538 then decide (1 ≤ count537 b) else decide (2 ≤ count537 b))))) else (if i < 546 then (if i < 542 then (if i < 540 then decide (1 ≤ count539 b) else (if i < 541 then decide (2 ≤ count539 b) else decide (1 ≤ count541 b))) else (if i < 544 then (if i < 543 then decide (2 ≤ count541 b) else decide (3 ≤ count541 b)) else (if i < 545 then decide (4 ≤ count541 b) else decide (1 ≤ count545 b)))) else (if i < 550 then (if i < 548 then (if i < 547 then decide (2 ≤ count545 b) else decide (3 ≤ count545 b)) else (if i < 549 then decide (4 ≤ count545 b) else decide (5 ≤ count545 b))) else (if i < 552 then (if i < 551 then decide (6 ≤ count545 b) else decide (7 ≤ count545 b)) else (if i < 553 then decide (8 ≤ count545 b) else decide (1 ≤ count553 b)))))) else (if i < 569 then (if i < 561 then (if i < 557 then (if i < 555 then decide (2 ≤ count553 b) else (if i < 556 then decide (3 ≤ count553 b) else decide (4 ≤ count553 b))) else (if i < 559 then (if i < 558 then decide (5 ≤ count553 b) else decide (6 ≤ count553 b)) else (if i < 560 then decide (7 ≤ count553 b) else decide (8 ≤ count553 b)))) else (if i < 565 then (if i < 563 then (if i < 562 then decide (9 ≤ count553 b) else decide (10 ≤ count553 b)) else (if i < 564 then decide (11 ≤ count553 b) else decide (12 ≤ count553 b))) else (if i < 567 then (if i < 566 then decide (13 ≤ count553 b) else decide (14 ≤ count553 b)) else (if i < 568 then decide (15 ≤ count553 b) else decide (16 ≤ count553 b))))) else (if i < 576 then (if i < 572 then (if i < 570 then decide (1 ≤ count569 b) else (if i < 571 then decide (2 ≤ count569 b) else decide (1 ≤ count571 b))) else (if i < 574 then (if i < 573 then decide (2 ≤ count571 b) else decide (1 ≤ count573 b)) else (if i < 575 then decide (2 ≤ count573 b) else decide (3 ≤ count573 b)))) else (if i < 580 then (if i < 578 then (if i < 577 then decide (4 ≤ count573 b) else decide (1 ≤ count577 b)) else (if i < 579 then decide (2 ≤ count577 b) else decide (1 ≤ count579 b))) else (if i < 582 then (if i < 581 then decide (2 ≤ count579 b) else decide (1 ≤ count581 b)) else (if i < 583 then decide (2 ≤ count581 b) else decide (3 ≤ count581 b)))))))) else (if i < 642 then (if i < 613 then (if i < 598 then (if i < 591 then (if i < 587 then (if i < 585 then decide (4 ≤ count581 b) else (if i < 586 then decide (1 ≤ count585 b) else decide (2 ≤ count585 b))) else (if i < 589 then (if i < 588 then decide (3 ≤ count585 b) else decide (4 ≤ count585 b)) else (if i < 590 then decide (5 ≤ count585 b) else decide (6 ≤ count585 b)))) else (if i < 594 then (if i < 592 then decide (7 ≤ count585 b) else (if i < 593 then decide (8 ≤ count585 b) else decide (1 ≤ count593 b))) else (if i < 596 then (if i < 595 then decide (2 ≤ count593 b) else decide (1 ≤ count595 b)) else (if i < 597 then decide (2 ≤ count595 b) else decide (1 ≤ count597 b))))) else (if i < 605 then (if i < 601 then (if i < 599 then decide (2 ≤ count597 b) else (if i < 600 then decide (3 ≤ count597 b) else decide (4 ≤ count597 b))) else (if i < 603 then (if i < 602 then decide (1 ≤ count601 b) else decide (2 ≤ count601 b)) else (if i < 604 then decide (1 ≤ count603 b) else decide (2 ≤ count603 b)))) else (if i < 609 then (if i < 607 then (if i < 606 then decide (1 ≤ count605 b) else decide (2 ≤ count605 b)) else (if i < 608 then decide (3 ≤ count605 b) else decide (4 ≤ count605 b))) else (if i < 611 then (if i < 610 then decide (1 ≤ count609 b) else decide (2 ≤ count609 b)) else (if i < 612 then decide (3 ≤ count609 b) else decide (4 ≤ count609 b)))))) else (if i < 627 then (if i < 620 then (if i < 616 then (if i < 614 then decide (5 ≤ count609 b) else (if i < 615 then decide (6 ≤ count609 b) else decide (7 ≤ count609 b))) else (if i < 618 then (if i < 617 then decide (8 ≤ count609 b) else decide (1 ≤ count617 b)) else (if i < 619 then decide (2 ≤ count617 b) else decide (3 ≤ count617 b)))) else (if i < 623 then (if i < 621 then decide (4 ≤ count617 b) else (if i < 622 then decide (5 ≤ count617 b) else decide (6 ≤ count617 b))) else (if i < 625 then (if i < 624 then decide (7 ≤ count617 b) else decide (8 ≤ count617 b)) else (if i < 626 then decide (9 ≤ count617 b) else decide (10 ≤ count617 b))))) else (if i < 634 then (if i < 630 then (if i < 628 then decide (11 ≤ count617 b) else (if i < 629 then decide (12 ≤ count617 b) else decide (13 ≤ count617 b))) else (if i < 632 then (if i < 631 then decide (14 ≤ count617 b) else decide (15 ≤ count617 b)) else (if i < 633 then decide (16 ≤ count617 b) else decide (1 ≤ count633 b)))) else (if i < 638 then (if i < 636 then (if i < 635 then decide (2 ≤ count633 b) else decide (3 ≤ count633 b)) else (if i < 637 then decide (4 ≤ count633 b) else decide (5 ≤ count633 b))) else (if i < 640 then (if i < 639 then decide (6 ≤ count633 b) else decide (7 ≤ count633 b)) else (if i < 641 then decide (8 ≤ count633 b) else decide (9 ≤ count633 b))))))) else (if i < 671 then (if i < 656 then (if i < 649 then (if i < 645 then (if i < 643 then decide (10 ≤ count633 b) else (if i < 644 then decide (11 ≤ count633 b) else decide (12 ≤ count633 b))) else (if i < 647 then (if i < 646 then decide (13 ≤ count633 b) else decide (14 ≤ count633 b)) else (if i < 648 then decide (15 ≤ count633 b) else decide (16 ≤ count633 b)))) else (if i < 652 then (if i < 650 then decide (17 ≤ count633 b) else (if i < 651 then decide (18 ≤ count633 b) else decide (19 ≤ count633 b))) else (if i < 654 then (if i < 653 then decide (20 ≤ count633 b) else decide (21 ≤ count633 b)) else (if i < 655 then decide (22 ≤ count633 b) else decide (23 ≤ count633 b))))) else (if i < 663 then (if i < 659 then (if i < 657 then decide (24 ≤ count633 b) else (if i < 658 then decide (25 ≤ count633 b) else decide (26 ≤ count633 b))) else (if i < 661 then (if i < 660 then decide (27 ≤ count633 b) else decide (28 ≤ count633 b)) else (if i < 662 then decide (29 ≤ count633 b) else decide (30 ≤ count633 b)))) else (if i < 667 then (if i < 665 then (if i < 664 then decide (31 ≤ count633 b) else decide (32 ≤ count633 b)) else (if i < 666 then decide (1 ≤ count665 b) else decide (2 ≤ count665 b))) else (if i < 669 then (if i < 668 then decide (1 ≤ count667 b) else decide (2 ≤ count667 b)) else (if i < 670 then decide (1 ≤ count669 b) else decide (2 ≤ count669 b)))))) else (if i < 686 then (if i < 678 then (if i < 674 then (if i < 672 then decide (3 ≤ count669 b) else (if i < 673 then decide (4 ≤ count669 b) else decide (1 ≤ count673 b))) else (if i < 676 then (if i < 675 then decide (2 ≤ count673 b) else decide (1 ≤ count675 b)) else (if i < 677 then decide (2 ≤ count675 b) else decide (1 ≤ count677 b)))) else (if i < 682 then (if i < 680 then (if i < 679 then decide (2 ≤ count677 b) else decide (3 ≤ count677 b)) else (if i < 681 then decide (4 ≤ count677 b) else decide (1 ≤ count681 b))) else (if i < 684 then (if i < 683 then decide (2 ≤ count681 b) else decide (3 ≤ count681 b)) else (if i < 685 then decide (4 ≤ count681 b) else decide (5 ≤ count681 b))))) else (if i < 693 then (if i < 689 then (if i < 687 then decide (6 ≤ count681 b) else (if i < 688 then decide (7 ≤ count681 b) else decide (8 ≤ count681 b))) else (if i < 691 then (if i < 690 then decide (1 ≤ count689 b) else decide (2 ≤ count689 b)) else (if i < 692 then decide (1 ≤ count691 b) else decide (2 ≤ count691 b)))) else (if i < 697 then (if i < 695 then (if i < 694 then decide (1 ≤ count693 b) else decide (2 ≤ count693 b)) else (if i < 696 then decide (3 ≤ count693 b) else decide (4 ≤ count693 b))) else (if i < 699 then (if i < 698 then decide (1 ≤ count697 b) else decide (2 ≤ count697 b)) else (if i < 700 then decide (1 ≤ count699 b) else decide (2 ≤ count699 b))))))))) else (if i < 818 then (if i < 759 then (if i < 730 then (if i < 715 then (if i < 708 then (if i < 704 then (if i < 702 then decide (1 ≤ count701 b) else (if i < 703 then decide (2 ≤ count701 b) else decide (3 ≤ count701 b))) else (if i < 706 then (if i < 705 then decide (4 ≤ count701 b) else decide (1 ≤ count705 b)) else (if i < 707 then decide (2 ≤ count705 b) else decide (3 ≤ count705 b)))) else (if i < 711 then (if i < 709 then decide (4 ≤ count705 b) else (if i < 710 then decide (5 ≤ count705 b) else decide (6 ≤ count705 b))) else (if i < 713 then (if i < 712 then decide (7 ≤ count705 b) else decide (8 ≤ count705 b)) else (if i < 714 then decide (1 ≤ count713 b) else decide (2 ≤ count713 b))))) else (if i < 722 then (if i < 718 then (if i < 716 then decide (3 ≤ count713 b) else (if i < 717 then decide (4 ≤ count713 b) else decide (5 ≤ count713 b))) else (if i < 720 then (if i < 719 then decide (6 ≤ count713 b) else decide (7 ≤ count713 b)) else (if i < 721 then decide (8 ≤ count713 b) else decide (9 ≤ count713 b)))) else (if i < 726 then (if i < 724 then (if i < 723 then decide (10 ≤ count713 b) else decide (11 ≤ count713 b)) else (if i < 725 then decide (12 ≤ count713 b) else decide (13 ≤ count713 b))) else (if i < 728 then (if i < 727 then decide (14 ≤ count713 b) else decide (15 ≤ count713 b)) else (if i < 729 then decide (16 ≤ count713 b) else decide (1 ≤ count729 b)))))) else (if i < 744 then (if i < 737 then (if i < 733 then (if i < 731 then decide (2 ≤ count729 b) else (if i < 732 then decide (1 ≤ count731 b) else decide (2 ≤ count731 b))) else (if i < 735 then (if i < 734 then decide (1 ≤ count733 b) else decide (2 ≤ count733 b)) else (if i < 736 then decide (3 ≤ count733 b) else decide (4 ≤ count733 b)))) else (if i < 740 then (if i < 738 then decide (1 ≤ count737 b) else (if i < 739 then decide (2 ≤ count737 b) else decide (1 ≤ count739 b))) else (if i < 742 then (if i < 741 then decide (2 ≤ count739 b) else decide (1 ≤ count741 b)) else (if i < 743 then decide (2 ≤ count741 b) else decide (3 ≤ count741 b))))) else (if i < 751 then (if i < 747 then (if i < 745 then decide (4 ≤ count741 b) else (if i < 746 then decide (1 ≤ count745 b) else decide (2 ≤ count745 b))) else (if i < 749 then (if i < 748 then decide (3 ≤ count745 b) else decide (4 ≤ count745 b)) else (if i < 750 then decide (5 ≤ count745 b) else decide (6 ≤ count745 b)))) else (if i < 755 then (if i < 753 then (if i < 752 then decide (7 ≤ count745 b) else decide (8 ≤ count745 b)) else (if i < 754 then decide (1 ≤ count753 b) else decide (2 ≤ count753 b))) else (if i < 757 then (if i < 756 then decide (1 ≤ count755 b) else decide (2 ≤ count755 b)) else (if i < 758 then decide (1 ≤ count757 b) else decide (2 ≤ count757 b))))))) else (if i < 788 then (if i < 773 then (if i < 766 then (if i < 762 then (if i < 760 then decide (3 ≤ count757 b) else (if i < 761 then decide (4 ≤ count757 b) else decide (1 ≤ count761 b))) else (if i < 764 then (if i < 763 then decide (2 ≤ count761 b) else decide (1 ≤ count763 b)) else (if i < 765 then decide (2 ≤ count763 b) else decide (1 ≤ count765 b)))) else (if i < 769 then (if i < 767 then decide (2 ≤ count765 b) else (if i < 768 then decide (3 ≤ count765 b) else decide (4 ≤ count765 b))) else (if i < 771 then (if i < 770 then decide (1 ≤ count769 b) else decide (2 ≤ count769 b)) else (if i < 772 then decide (3 ≤ count769 b) else decide (4 ≤ count769 b))))) else (if i < 780 then (if i < 776 then (if i < 774 then decide (5 ≤ count769 b) else (if i < 775 then decide (6 ≤ count769 b) else decide (7 ≤ count769 b))) else (if i < 778 then (if i < 777 then decide (8 ≤ count769 b) else decide (1 ≤ count777 b)) else (if i < 779 then decide (2 ≤ count777 b) else decide (3 ≤ count777 b)))) else (if i < 784 then (if i < 782 then (if i < 781 then decide (4 ≤ count777 b) else decide (5 ≤ count777 b)) else (if i < 783 then decide (6 ≤ count777 b) else decide (7 ≤ count777 b))) else (if i < 786 then (if i < 785 then decide (8 ≤ count777 b) else decide (9 ≤ count777 b)) else (if i < 787 then decide (10 ≤ count777 b) else decide (11 ≤ count777 b)))))) else (if i < 803 then (if i < 795 then (if i < 791 then (if i < 789 then decide (12 ≤ count777 b) else (if i < 790 then decide (13 ≤ count777 b) else decide (14 ≤ count777 b))) else (if i < 793 then (if i < 792 then decide (15 ≤ count777 b) else decide (16 ≤ count777 b)) else (if i < 794 then decide (1 ≤ count793 b) else decide (2 ≤ count793 b)))) else (if i < 799 then (if i < 797 then (if i < 796 then decide (3 ≤ count793 b) else decide (4 ≤ count793 b)) else (if i < 798 then decide (5 ≤ count793 b) else decide (6 ≤ count793 b))) else (if i < 801 then (if i < 800 then decide (7 ≤ count793 b) else decide (8 ≤ count793 b)) else (if i < 802 then decide (9 ≤ count793 b) else decide (10 ≤ count793 b))))) else (if i < 810 then (if i < 806 then (if i < 804 then decide (11 ≤ count793 b) else (if i < 805 then decide (12 ≤ count793 b) else decide (13 ≤ count793 b))) else (if i < 808 then (if i < 807 then decide (14 ≤ count793 b) else decide (15 ≤ count793 b)) else (if i < 809 then decide (16 ≤ count793 b) else decide (17 ≤ count793 b)))) else (if i < 814 then (if i < 812 then (if i < 811 then decide (18 ≤ count793 b) else decide (19 ≤ count793 b)) else (if i < 813 then decide (20 ≤ count793 b) else decide (21 ≤ count793 b))) else (if i < 816 then (if i < 815 then decide (22 ≤ count793 b) else decide (23 ≤ count793 b)) else (if i < 817 then decide (24 ≤ count793 b) else decide (25 ≤ count793 b)))))))) else (if i < 876 then (if i < 847 then (if i < 832 then (if i < 825 then (if i < 821 then (if i < 819 then decide (26 ≤ count793 b) else (if i < 820 then decide (27 ≤ count793 b) else decide (28 ≤ count793 b))) else (if i < 823 then (if i < 822 then decide (29 ≤ count793 b) else decide (30 ≤ count793 b)) else (if i < 824 then decide (31 ≤ count793 b) else decide (32 ≤ count793 b)))) else (if i < 828 then (if i < 826 then decide (1 ≤ count825 b) else (if i < 827 then decide (2 ≤ count825 b) else decide (3 ≤ count825 b))) else (if i < 830 then (if i < 829 then decide (4 ≤ count825 b) else decide (5 ≤ count825 b)) else (if i < 831 then decide (6 ≤ count825 b) else decide (7 ≤ count825 b))))) else (if i < 839 then (if i < 835 then (if i < 833 then decide (8 ≤ count825 b) else (if i < 834 then decide (9 ≤ count825 b) else decide (10 ≤ count825 b))) else (if i < 837 then (if i < 836 then decide (11 ≤ count825 b) else decide (12 ≤ count825 b)) else (if i < 838 then decide (13 ≤ count825 b) else decide (14 ≤ count825 b)))) else (if i < 843 then (if i < 841 then (if i < 840 then decide (15 ≤ count825 b) else decide (16 ≤ count825 b)) else (if i < 842 then decide (17 ≤ count825 b) else decide (18 ≤ count825 b))) else (if i < 845 then (if i < 844 then decide (19 ≤ count825 b) else decide (20 ≤ count825 b)) else (if i < 846 then decide (21 ≤ count825 b) else decide (22 ≤ count825 b)))))) else (if i < 861 then (if i < 854 then (if i < 850 then (if i < 848 then decide (23 ≤ count825 b) else (if i < 849 then decide (24 ≤ count825 b) else decide (25 ≤ count825 b))) else (if i < 852 then (if i < 851 then decide (26 ≤ count825 b) else decide (27 ≤ count825 b)) else (if i < 853 then decide (28 ≤ count825 b) else decide (29 ≤ count825 b)))) else (if i < 857 then (if i < 855 then decide (30 ≤ count825 b) else (if i < 856 then decide (31 ≤ count825 b) else decide (32 ≤ count825 b))) else (if i < 859 then (if i < 858 then decide (33 ≤ count825 b) else decide (34 ≤ count825 b)) else (if i < 860 then decide (35 ≤ count825 b) else decide (36 ≤ count825 b))))) else (if i < 868 then (if i < 864 then (if i < 862 then decide (37 ≤ count825 b) else (if i < 863 then decide (38 ≤ count825 b) else decide (39 ≤ count825 b))) else (if i < 866 then (if i < 865 then decide (40 ≤ count825 b) else decide (41 ≤ count825 b)) else (if i < 867 then decide (42 ≤ count825 b) else decide (1 ≤ count867 b)))) else (if i < 872 then (if i < 870 then (if i < 869 then decide (2 ≤ count867 b) else decide (1 ≤ count869 b)) else (if i < 871 then decide (2 ≤ count869 b) else decide (1 ≤ count871 b))) else (if i < 874 then (if i < 873 then decide (2 ≤ count871 b) else decide (3 ≤ count871 b)) else (if i < 875 then decide (4 ≤ count871 b) else decide (1 ≤ count875 b))))))) else (if i < 905 then (if i < 890 then (if i < 883 then (if i < 879 then (if i < 877 then decide (2 ≤ count875 b) else (if i < 878 then decide (1 ≤ count877 b) else decide (2 ≤ count877 b))) else (if i < 881 then (if i < 880 then decide (1 ≤ count879 b) else decide (2 ≤ count879 b)) else (if i < 882 then decide (3 ≤ count879 b) else decide (4 ≤ count879 b)))) else (if i < 886 then (if i < 884 then decide (1 ≤ count883 b) else (if i < 885 then decide (2 ≤ count883 b) else decide (3 ≤ count883 b))) else (if i < 888 then (if i < 887 then decide (4 ≤ count883 b) else decide (5 ≤ count883 b)) else (if i < 889 then decide (6 ≤ count883 b) else decide (7 ≤ count883 b))))) else (if i < 897 then (if i < 893 then (if i < 891 then decide (8 ≤ count883 b) else (if i < 892 then decide (1 ≤ count891 b) else decide (2 ≤ count891 b))) else (if i < 895 then (if i < 894 then decide (1 ≤ count893 b) else decide (2 ≤ count893 b)) else (if i < 896 then decide (1 ≤ count895 b) else decide (2 ≤ count895 b)))) else (if i < 901 then (if i < 899 then (if i < 898 then decide (3 ≤ count895 b) else decide (4 ≤ count895 b)) else (if i < 900 then decide (1 ≤ count899 b) else decide (2 ≤ count899 b))) else (if i < 903 then (if i < 902 then decide (1 ≤ count901 b) else decide (2 ≤ count901 b)) else (if i < 904 then decide (1 ≤ count903 b) else decide (2 ≤ count903 b)))))) else (if i < 920 then (if i < 912 then (if i < 908 then (if i < 906 then decide (3 ≤ count903 b) else (if i < 907 then decide (4 ≤ count903 b) else decide (1 ≤ count907 b))) else (if i < 910 then (if i < 909 then decide (2 ≤ count907 b) else decide (3 ≤ count907 b)) else (if i < 911 then decide (4 ≤ count907 b) else decide (5 ≤ count907 b)))) else (if i < 916 then (if i < 914 then (if i < 913 then decide (6 ≤ count907 b) else decide (7 ≤ count907 b)) else (if i < 915 then decide (8 ≤ count907 b) else decide (1 ≤ count915 b))) else (if i < 918 then (if i < 917 then decide (2 ≤ count915 b) else decide (3 ≤ count915 b)) else (if i < 919 then decide (4 ≤ count915 b) else decide (5 ≤ count915 b))))) else (if i < 927 then (if i < 923 then (if i < 921 then decide (6 ≤ count915 b) else (if i < 922 then decide (7 ≤ count915 b) else decide (8 ≤ count915 b))) else (if i < 925 then (if i < 924 then decide (9 ≤ count915 b) else decide (10 ≤ count915 b)) else (if i < 926 then decide (11 ≤ count915 b) else decide (12 ≤ count915 b)))) else (if i < 931 then (if i < 929 then (if i < 928 then decide (13 ≤ count915 b) else decide (14 ≤ count915 b)) else (if i < 930 then decide (15 ≤ count915 b) else decide (16 ≤ count915 b))) else (if i < 933 then (if i < 932 then decide (1 ≤ count931 b) else decide (2 ≤ count931 b)) else (if i < 934 then decide (1 ≤ count933 b) else decide (2 ≤ count933 b))))))))))) else (if i < 1403 then (if i < 1169 then (if i < 1052 then (if i < 993 then (if i < 964 then (if i < 949 then (if i < 942 then (if i < 938 then (if i < 936 then decide (1 ≤ count935 b) else (if i < 937 then decide (2 ≤ count935 b) else decide (3 ≤ count935 b))) else (if i < 940 then (if i < 939 then decide (4 ≤ count935 b) else decide (1 ≤ count939 b)) else (if i < 941 then decide (2 ≤ count939 b) else decide (1 ≤ count941 b)))) else (if i < 945 then (if i < 943 then decide (2 ≤ count941 b) else (if i < 944 then decide (1 ≤ count943 b) else decide (2 ≤ count943 b))) else (if i < 947 then (if i < 946 then decide (3 ≤ count943 b) else decide (4 ≤ count943 b)) else (if i < 948 then decide (1 ≤ count947 b) else decide (2 ≤ count947 b))))) else (if i < 956 then (if i < 952 then (if i < 950 then decide (3 ≤ count947 b) else (if i < 951 then decide (4 ≤ count947 b) else decide (5 ≤ count947 b))) else (if i < 954 then (if i < 953 then decide (6 ≤ count947 b) else decide (7 ≤ count947 b)) else (if i < 955 then decide (8 ≤ count947 b) else decide (1 ≤ count955 b)))) else (if i < 960 then (if i < 958 then (if i < 957 then decide (2 ≤ count955 b) else decide (1 ≤ count957 b)) else (if i < 959 then decide (2 ≤ count957 b) else decide (1 ≤ count959 b))) else (if i < 962 then (if i < 961 then decide (2 ≤ count959 b) else decide (3 ≤ count959 b)) else (if i < 963 then decide (4 ≤ count959 b) else decide (1 ≤ count963 b)))))) else (if i < 978 then (if i < 971 then (if i < 967 then (if i < 965 then decide (2 ≤ count963 b) else (if i < 966 then decide (1 ≤ count965 b) else decide (2 ≤ count965 b))) else (if i < 969 then (if i < 968 then decide (1 ≤ count967 b) else decide (2 ≤ count967 b)) else (if i < 970 then decide (3 ≤ count967 b) else decide (4 ≤ count967 b)))) else (if i < 974 then (if i < 972 then decide (1 ≤ count971 b) else (if i < 973 then decide (2 ≤ count971 b) else decide (3 ≤ count971 b))) else (if i < 976 then (if i < 975 then decide (4 ≤ count971 b) else decide (5 ≤ count971 b)) else (if i < 977 then decide (6 ≤ count971 b) else decide (7 ≤ count971 b))))) else (if i < 985 then (if i < 981 then (if i < 979 then decide (8 ≤ count971 b) else (if i < 980 then decide (1 ≤ count979 b) else decide (2 ≤ count979 b))) else (if i < 983 then (if i < 982 then decide (3 ≤ count979 b) else decide (4 ≤ count979 b)) else (if i < 984 then decide (5 ≤ count979 b) else decide (6 ≤ count979 b)))) else (if i < 989 then (if i < 987 then (if i < 986 then decide (7 ≤ count979 b) else decide (8 ≤ count979 b)) else (if i < 988 then decide (9 ≤ count979 b) else decide (10 ≤ count979 b))) else (if i < 991 then (if i < 990 then decide (11 ≤ count979 b) else decide (12 ≤ count979 b)) else (if i < 992 then decide (13 ≤ count979 b) else decide (14 ≤ count979 b))))))) else (if i < 1022 then (if i < 1007 then (if i < 1000 then (if i < 996 then (if i < 994 then decide (15 ≤ count979 b) else (if i < 995 then decide (16 ≤ count979 b) else decide (1 ≤ count995 b))) else (if i < 998 then (if i < 997 then decide (2 ≤ count995 b) else decide (3 ≤ count995 b)) else (if i < 999 then decide (4 ≤ count995 b) else decide (5 ≤ count995 b)))) else (if i < 1003 then (if i < 1001 then decide (6 ≤ count995 b) else (if i < 1002 then decide (7 ≤ count995 b) else decide (8 ≤ count995 b))) else (if i < 1005 then (if i < 1004 then decide (9 ≤ count995 b) else decide (10 ≤ count995 b)) else (if i < 1006 then decide (11 ≤ count995 b) else decide (12 ≤ count995 b))))) else (if i < 1014 then (if i < 1010 then (if i < 1008 then decide (13 ≤ count995 b) else (if i < 1009 then decide (14 ≤ count995 b) else decide (15 ≤ count995 b))) else (if i < 1012 then (if i < 1011 then decide (16 ≤ count995 b) else decide (17 ≤ count995 b)) else (if i < 1013 then decide (18 ≤ count995 b) else decide (19 ≤ count995 b)))) else (if i < 1018 then (if i < 1016 then (if i < 1015 then decide (20 ≤ count995 b) else decide (21 ≤ count995 b)) else (if i < 1017 then decide (22 ≤ count995 b) else decide (23 ≤ count995 b))) else (if i < 1020 then (if i < 1019 then decide (24 ≤ count995 b) else decide (1 ≤ count1019 b)) else (if i < 1021 then decide (2 ≤ count1019 b) else decide (1 ≤ count1021 b)))))) else (if i < 1037 then (if i < 1029 then (if i < 1025 then (if i < 1023 then decide (2 ≤ count1021 b) else (if i < 1024 then decide (1 ≤ count1023 b) else decide (2 ≤ count1023 b))) else (if i < 1027 then (if i < 1026 then decide (3 ≤ count1023 b) else decide (4 ≤ count1023 b)) else (if i < 1028 then decide (1 ≤ count1027 b) else decide (2 ≤ count1027 b)))) else (if i < 1033 then (if i < 1031 then (if i < 1030 then decide (1 ≤ count1029 b) else decide (2 ≤ count1029 b)) else (if i < 1032 then decide (1 ≤ count1031 b) else decide (2 ≤ count1031 b))) else (if i < 1035 then (if i < 1034 then decide (3 ≤ count1031 b) else decide (4 ≤ count1031 b)) else (if i < 1036 then decide (1 ≤ count1035 b) else decide (2 ≤ count1035 b))))) else (if i < 1044 then (if i < 1040 then (if i < 1038 then decide (3 ≤ count1035 b) else (if i < 1039 then decide (4 ≤ count1035 b) else decide (5 ≤ count1035 b))) else (if i < 1042 then (if i < 1041 then decide (6 ≤ count1035 b) else decide (7 ≤ count1035 b)) else (if i < 1043 then decide (8 ≤ count1035 b) else decide (1 ≤ count1043 b)))) else (if i < 1048 then (if i < 1046 then (if i < 1045 then decide (2 ≤ count1043 b) else decide (1 ≤ count1045 b)) else (if i < 1047 then decide (2 ≤ count1045 b) else decide (1 ≤ count1047 b))) else (if i < 1050 then (if i < 1049 then decide (2 ≤ count1047 b) else decide (3 ≤ count1047 b)) else (if i < 1051 then decide (4 ≤ count1047 b) else decide (1 ≤ count1051 b)))))))) else (if i < 1110 then (if i < 1081 then (if i < 1066 then (if i < 1059 then (if i < 1055 then (if i < 1053 then decide (2 ≤ count1051 b) else (if i < 1054 then decide (1 ≤ count1053 b) else decide (2 ≤ count1053 b))) else (if i < 1057 then (if i < 1056 then decide (1 ≤ count1055 b) else decide (2 ≤ count1055 b)) else (if i < 1058 then decide (3 ≤ count1055 b) else decide (4 ≤ count1055 b)))) else (if i < 1062 then (if i < 1060 then decide (1 ≤ count1059 b) else (if i < 1061 then decide (2 ≤ count1059 b) else decide (3 ≤ count1059 b))) else (if i < 1064 then (if i < 1063 then decide (4 ≤ count1059 b) else decide (5 ≤ count1059 b)) else (if i < 1065 then decide (6 ≤ count1059 b) else decide (7 ≤ count1059 b))))) else (if i < 1073 then (if i < 1069 then (if i < 1067 then decide (8 ≤ count1059 b) else (if i < 1068 then decide (1 ≤ count1067 b) else decide (2 ≤ count1067 b))) else (if i < 1071 then (if i < 1070 then decide (3 ≤ count1067 b) else decide (4 ≤ count1067 b)) else (if i < 1072 then decide (5 ≤ count1067 b) else decide (6 ≤ count1067 b)))) else (if i < 1077 then (if i < 1075 then (if i < 1074 then decide (7 ≤ count1067 b) else decide (8 ≤ count1067 b)) else (if i < 1076 then decide (9 ≤ count1067 b) else decide (10 ≤ count1067 b))) else (if i < 1079 then (if i < 1078 then decide (11 ≤ count1067 b) else decide (12 ≤ count1067 b)) else (if i < 1080 then decide (13 ≤ count1067 b) else decide (14 ≤ count1067 b)))))) else (if i < 1095 then (if i < 1088 then (if i < 1084 then (if i < 1082 then decide (15 ≤ count1067 b) else (if i < 1083 then decide (16 ≤ count1067 b) else decide (1 ≤ count1083 b))) else (if i < 1086 then (if i < 1085 then decide (2 ≤ count1083 b) else decide (1 ≤ count1085 b)) else (if i < 1087 then decide (2 ≤ count1085 b) else decide (1 ≤ count1087 b)))) else (if i < 1091 then (if i < 1089 then decide (2 ≤ count1087 b) else (if i < 1090 then decide (3 ≤ count1087 b) else decide (4 ≤ count1087 b))) else (if i < 1093 then (if i < 1092 then decide (1 ≤ count1091 b) else decide (2 ≤ count1091 b)) else (if i < 1094 then decide (1 ≤ count1093 b) else decide (2 ≤ count1093 b))))) else (if i < 1102 then (if i < 1098 then (if i < 1096 then decide (1 ≤ count1095 b) else (if i < 1097 then decide (2 ≤ count1095 b) else decide (3 ≤ count1095 b))) else (if i < 1100 then (if i < 1099 then decide (4 ≤ count1095 b) else decide (1 ≤ count1099 b)) else (if i < 1101 then decide (2 ≤ count1099 b) else decide (3 ≤ count1099 b)))) else (if i < 1106 then (if i < 1104 then (if i < 1103 then decide (4 ≤ count1099 b) else decide (5 ≤ count1099 b)) else (if i < 1105 then decide (6 ≤ count1099 b) else decide (7 ≤ count1099 b))) else (if i < 1108 then (if i < 1107 then decide (8 ≤ count1099 b) else decide (1 ≤ count1107 b)) else (if i < 1109 then decide (2 ≤ count1107 b) else decide (1 ≤ count1109 b))))))) else (if i < 1139 then (if i < 1124 then (if i < 1117 then (if i < 1113 then (if i < 1111 then decide (2 ≤ count1109 b) else (if i < 1112 then decide (1 ≤ count1111 b) else decide (2 ≤ count1111 b))) else (if i < 1115 then (if i < 1114 then decide (3 ≤ count1111 b) else decide (4 ≤ count1111 b)) else (if i < 1116 then decide (1 ≤ count1115 b) else decide (2 ≤ count1115 b)))) else (if i < 1120 then (if i < 1118 then decide (1 ≤ count1117 b) else (if i < 1119 then decide (2 ≤ count1117 b) else decide (1 ≤ count1119 b))) else (if i < 1122 then (if i < 1121 then decide (2 ≤ count1119 b) else decide (3 ≤ count1119 b)) else (if i < 1123 then decide (4 ≤ count1119 b) else decide (1 ≤ count1123 b))))) else (if i < 1131 then (if i < 1127 then (if i < 1125 then decide (2 ≤ count1123 b) else (if i < 1126 then decide (3 ≤ count1123 b) else decide (4 ≤ count1123 b))) else (if i < 1129 then (if i < 1128 then decide (5 ≤ count1123 b) else decide (6 ≤ count1123 b)) else (if i < 1130 then decide (7 ≤ count1123 b) else decide (8 ≤ count1123 b)))) else (if i < 1135 then (if i < 1133 then (if i < 1132 then decide (1 ≤ count1131 b) else decide (2 ≤ count1131 b)) else (if i < 1134 then decide (3 ≤ count1131 b) else decide (4 ≤ count1131 b))) else (if i < 1137 then (if i < 1136 then decide (5 ≤ count1131 b) else decide (6 ≤ count1131 b)) else (if i < 1138 then decide (7 ≤ count1131 b) else decide (8 ≤ count1131 b)))))) else (if i < 1154 then (if i < 1146 then (if i < 1142 then (if i < 1140 then decide (9 ≤ count1131 b) else (if i < 1141 then decide (10 ≤ count1131 b) else decide (11 ≤ count1131 b))) else (if i < 1144 then (if i < 1143 then decide (12 ≤ count1131 b) else decide (13 ≤ count1131 b)) else (if i < 1145 then decide (14 ≤ count1131 b) else decide (15 ≤ count1131 b)))) else (if i < 1150 then (if i < 1148 then (if i < 1147 then decide (16 ≤ count1131 b) else decide (1 ≤ count1147 b)) else (if i < 1149 then decide (2 ≤ count1147 b) else decide (3 ≤ count1147 b))) else (if i < 1152 then (if i < 1151 then decide (4 ≤ count1147 b) else decide (5 ≤ count1147 b)) else (if i < 1153 then decide (6 ≤ count1147 b) else decide (7 ≤ count1147 b))))) else (if i < 1161 then (if i < 1157 then (if i < 1155 then decide (8 ≤ count1147 b) else (if i < 1156 then decide (9 ≤ count1147 b) else decide (10 ≤ count1147 b))) else (if i < 1159 then (if i < 1158 then decide (11 ≤ count1147 b) else decide (12 ≤ count1147 b)) else (if i < 1160 then decide (13 ≤ count1147 b) else decide (14 ≤ count1147 b)))) else (if i < 1165 then (if i < 1163 then (if i < 1162 then decide (15 ≤ count1147 b) else decide (16 ≤ count1147 b)) else (if i < 1164 then decide (17 ≤ count1147 b) else decide (18 ≤ count1147 b))) else (if i < 1167 then (if i < 1166 then decide (19 ≤ count1147 b) else decide (20 ≤ count1147 b)) else (if i < 1168 then decide (21 ≤ count1147 b) else decide (22 ≤ count1147 b))))))))) else (if i < 1286 then (if i < 1227 then (if i < 1198 then (if i < 1183 then (if i < 1176 then (if i < 1172 then (if i < 1170 then decide (23 ≤ count1147 b) else (if i < 1171 then decide (24 ≤ count1147 b) else decide (1 ≤ count1171 b))) else (if i < 1174 then (if i < 1173 then decide (2 ≤ count1171 b) else decide (3 ≤ count1171 b)) else (if i < 1175 then decide (4 ≤ count1171 b) else decide (5 ≤ count1171 b)))) else (if i < 1179 then (if i < 1177 then decide (6 ≤ count1171 b) else (if i < 1178 then decide (7 ≤ count1171 b) else decide (8 ≤ count1171 b))) else (if i < 1181 then (if i < 1180 then decide (9 ≤ count1171 b) else decide (10 ≤ count1171 b)) else (if i < 1182 then decide (11 ≤ count1171 b) else decide (12 ≤ count1171 b))))) else (if i < 1190 then (if i < 1186 then (if i < 1184 then decide (13 ≤ count1171 b) else (if i < 1185 then decide (14 ≤ count1171 b) else decide (15 ≤ count1171 b))) else (if i < 1188 then (if i < 1187 then decide (16 ≤ count1171 b) else decide (17 ≤ count1171 b)) else (if i < 1189 then decide (18 ≤ count1171 b) else decide (19 ≤ count1171 b)))) else (if i < 1194 then (if i < 1192 then (if i < 1191 then decide (20 ≤ count1171 b) else decide (21 ≤ count1171 b)) else (if i < 1193 then decide (22 ≤ count1171 b) else decide (23 ≤ count1171 b))) else (if i < 1196 then (if i < 1195 then decide (24 ≤ count1171 b) else decide (1 ≤ count1195 b)) else (if i < 1197 then decide (2 ≤ count1195 b) else decide (1 ≤ count1197 b)))))) else (if i < 1212 then (if i < 1205 then (if i < 1201 then (if i < 1199 then decide (2 ≤ count1197 b) else (if i < 1200 then decide (3 ≤ count1197 b) else decide (1 ≤ count1200 b))) else (if i < 1203 then (if i < 1202 then decide (2 ≤ count1200 b) else decide (1 ≤ count1202 b)) else (if i < 1204 then decide (2 ≤ count1202 b) else decide (1 ≤ count1204 b)))) else (if i < 1208 then (if i < 1206 then decide (2 ≤ count1204 b) else (if i < 1207 then decide (3 ≤ count1204 b) else decide (4 ≤ count1204 b))) else (if i < 1210 then (if i < 1209 then decide (1 ≤ count1208 b) else decide (2 ≤ count1208 b)) else (if i < 1211 then decide (3 ≤ count1208 b) else decide (4 ≤ count1208 b))))) else (if i < 1219 then (if i < 1215 then (if i < 1213 then decide (5 ≤ count1208 b) else (if i < 1214 then decide (6 ≤ count1208 b) else decide (7 ≤ count1208 b))) else (if i < 1217 then (if i < 1216 then decide (1 ≤ count1215 b) else decide (2 ≤ count1215 b)) else (if i < 1218 then decide (1 ≤ count1217 b) else decide (2 ≤ count1217 b)))) else (if i < 1223 then (if i < 1221 then (if i < 1220 then decide (1 ≤ count1219 b) else decide (2 ≤ count1219 b)) else (if i < 1222 then decide (3 ≤ count1219 b) else decide (4 ≤ count1219 b))) else (if i < 1225 then (if i < 1224 then decide (1 ≤ count1223 b) else decide (2 ≤ count1223 b)) else (if i < 1226 then decide (1 ≤ count1225 b) else decide (2 ≤ count1225 b))))))) else (if i < 1256 then (if i < 1241 then (if i < 1234 then (if i < 1230 then (if i < 1228 then decide (1 ≤ count1227 b) else (if i < 1229 then decide (2 ≤ count1227 b) else decide (3 ≤ count1227 b))) else (if i < 1232 then (if i < 1231 then decide (4 ≤ count1227 b) else decide (1 ≤ count1231 b)) else (if i < 1233 then decide (2 ≤ count1231 b) else decide (3 ≤ count1231 b)))) else (if i < 1237 then (if i < 1235 then decide (4 ≤ count1231 b) else (if i < 1236 then decide (5 ≤ count1231 b) else decide (6 ≤ count1231 b))) else (if i < 1239 then (if i < 1238 then decide (7 ≤ count1231 b) else decide (8 ≤ count1231 b)) else (if i < 1240 then decide (1 ≤ count1239 b) else decide (2 ≤ count1239 b))))) else (if i < 1248 then (if i < 1244 then (if i < 1242 then decide (3 ≤ count1239 b) else (if i < 1243 then decide (4 ≤ count1239 b) else decide (5 ≤ count1239 b))) else (if i < 1246 then (if i < 1245 then decide (6 ≤ count1239 b) else decide (7 ≤ count1239 b)) else (if i < 1247 then decide (8 ≤ count1239 b) else decide (9 ≤ count1239 b)))) else (if i < 1252 then (if i < 1250 then (if i < 1249 then decide (10 ≤ count1239 b) else decide (11 ≤ count1239 b)) else (if i < 1251 then decide (12 ≤ count1239 b) else decide (13 ≤ count1239 b))) else (if i < 1254 then (if i < 1253 then decide (14 ≤ count1239 b) else decide (15 ≤ count1239 b)) else (if i < 1255 then decide (1 ≤ count1254 b) else decide (2 ≤ count1254 b)))))) else (if i < 1271 then (if i < 1263 then (if i < 1259 then (if i < 1257 then decide (1 ≤ count1256 b) else (if i < 1258 then decide (2 ≤ count1256 b) else decide (1 ≤ count1258 b))) else (if i < 1261 then (if i < 1260 then decide (2 ≤ count1258 b) else decide (3 ≤ count1258 b)) else (if i < 1262 then decide (4 ≤ count1258 b) else decide (1 ≤ count1262 b)))) else (if i < 1267 then (if i < 1265 then (if i < 1264 then decide (2 ≤ count1262 b) else decide (1 ≤ count1264 b)) else (if i < 1266 then decide (2 ≤ count1264 b) else decide (1 ≤ count1266 b))) else (if i < 1269 then (if i < 1268 then decide (2 ≤ count1266 b) else decide (3 ≤ count1266 b)) else (if i < 1270 then decide (4 ≤ count1266 b) else decide (1 ≤ count1270 b))))) else (if i < 1278 then (if i < 1274 then (if i < 1272 then decide (2 ≤ count1270 b) else (if i < 1273 then decide (3 ≤ count1270 b) else decide (4 ≤ count1270 b))) else (if i < 1276 then (if i < 1275 then decide (5 ≤ count1270 b) else decide (6 ≤ count1270 b)) else (if i < 1277 then decide (7 ≤ count1270 b) else decide (8 ≤ count1270 b)))) else (if i < 1282 then (if i < 1280 then (if i < 1279 then decide (1 ≤ count1278 b) else decide (2 ≤ count1278 b)) else (if i < 1281 then decide (1 ≤ count1280 b) else decide (2 ≤ count1280 b))) else (if i < 1284 then (if i < 1283 then decide (1 ≤ count1282 b) else decide (2 ≤ count1282 b)) else (if i < 1285 then decide (3 ≤ count1282 b) else decide (4 ≤ count1282 b)))))))) else (if i < 1344 then (if i < 1315 then (if i < 1300 then (if i < 1293 then (if i < 1289 then (if i < 1287 then decide (1 ≤ count1286 b) else (if i < 1288 then decide (2 ≤ count1286 b) else decide (1 ≤ count1288 b))) else (if i < 1291 then (if i < 1290 then decide (2 ≤ count1288 b) else decide (1 ≤ count1290 b)) else (if i < 1292 then decide (2 ≤ count1290 b) else decide (3 ≤ count1290 b)))) else (if i < 1296 then (if i < 1294 then decide (4 ≤ count1290 b) else (if i < 1295 then decide (1 ≤ count1294 b) else decide (2 ≤ count1294 b))) else (if i < 1298 then (if i < 1297 then decide (3 ≤ count1294 b) else decide (4 ≤ count1294 b)) else (if i < 1299 then decide (5 ≤ count1294 b) else decide (6 ≤ count1294 b))))) else (if i < 1307 then (if i < 1303 then (if i < 1301 then decide (7 ≤ count1294 b) else (if i < 1302 then decide (8 ≤ count1294 b) else decide (1 ≤ count1302 b))) else (if i < 1305 then (if i < 1304 then decide (2 ≤ count1302 b) else decide (3 ≤ count1302 b)) else (if i < 1306 then decide (4 ≤ count1302 b) else decide (5 ≤ count1302 b)))) else (if i < 1311 then (if i < 1309 then (if i < 1308 then decide (6 ≤ count1302 b) else decide (7 ≤ count1302 b)) else (if i < 1310 then decide (8 ≤ count1302 b) else decide (9 ≤ count1302 b))) else (if i < 1313 then (if i < 1312 then decide (10 ≤ count1302 b) else decide (11 ≤ count1302 b)) else (if i < 1314 then decide (12 ≤ count1302 b) else decide (13 ≤ count1302 b)))))) else (if i < 1329 then (if i < 1322 then (if i < 1318 then (if i < 1316 then decide (14 ≤ count1302 b) else (if i < 1317 then decide (15 ≤ count1302 b) else decide (16 ≤ count1302 b))) else (if i < 1320 then (if i < 1319 then decide (1 ≤ count1318 b) else decide (2 ≤ count1318 b)) else (if i < 1321 then decide (3 ≤ count1318 b) else decide (4 ≤ count1318 b)))) else (if i < 1325 then (if i < 1323 then decide (5 ≤ count1318 b) else (if i < 1324 then decide (6 ≤ count1318 b) else decide (7 ≤ count1318 b))) else (if i < 1327 then (if i < 1326 then decide (8 ≤ count1318 b) else decide (9 ≤ count1318 b)) else (if i < 1328 then decide (10 ≤ count1318 b) else decide (11 ≤ count1318 b))))) else (if i < 1336 then (if i < 1332 then (if i < 1330 then decide (12 ≤ count1318 b) else (if i < 1331 then decide (13 ≤ count1318 b) else decide (14 ≤ count1318 b))) else (if i < 1334 then (if i < 1333 then decide (15 ≤ count1318 b) else decide (16 ≤ count1318 b)) else (if i < 1335 then decide (17 ≤ count1318 b) else decide (18 ≤ count1318 b)))) else (if i < 1340 then (if i < 1338 then (if i < 1337 then decide (19 ≤ count1318 b) else decide (20 ≤ count1318 b)) else (if i < 1339 then decide (21 ≤ count1318 b) else decide (22 ≤ count1318 b))) else (if i < 1342 then (if i < 1341 then decide (23 ≤ count1318 b) else decide (24 ≤ count1318 b)) else (if i < 1343 then decide (25 ≤ count1318 b) else decide (26 ≤ count1318 b))))))) else (if i < 1373 then (if i < 1358 then (if i < 1351 then (if i < 1347 then (if i < 1345 then decide (27 ≤ count1318 b) else (if i < 1346 then decide (28 ≤ count1318 b) else decide (29 ≤ count1318 b))) else (if i < 1349 then (if i < 1348 then decide (30 ≤ count1318 b) else decide (31 ≤ count1318 b)) else (if i < 1350 then decide (1 ≤ count1349 b) else decide (2 ≤ count1349 b)))) else (if i < 1354 then (if i < 1352 then decide (1 ≤ count1351 b) else (if i < 1353 then decide (2 ≤ count1351 b) else decide (1 ≤ count1353 b))) else (if i < 1356 then (if i < 1355 then decide (2 ≤ count1353 b) else decide (3 ≤ count1353 b)) else (if i < 1357 then decide (4 ≤ count1353 b) else decide (1 ≤ count1357 b))))) else (if i < 1365 then (if i < 1361 then (if i < 1359 then decide (2 ≤ count1357 b) else (if i < 1360 then decide (1 ≤ count1359 b) else decide (2 ≤ count1359 b))) else (if i < 1363 then (if i < 1362 then decide (1 ≤ count1361 b) else decide (2 ≤ count1361 b)) else (if i < 1364 then decide (3 ≤ count1361 b) else decide (4 ≤ count1361 b)))) else (if i < 1369 then (if i < 1367 then (if i < 1366 then decide (1 ≤ count1365 b) else decide (2 ≤ count1365 b)) else (if i < 1368 then decide (3 ≤ count1365 b) else decide (4 ≤ count1365 b))) else (if i < 1371 then (if i < 1370 then decide (5 ≤ count1365 b) else decide (6 ≤ count1365 b)) else (if i < 1372 then decide (7 ≤ count1365 b) else decide (8 ≤ count1365 b)))))) else (if i < 1388 then (if i < 1380 then (if i < 1376 then (if i < 1374 then decide (1 ≤ count1373 b) else (if i < 1375 then decide (2 ≤ count1373 b) else decide (1 ≤ count1375 b))) else (if i < 1378 then (if i < 1377 then decide (2 ≤ count1375 b) else decide (1 ≤ count1377 b)) else (if i < 1379 then decide (2 ≤ count1377 b) else decide (3 ≤ count1377 b)))) else (if i < 1384 then (if i < 1382 then (if i < 1381 then decide (4 ≤ count1377 b) else decide (1 ≤ count1381 b)) else (if i < 1383 then decide (2 ≤ count1381 b) else decide (1 ≤ count1383 b))) else (if i < 1386 then (if i < 1385 then decide (2 ≤ count1383 b) else decide (1 ≤ count1385 b)) else (if i < 1387 then decide (2 ≤ count1385 b) else decide (3 ≤ count1385 b))))) else (if i < 1395 then (if i < 1391 then (if i < 1389 then decide (4 ≤ count1385 b) else (if i < 1390 then decide (1 ≤ count1389 b) else decide (2 ≤ count1389 b))) else (if i < 1393 then (if i < 1392 then decide (3 ≤ count1389 b) else decide (4 ≤ count1389 b)) else (if i < 1394 then decide (5 ≤ count1389 b) else decide (6 ≤ count1389 b)))) else (if i < 1399 then (if i < 1397 then (if i < 1396 then decide (7 ≤ count1389 b) else decide (8 ≤ count1389 b)) else (if i < 1398 then decide (1 ≤ count1397 b) else decide (2 ≤ count1397 b))) else (if i < 1401 then (if i < 1400 then decide (3 ≤ count1397 b) else decide (4 ≤ count1397 b)) else (if i < 1402 then decide (5 ≤ count1397 b) else decide (6 ≤ count1397 b)))))))))) else (if i < 1637 then (if i < 1520 then (if i < 1461 then (if i < 1432 then (if i < 1417 then (if i < 1410 then (if i < 1406 then (if i < 1404 then decide (7 ≤ count1397 b) else (if i < 1405 then decide (8 ≤ count1397 b) else decide (9 ≤ count1397 b))) else (if i < 1408 then (if i < 1407 then decide (10 ≤ count1397 b) else decide (11 ≤ count1397 b)) else (if i < 1409 then decide (12 ≤ count1397 b) else decide (13 ≤ count1397 b)))) else (if i < 1413 then (if i < 1411 then decide (14 ≤ count1397 b) else (if i < 1412 then decide (15 ≤ count1397 b) else decide (16 ≤ count1397 b))) else (if i < 1415 then (if i < 1414 then decide (1 ≤ count1413 b) else decide (2 ≤ count1413 b)) else (if i < 1416 then decide (1 ≤ count1415 b) else decide (2 ≤ count1415 b))))) else (if i < 1424 then (if i < 1420 then (if i < 1418 then decide (1 ≤ count1417 b) else (if i < 1419 then decide (2 ≤ count1417 b) else decide (3 ≤ count1417 b))) else (if i < 1422 then (if i < 1421 then decide (4 ≤ count1417 b) else decide (1 ≤ count1421 b)) else (if i < 1423 then decide (2 ≤ count1421 b) else decide (1 ≤ count1423 b)))) else (if i < 1428 then (if i < 1426 then (if i < 1425 then decide (2 ≤ count1423 b) else decide (1 ≤ count1425 b)) else (if i < 1427 then decide (2 ≤ count1425 b) else decide (3 ≤ count1425 b))) else (if i < 1430 then (if i < 1429 then decide (4 ≤ count1425 b) else decide (1 ≤ count1429 b)) else (if i < 1431 then decide (2 ≤ count1429 b) else decide (3 ≤ count1429 b)))))) else (if i < 1446 then (if i < 1439 then (if i < 1435 then (if i < 1433 then decide (4 ≤ count1429 b) else (if i < 1434 then decide (5 ≤ count1429 b) else decide (6 ≤ count1429 b))) else (if i < 1437 then (if i < 1436 then decide (7 ≤ count1429 b) else decide (8 ≤ count1429 b)) else (if i < 1438 then decide (1 ≤ count1437 b) else decide (2 ≤ count1437 b)))) else (if i < 1442 then (if i < 1440 then decide (1 ≤ count1439 b) else (if i < 1441 then decide (2 ≤ count1439 b) else decide (1 ≤ count1441 b))) else (if i < 1444 then (if i < 1443 then decide (2 ≤ count1441 b) else decide (3 ≤ count1441 b)) else (if i < 1445 then decide (4 ≤ count1441 b) else decide (1 ≤ count1445 b))))) else (if i < 1453 then (if i < 1449 then (if i < 1447 then decide (2 ≤ count1445 b) else (if i < 1448 then decide (1 ≤ count1447 b) else decide (2 ≤ count1447 b))) else (if i < 1451 then (if i < 1450 then decide (1 ≤ count1449 b) else decide (2 ≤ count1449 b)) else (if i < 1452 then decide (3 ≤ count1449 b) else decide (4 ≤ count1449 b)))) else (if i < 1457 then (if i < 1455 then (if i < 1454 then decide (1 ≤ count1453 b) else decide (2 ≤ count1453 b)) else (if i < 1456 then decide (3 ≤ count1453 b) else decide (4 ≤ count1453 b))) else (if i < 1459 then (if i < 1458 then decide (5 ≤ count1453 b) else decide (6 ≤ count1453 b)) else (if i < 1460 then decide (7 ≤ count1453 b) else decide (8 ≤ count1453 b))))))) else (if i < 1490 then (if i < 1475 then (if i < 1468 then (if i < 1464 then (if i < 1462 then decide (1 ≤ count1461 b) else (if i < 1463 then decide (2 ≤ count1461 b) else decide (3 ≤ count1461 b))) else (if i < 1466 then (if i < 1465 then decide (4 ≤ count1461 b) else decide (5 ≤ count1461 b)) else (if i < 1467 then decide (6 ≤ count1461 b) else decide (7 ≤ count1461 b)))) else (if i < 1471 then (if i < 1469 then decide (8 ≤ count1461 b) else (if i < 1470 then decide (9 ≤ count1461 b) else decide (10 ≤ count1461 b))) else (if i < 1473 then (if i < 1472 then decide (11 ≤ count1461 b) else decide (12 ≤ count1461 b)) else (if i < 1474 then decide (13 ≤ count1461 b) else decide (14 ≤ count1461 b))))) else (if i < 1482 then (if i < 1478 then (if i < 1476 then decide (15 ≤ count1461 b) else (if i < 1477 then decide (16 ≤ count1461 b) else decide (1 ≤ count1477 b))) else (if i < 1480 then (if i < 1479 then decide (2 ≤ count1477 b) else decide (3 ≤ count1477 b)) else (if i < 1481 then decide (4 ≤ count1477 b) else decide (5 ≤ count1477 b)))) else (if i < 1486 then (if i < 1484 then (if i < 1483 then decide (6 ≤ count1477 b) else decide (7 ≤ count1477 b)) else (if i < 1485 then decide (8 ≤ count1477 b) else decide (9 ≤ count1477 b))) else (if i < 1488 then (if i < 1487 then decide (10 ≤ count1477 b) else decide (11 ≤ count1477 b)) else (if i < 1489 then decide (12 ≤ count1477 b) else decide (13 ≤ count1477 b)))))) else (if i < 1505 then (if i < 1497 then (if i < 1493 then (if i < 1491 then decide (14 ≤ count1477 b) else (if i < 1492 then decide (15 ≤ count1477 b) else decide (16 ≤ count1477 b))) else (if i < 1495 then (if i < 1494 then decide (17 ≤ count1477 b) else decide (18 ≤ count1477 b)) else (if i < 1496 then decide (19 ≤ count1477 b) else decide (20 ≤ count1477 b)))) else (if i < 1501 then (if i < 1499 then (if i < 1498 then decide (21 ≤ count1477 b) else decide (22 ≤ count1477 b)) else (if i < 1500 then decide (23 ≤ count1477 b) else decide (24 ≤ count1477 b))) else (if i < 1503 then (if i < 1502 then decide (25 ≤ count1477 b) else decide (26 ≤ count1477 b)) else (if i < 1504 then decide (27 ≤ count1477 b) else decide (28 ≤ count1477 b))))) else (if i < 1512 then (if i < 1508 then (if i < 1506 then decide (29 ≤ count1477 b) else (if i < 1507 then decide (30 ≤ count1477 b) else decide (31 ≤ count1477 b))) else (if i < 1510 then (if i < 1509 then decide (32 ≤ count1477 b) else decide (1 ≤ count1509 b)) else (if i < 1511 then decide (2 ≤ count1509 b) else decide (3 ≤ count1509 b)))) else (if i < 1516 then (if i < 1514 then (if i < 1513 then decide (4 ≤ count1509 b) else decide (5 ≤ count1509 b)) else (if i < 1515 then decide (6 ≤ count1509 b) else decide (7 ≤ count1509 b))) else (if i < 1518 then (if i < 1517 then decide (8 ≤ count1509 b) else decide (9 ≤ count1509 b)) else (if i < 1519 then decide (10 ≤ count1509 b) else decide (11 ≤ count1509 b)))))))) else (if i < 1578 then (if i < 1549 then (if i < 1534 then (if i < 1527 then (if i < 1523 then (if i < 1521 then decide (12 ≤ count1509 b) else (if i < 1522 then decide (13 ≤ count1509 b) else decide (14 ≤ count1509 b))) else (if i < 1525 then (if i < 1524 then decide (15 ≤ count1509 b) else decide (16 ≤ count1509 b)) else (if i < 1526 then decide (17 ≤ count1509 b) else decide (18 ≤ count1509 b)))) else (if i < 1530 then (if i < 1528 then decide (19 ≤ count1509 b) else (if i < 1529 then decide (20 ≤ count1509 b) else decide (21 ≤ count1509 b))) else (if i < 1532 then (if i < 1531 then decide (22 ≤ count1509 b) else decide (23 ≤ count1509 b)) else (if i < 1533 then decide (24 ≤ count1509 b) else decide (25 ≤ count1509 b))))) else (if i < 1541 then (if i < 1537 then (if i < 1535 then decide (26 ≤ count1509 b) else (if i < 1536 then decide (27 ≤ count1509 b) else decide (28 ≤ count1509 b))) else (if i < 1539 then (if i < 1538 then decide (29 ≤ count1509 b) else decide (30 ≤ count1509 b)) else (if i < 1540 then decide (31 ≤ count1509 b) else decide (32 ≤ count1509 b)))) else (if i < 1545 then (if i < 1543 then (if i < 1542 then decide (33 ≤ count1509 b) else decide (34 ≤ count1509 b)) else (if i < 1544 then decide (35 ≤ count1509 b) else decide (36 ≤ count1509 b))) else (if i < 1547 then (if i < 1546 then decide (37 ≤ count1509 b) else decide (38 ≤ count1509 b)) else (if i < 1548 then decide (39 ≤ count1509 b) else decide (40 ≤ count1509 b)))))) else (if i < 1563 then (if i < 1556 then (if i < 1552 then (if i < 1550 then decide (41 ≤ count1509 b) else (if i < 1551 then decide (42 ≤ count1509 b) else decide (1 ≤ count1551 b))) else (if i < 1554 then (if i < 1553 then decide (2 ≤ count1551 b) else decide (1 ≤ count1553 b)) else (if i < 1555 then decide (2 ≤ count1553 b) else decide (3 ≤ count1553 b)))) else (if i < 1559 then (if i < 1557 then decide (1 ≤ count1556 b) else (if i < 1558 then decide (2 ≤ count1556 b) else decide (1 ≤ count1558 b))) else (if i < 1561 then (if i < 1560 then decide (2 ≤ count1558 b) else decide (1 ≤ count1560 b)) else (if i < 1562 then decide (2 ≤ count1560 b) else decide (3 ≤ count1560 b))))) else (if i < 1570 then (if i < 1566 then (if i < 1564 then decide (4 ≤ count1560 b) else (if i < 1565 then decide (1 ≤ count1564 b) else decide (2 ≤ count1564 b))) else (if i < 1568 then (if i < 1567 then decide (3 ≤ count1564 b) else decide (4 ≤ count1564 b)) else (if i < 1569 then decide (5 ≤ count1564 b) else decide (6 ≤ count1564 b)))) else (if i < 1574 then (if i < 1572 then (if i < 1571 then decide (7 ≤ count1564 b) else decide (1 ≤ count1571 b)) else (if i < 1573 then decide (2 ≤ count1571 b) else decide (1 ≤ count1573 b))) else (if i < 1576 then (if i < 1575 then decide (2 ≤ count1573 b) else decide (1 ≤ count1575 b)) else (if i < 1577 then decide (2 ≤ count1575 b) else decide (3 ≤ count1575 b))))))) else (if i < 1607 then (if i < 1592 then (if i < 1585 then (if i < 1581 then (if i < 1579 then decide (4 ≤ count1575 b) else (if i < 1580 then decide (1 ≤ count1579 b) else decide (2 ≤ count1579 b))) else (if i < 1583 then (if i < 1582 then decide (1 ≤ count1581 b) else decide (2 ≤ count1581 b)) else (if i < 1584 then decide (1 ≤ count1583 b) else decide (2 ≤ count1583 b)))) else (if i < 1588 then (if i < 1586 then decide (3 ≤ count1583 b) else (if i < 1587 then decide (4 ≤ count1583 b) else decide (1 ≤ count1587 b))) else (if i < 1590 then (if i < 1589 then decide (2 ≤ count1587 b) else decide (3 ≤ count1587 b)) else (if i < 1591 then decide (4 ≤ count1587 b) else decide (5 ≤ count1587 b))))) else (if i < 1599 then (if i < 1595 then (if i < 1593 then decide (6 ≤ count1587 b) else (if i < 1594 then decide (7 ≤ count1587 b) else decide (8 ≤ count1587 b))) else (if i < 1597 then (if i < 1596 then decide (1 ≤ count1595 b) else decide (2 ≤ count1595 b)) else (if i < 1598 then decide (3 ≤ count1595 b) else decide (4 ≤ count1595 b)))) else (if i < 1603 then (if i < 1601 then (if i < 1600 then decide (5 ≤ count1595 b) else decide (6 ≤ count1595 b)) else (if i < 1602 then decide (7 ≤ count1595 b) else decide (8 ≤ count1595 b))) else (if i < 1605 then (if i < 1604 then decide (9 ≤ count1595 b) else decide (10 ≤ count1595 b)) else (if i < 1606 then decide (11 ≤ count1595 b) else decide (12 ≤ count1595 b)))))) else (if i < 1622 then (if i < 1614 then (if i < 1610 then (if i < 1608 then decide (13 ≤ count1595 b) else (if i < 1609 then decide (14 ≤ count1595 b) else decide (15 ≤ count1595 b))) else (if i < 1612 then (if i < 1611 then decide (1 ≤ count1610 b) else decide (2 ≤ count1610 b)) else (if i < 1613 then decide (1 ≤ count1612 b) else decide (2 ≤ count1612 b)))) else (if i < 1618 then (if i < 1616 then (if i < 1615 then decide (1 ≤ count1614 b) else decide (2 ≤ count1614 b)) else (if i < 1617 then decide (3 ≤ count1614 b) else decide (4 ≤ count1614 b))) else (if i < 1620 then (if i < 1619 then decide (1 ≤ count1618 b) else decide (2 ≤ count1618 b)) else (if i < 1621 then decide (1 ≤ count1620 b) else decide (2 ≤ count1620 b))))) else (if i < 1629 then (if i < 1625 then (if i < 1623 then decide (1 ≤ count1622 b) else (if i < 1624 then decide (2 ≤ count1622 b) else decide (3 ≤ count1622 b))) else (if i < 1627 then (if i < 1626 then decide (4 ≤ count1622 b) else decide (1 ≤ count1626 b)) else (if i < 1628 then decide (2 ≤ count1626 b) else decide (3 ≤ count1626 b)))) else (if i < 1633 then (if i < 1631 then (if i < 1630 then decide (4 ≤ count1626 b) else decide (5 ≤ count1626 b)) else (if i < 1632 then decide (6 ≤ count1626 b) else decide (7 ≤ count1626 b))) else (if i < 1635 then (if i < 1634 then decide (8 ≤ count1626 b) else decide (1 ≤ count1634 b)) else (if i < 1636 then decide (2 ≤ count1634 b) else decide (1 ≤ count1636 b))))))))) else (if i < 1754 then (if i < 1695 then (if i < 1666 then (if i < 1651 then (if i < 1644 then (if i < 1640 then (if i < 1638 then decide (2 ≤ count1636 b) else (if i < 1639 then decide (1 ≤ count1638 b) else decide (2 ≤ count1638 b))) else (if i < 1642 then (if i < 1641 then decide (3 ≤ count1638 b) else decide (4 ≤ count1638 b)) else (if i < 1643 then decide (1 ≤ count1642 b) else decide (2 ≤ count1642 b)))) else (if i < 1647 then (if i < 1645 then decide (1 ≤ count1644 b) else (if i < 1646 then decide (2 ≤ count1644 b) else decide (1 ≤ count1646 b))) else (if i < 1649 then (if i < 1648 then decide (2 ≤ count1646 b) else decide (3 ≤ count1646 b)) else (if i < 1650 then decide (4 ≤ count1646 b) else decide (1 ≤ count1650 b))))) else (if i < 1658 then (if i < 1654 then (if i < 1652 then decide (2 ≤ count1650 b) else (if i < 1653 then decide (3 ≤ count1650 b) else decide (4 ≤ count1650 b))) else (if i < 1656 then (if i < 1655 then decide (5 ≤ count1650 b) else decide (6 ≤ count1650 b)) else (if i < 1657 then decide (7 ≤ count1650 b) else decide (8 ≤ count1650 b)))) else (if i < 1662 then (if i < 1660 then (if i < 1659 then decide (1 ≤ count1658 b) else decide (2 ≤ count1658 b)) else (if i < 1661 then decide (3 ≤ count1658 b) else decide (4 ≤ count1658 b))) else (if i < 1664 then (if i < 1663 then decide (5 ≤ count1658 b) else decide (6 ≤ count1658 b)) else (if i < 1665 then decide (7 ≤ count1658 b) else decide (8 ≤ count1658 b)))))) else (if i < 1680 then (if i < 1673 then (if i < 1669 then (if i < 1667 then decide (9 ≤ count1658 b) else (if i < 1668 then decide (10 ≤ count1658 b) else decide (11 ≤ count1658 b))) else (if i < 1671 then (if i < 1670 then decide (12 ≤ count1658 b) else decide (13 ≤ count1658 b)) else (if i < 1672 then decide (14 ≤ count1658 b) else decide (15 ≤ count1658 b)))) else (if i < 1676 then (if i < 1674 then decide (16 ≤ count1658 b) else (if i < 1675 then decide (1 ≤ count1674 b) else decide (2 ≤ count1674 b))) else (if i < 1678 then (if i < 1677 then decide (3 ≤ count1674 b) else decide (4 ≤ count1674 b)) else (if i < 1679 then decide (5 ≤ count1674 b) else decide (6 ≤ count1674 b))))) else (if i < 1687 then (if i < 1683 then (if i < 1681 then decide (7 ≤ count1674 b) else (if i < 1682 then decide (8 ≤ count1674 b) else decide (9 ≤ count1674 b))) else (if i < 1685 then (if i < 1684 then decide (10 ≤ count1674 b) else decide (11 ≤ count1674 b)) else (if i < 1686 then decide (12 ≤ count1674 b) else decide (13 ≤ count1674 b)))) else (if i < 1691 then (if i < 1689 then (if i < 1688 then decide (14 ≤ count1674 b) else decide (15 ≤ count1674 b)) else (if i < 1690 then decide (16 ≤ count1674 b) else decide (17 ≤ count1674 b))) else (if i < 1693 then (if i < 1692 then decide (18 ≤ count1674 b) else decide (19 ≤ count1674 b)) else (if i < 1694 then decide (20 ≤ count1674 b) else decide (21 ≤ count1674 b))))))) else (if i < 1724 then (if i < 1709 then (if i < 1702 then (if i < 1698 then (if i < 1696 then decide (22 ≤ count1674 b) else (if i < 1697 then decide (23 ≤ count1674 b) else decide (1 ≤ count1697 b))) else (if i < 1700 then (if i < 1699 then decide (2 ≤ count1697 b) else decide (1 ≤ count1699 b)) else (if i < 1701 then decide (2 ≤ count1699 b) else decide (1 ≤ count1701 b)))) else (if i < 1705 then (if i < 1703 then decide (2 ≤ count1701 b) else (if i < 1704 then decide (3 ≤ count1701 b) else decide (4 ≤ count1701 b))) else (if i < 1707 then (if i < 1706 then decide (1 ≤ count1705 b) else decide (2 ≤ count1705 b)) else (if i < 1708 then decide (1 ≤ count1707 b) else decide (2 ≤ count1707 b))))) else (if i < 1716 then (if i < 1712 then (if i < 1710 then decide (1 ≤ count1709 b) else (if i < 1711 then decide (2 ≤ count1709 b) else decide (3 ≤ count1709 b))) else (if i < 1714 then (if i < 1713 then decide (4 ≤ count1709 b) else decide (1 ≤ count1713 b)) else (if i < 1715 then decide (2 ≤ count1713 b) else decide (3 ≤ count1713 b)))) else (if i < 1720 then (if i < 1718 then (if i < 1717 then decide (4 ≤ count1713 b) else decide (5 ≤ count1713 b)) else (if i < 1719 then decide (6 ≤ count1713 b) else decide (7 ≤ count1713 b))) else (if i < 1722 then (if i < 1721 then decide (8 ≤ count1713 b) else decide (1 ≤ count1721 b)) else (if i < 1723 then decide (2 ≤ count1721 b) else decide (1 ≤ count1723 b)))))) else (if i < 1739 then (if i < 1731 then (if i < 1727 then (if i < 1725 then decide (2 ≤ count1723 b) else (if i < 1726 then decide (1 ≤ count1725 b) else decide (2 ≤ count1725 b))) else (if i < 1729 then (if i < 1728 then decide (3 ≤ count1725 b) else decide (4 ≤ count1725 b)) else (if i < 1730 then decide (1 ≤ count1729 b) else decide (2 ≤ count1729 b)))) else (if i < 1735 then (if i < 1733 then (if i < 1732 then decide (1 ≤ count1731 b) else decide (2 ≤ count1731 b)) else (if i < 1734 then decide (1 ≤ count1733 b) else decide (2 ≤ count1733 b))) else (if i < 1737 then (if i < 1736 then decide (3 ≤ count1733 b) else decide (4 ≤ count1733 b)) else (if i < 1738 then decide (1 ≤ count1737 b) else decide (2 ≤ count1737 b))))) else (if i < 1746 then (if i < 1742 then (if i < 1740 then decide (3 ≤ count1737 b) else (if i < 1741 then decide (4 ≤ count1737 b) else decide (5 ≤ count1737 b))) else (if i < 1744 then (if i < 1743 then decide (6 ≤ count1737 b) else decide (7 ≤ count1737 b)) else (if i < 1745 then decide (8 ≤ count1737 b) else decide (1 ≤ count1745 b)))) else (if i < 1750 then (if i < 1748 then (if i < 1747 then decide (2 ≤ count1745 b) else decide (3 ≤ count1745 b)) else (if i < 1749 then decide (4 ≤ count1745 b) else decide (5 ≤ count1745 b))) else (if i < 1752 then (if i < 1751 then decide (6 ≤ count1745 b) else decide (7 ≤ count1745 b)) else (if i < 1753 then decide (8 ≤ count1745 b) else decide (9 ≤ count1745 b)))))))) else (if i < 1812 then (if i < 1783 then (if i < 1768 then (if i < 1761 then (if i < 1757 then (if i < 1755 then decide (10 ≤ count1745 b) else (if i < 1756 then decide (11 ≤ count1745 b) else decide (12 ≤ count1745 b))) else (if i < 1759 then (if i < 1758 then decide (13 ≤ count1745 b) else decide (14 ≤ count1745 b)) else (if i < 1760 then decide (15 ≤ count1745 b) else decide (16 ≤ count1745 b)))) else (if i < 1764 then (if i < 1762 then decide (1 ≤ count1761 b) else (if i < 1763 then decide (2 ≤ count1761 b) else decide (1 ≤ count1763 b))) else (if i < 1766 then (if i < 1765 then decide (2 ≤ count1763 b) else decide (1 ≤ count1765 b)) else (if i < 1767 then decide (2 ≤ count1765 b) else decide (3 ≤ count1765 b))))) else (if i < 1775 then (if i < 1771 then (if i < 1769 then decide (4 ≤ count1765 b) else (if i < 1770 then decide (1 ≤ count1769 b) else decide (2 ≤ count1769 b))) else (if i < 1773 then (if i < 1772 then decide (1 ≤ count1771 b) else decide (2 ≤ count1771 b)) else (if i < 1774 then decide (1 ≤ count1773 b) else decide (2 ≤ count1773 b)))) else (if i < 1779 then (if i < 1777 then (if i < 1776 then decide (3 ≤ count1773 b) else decide (4 ≤ count1773 b)) else (if i < 1778 then decide (1 ≤ count1777 b) else decide (2 ≤ count1777 b))) else (if i < 1781 then (if i < 1780 then decide (3 ≤ count1777 b) else decide (4 ≤ count1777 b)) else (if i < 1782 then decide (5 ≤ count1777 b) else decide (6 ≤ count1777 b)))))) else (if i < 1797 then (if i < 1790 then (if i < 1786 then (if i < 1784 then decide (7 ≤ count1777 b) else (if i < 1785 then decide (8 ≤ count1777 b) else decide (1 ≤ count1785 b))) else (if i < 1788 then (if i < 1787 then decide (2 ≤ count1785 b) else decide (1 ≤ count1787 b)) else (if i < 1789 then decide (2 ≤ count1787 b) else decide (1 ≤ count1789 b)))) else (if i < 1793 then (if i < 1791 then decide (2 ≤ count1789 b) else (if i < 1792 then decide (3 ≤ count1789 b) else decide (4 ≤ count1789 b))) else (if i < 1795 then (if i < 1794 then decide (1 ≤ count1793 b) else decide (2 ≤ count1793 b)) else (if i < 1796 then decide (1 ≤ count1795 b) else decide (2 ≤ count1795 b))))) else (if i < 1804 then (if i < 1800 then (if i < 1798 then decide (1 ≤ count1797 b) else (if i < 1799 then decide (2 ≤ count1797 b) else decide (3 ≤ count1797 b))) else (if i < 1802 then (if i < 1801 then decide (4 ≤ count1797 b) else decide (1 ≤ count1801 b)) else (if i < 1803 then decide (2 ≤ count1801 b) else decide (3 ≤ count1801 b)))) else (if i < 1808 then (if i < 1806 then (if i < 1805 then decide (4 ≤ count1801 b) else decide (5 ≤ count1801 b)) else (if i < 1807 then decide (6 ≤ count1801 b) else decide (7 ≤ count1801 b))) else (if i < 1810 then (if i < 1809 then decide (8 ≤ count1801 b) else decide (1 ≤ count1809 b)) else (if i < 1811 then decide (2 ≤ count1809 b) else decide (3 ≤ count1809 b))))))) else (if i < 1841 then (if i < 1826 then (if i < 1819 then (if i < 1815 then (if i < 1813 then decide (4 ≤ count1809 b) else (if i < 1814 then decide (5 ≤ count1809 b) else decide (6 ≤ count1809 b))) else (if i < 1817 then (if i < 1816 then decide (7 ≤ count1809 b) else decide (8 ≤ count1809 b)) else (if i < 1818 then decide (9 ≤ count1809 b) else decide (10 ≤ count1809 b)))) else (if i < 1822 then (if i < 1820 then decide (11 ≤ count1809 b) else (if i < 1821 then decide (12 ≤ count1809 b) else decide (13 ≤ count1809 b))) else (if i < 1824 then (if i < 1823 then decide (14 ≤ count1809 b) else decide (15 ≤ count1809 b)) else (if i < 1825 then decide (16 ≤ count1809 b) else decide (1 ≤ count1825 b))))) else (if i < 1833 then (if i < 1829 then (if i < 1827 then decide (2 ≤ count1825 b) else (if i < 1828 then decide (3 ≤ count1825 b) else decide (4 ≤ count1825 b))) else (if i < 1831 then (if i < 1830 then decide (5 ≤ count1825 b) else decide (6 ≤ count1825 b)) else (if i < 1832 then decide (7 ≤ count1825 b) else decide (8 ≤ count1825 b)))) else (if i < 1837 then (if i < 1835 then (if i < 1834 then decide (9 ≤ count1825 b) else decide (10 ≤ count1825 b)) else (if i < 1836 then decide (11 ≤ count1825 b) else decide (12 ≤ count1825 b))) else (if i < 1839 then (if i < 1838 then decide (13 ≤ count1825 b) else decide (14 ≤ count1825 b)) else (if i < 1840 then decide (15 ≤ count1825 b) else decide (16 ≤ count1825 b)))))) else (if i < 1856 then (if i < 1848 then (if i < 1844 then (if i < 1842 then decide (17 ≤ count1825 b) else (if i < 1843 then decide (18 ≤ count1825 b) else decide (19 ≤ count1825 b))) else (if i < 1846 then (if i < 1845 then decide (20 ≤ count1825 b) else decide (21 ≤ count1825 b)) else (if i < 1847 then decide (22 ≤ count1825 b) else decide (23 ≤ count1825 b)))) else (if i < 1852 then (if i < 1850 then (if i < 1849 then decide (1 ≤ count1848 b) else decide (2 ≤ count1848 b)) else (if i < 1851 then decide (3 ≤ count1848 b) else decide (4 ≤ count1848 b))) else (if i < 1854 then (if i < 1853 then decide (5 ≤ count1848 b) else decide (6 ≤ count1848 b)) else (if i < 1855 then decide (7 ≤ count1848 b) else decide (8 ≤ count1848 b))))) else (if i < 1863 then (if i < 1859 then (if i < 1857 then decide (9 ≤ count1848 b) else (if i < 1858 then decide (10 ≤ count1848 b) else decide (11 ≤ count1848 b))) else (if i < 1861 then (if i < 1860 then decide (12 ≤ count1848 b) else decide (13 ≤ count1848 b)) else (if i < 1862 then decide (14 ≤ count1848 b) else decide (15 ≤ count1848 b)))) else (if i < 1867 then (if i < 1865 then (if i < 1864 then decide (16 ≤ count1848 b) else decide (17 ≤ count1848 b)) else (if i < 1866 then decide (18 ≤ count1848 b) else decide (19 ≤ count1848 b))) else (if i < 1869 then (if i < 1868 then decide (20 ≤ count1848 b) else decide (21 ≤ count1848 b)) else (if i < 1870 then decide (22 ≤ count1848 b) else decide (23 ≤ count1848 b))))))))))))
def valuation (q : Snake 81) : Nat → Bool := valuationOf (baseVal q)
theorem value1 (q : Snake 81) : valuation q 1 = decide (InPath q (0 : Vertex)) := rfl
theorem value2 (q : Snake 81) : valuation q 2 = decide (InPath q (1 : Vertex)) := rfl
theorem value3 (q : Snake 81) : valuation q 3 = decide (InPath q (2 : Vertex)) := rfl
theorem value4 (q : Snake 81) : valuation q 4 = decide (InPath q (5 : Vertex)) := rfl
theorem value5 (q : Snake 81) : valuation q 5 = decide (InPath q (8 : Vertex)) := rfl
theorem value6 (q : Snake 81) : valuation q 6 = decide (InPath q (10 : Vertex)) := rfl
theorem value7 (q : Snake 81) : valuation q 7 = decide (InPath q (12 : Vertex)) := rfl
theorem value8 (q : Snake 81) : valuation q 8 = decide (InPath q (14 : Vertex)) := rfl
theorem value9 (q : Snake 81) : valuation q 9 = decide (InPath q (15 : Vertex)) := rfl
theorem value10 (q : Snake 81) : valuation q 10 = decide (InPath q (17 : Vertex)) := rfl
theorem value11 (q : Snake 81) : valuation q 11 = decide (InPath q (18 : Vertex)) := rfl
theorem value12 (q : Snake 81) : valuation q 12 = decide (InPath q (19 : Vertex)) := rfl
theorem value13 (q : Snake 81) : valuation q 13 = decide (InPath q (21 : Vertex)) := rfl
theorem value14 (q : Snake 81) : valuation q 14 = decide (InPath q (22 : Vertex)) := rfl
theorem value15 (q : Snake 81) : valuation q 15 = decide (InPath q (23 : Vertex)) := rfl
theorem value16 (q : Snake 81) : valuation q 16 = decide (InPath q (25 : Vertex)) := rfl
theorem value17 (q : Snake 81) : valuation q 17 = decide (InPath q (27 : Vertex)) := rfl
theorem value18 (q : Snake 81) : valuation q 18 = decide (InPath q (28 : Vertex)) := rfl
theorem value19 (q : Snake 81) : valuation q 19 = decide (InPath q (29 : Vertex)) := rfl
theorem value20 (q : Snake 81) : valuation q 20 = decide (InPath q (31 : Vertex)) := rfl
theorem value21 (q : Snake 81) : valuation q 21 = decide (InPath q (67 : Vertex)) := rfl
theorem value22 (q : Snake 81) : valuation q 22 = decide (InPath q (68 : Vertex)) := rfl
theorem value23 (q : Snake 81) : valuation q 23 = decide (InPath q (69 : Vertex)) := rfl
theorem value24 (q : Snake 81) : valuation q 24 = decide (InPath q (70 : Vertex)) := rfl
theorem value25 (q : Snake 81) : valuation q 25 = decide (InPath q (71 : Vertex)) := rfl
theorem value26 (q : Snake 81) : valuation q 26 = decide (InPath q (72 : Vertex)) := rfl
theorem value27 (q : Snake 81) : valuation q 27 = decide (InPath q (73 : Vertex)) := rfl
theorem value28 (q : Snake 81) : valuation q 28 = decide (InPath q (75 : Vertex)) := rfl
theorem value29 (q : Snake 81) : valuation q 29 = decide (InPath q (79 : Vertex)) := rfl
theorem value30 (q : Snake 81) : valuation q 30 = decide (InPath q (80 : Vertex)) := rfl
theorem value31 (q : Snake 81) : valuation q 31 = decide (InPath q (82 : Vertex)) := rfl
theorem value32 (q : Snake 81) : valuation q 32 = decide (InPath q (84 : Vertex)) := rfl
theorem value33 (q : Snake 81) : valuation q 33 = decide (InPath q (85 : Vertex)) := rfl
theorem value34 (q : Snake 81) : valuation q 34 = decide (InPath q (88 : Vertex)) := rfl
theorem value35 (q : Snake 81) : valuation q 35 = decide (InPath q (90 : Vertex)) := rfl
theorem value36 (q : Snake 81) : valuation q 36 = decide (InPath q (92 : Vertex)) := rfl
theorem value37 (q : Snake 81) : valuation q 37 = decide (InPath q (94 : Vertex)) := rfl
theorem value38 (q : Snake 81) : valuation q 38 = decide (InPath q (131 : Vertex)) := rfl
theorem value39 (q : Snake 81) : valuation q 39 = decide (InPath q (132 : Vertex)) := rfl
theorem value40 (q : Snake 81) : valuation q 40 = decide (InPath q (133 : Vertex)) := rfl
theorem value41 (q : Snake 81) : valuation q 41 = decide (InPath q (134 : Vertex)) := rfl
theorem value42 (q : Snake 81) : valuation q 42 = decide (InPath q (135 : Vertex)) := rfl
theorem value43 (q : Snake 81) : valuation q 43 = decide (InPath q (136 : Vertex)) := rfl
theorem value44 (q : Snake 81) : valuation q 44 = decide (InPath q (137 : Vertex)) := rfl
theorem value45 (q : Snake 81) : valuation q 45 = decide (InPath q (138 : Vertex)) := rfl
theorem value46 (q : Snake 81) : valuation q 46 = decide (InPath q (139 : Vertex)) := rfl
theorem value47 (q : Snake 81) : valuation q 47 = decide (InPath q (141 : Vertex)) := rfl
theorem value48 (q : Snake 81) : valuation q 48 = decide (InPath q (144 : Vertex)) := rfl
theorem value49 (q : Snake 81) : valuation q 49 = decide (InPath q (148 : Vertex)) := rfl
theorem value50 (q : Snake 81) : valuation q 50 = decide (InPath q (149 : Vertex)) := rfl
theorem value51 (q : Snake 81) : valuation q 51 = decide (InPath q (150 : Vertex)) := rfl
theorem value52 (q : Snake 81) : valuation q 52 = decide (InPath q (151 : Vertex)) := rfl
theorem value53 (q : Snake 81) : valuation q 53 = decide (InPath q (152 : Vertex)) := rfl
theorem value54 (q : Snake 81) : valuation q 54 = decide (InPath q (154 : Vertex)) := rfl
theorem value55 (q : Snake 81) : valuation q 55 = decide (InPath q (158 : Vertex)) := rfl
theorem value56 (q : Snake 81) : valuation q 56 = decide (InPath q (192 : Vertex)) := rfl
theorem value57 (q : Snake 81) : valuation q 57 = decide (InPath q (193 : Vertex)) := rfl
theorem value58 (q : Snake 81) : valuation q 58 = decide (InPath q (194 : Vertex)) := rfl
theorem value59 (q : Snake 81) : valuation q 59 = decide (InPath q (197 : Vertex)) := rfl
theorem value60 (q : Snake 81) : valuation q 60 = decide (InPath q (202 : Vertex)) := rfl
theorem value61 (q : Snake 81) : valuation q 61 = decide (InPath q (204 : Vertex)) := rfl
theorem value62 (q : Snake 81) : valuation q 62 = decide (InPath q (206 : Vertex)) := rfl
theorem value63 (q : Snake 81) : valuation q 63 = decide (InPath q (208 : Vertex)) := rfl
theorem value64 (q : Snake 81) : valuation q 64 = decide (InPath q (222 : Vertex)) := rfl
theorem value65 (q : Snake 81) : valuation q 65 = decide (InPath q (228 : Vertex)) := rfl
theorem value66 (q : Snake 81) : valuation q 66 = decide (InPath q (229 : Vertex)) := rfl
theorem value67 (q : Snake 81) : valuation q 67 = decide (InPath q (245 : Vertex)) := rfl
theorem value68 (q : Snake 81) : valuation q 68 = decide (InPath q (259 : Vertex)) := rfl
theorem value69 (q : Snake 81) : valuation q 69 = decide (InPath q (260 : Vertex)) := rfl
theorem value70 (q : Snake 81) : valuation q 70 = decide (InPath q (261 : Vertex)) := rfl
theorem value71 (q : Snake 81) : valuation q 71 = decide (InPath q (262 : Vertex)) := rfl
theorem value72 (q : Snake 81) : valuation q 72 = decide (InPath q (263 : Vertex)) := rfl
theorem value73 (q : Snake 81) : valuation q 73 = decide (InPath q (264 : Vertex)) := rfl
theorem value74 (q : Snake 81) : valuation q 74 = decide (InPath q (265 : Vertex)) := rfl
theorem value75 (q : Snake 81) : valuation q 75 = decide (InPath q (267 : Vertex)) := rfl
theorem value76 (q : Snake 81) : valuation q 76 = decide (InPath q (268 : Vertex)) := rfl
theorem value77 (q : Snake 81) : valuation q 77 = decide (InPath q (269 : Vertex)) := rfl
theorem value78 (q : Snake 81) : valuation q 78 = decide (InPath q (271 : Vertex)) := rfl
theorem value79 (q : Snake 81) : valuation q 79 = decide (InPath q (272 : Vertex)) := rfl
theorem value80 (q : Snake 81) : valuation q 80 = decide (InPath q (274 : Vertex)) := rfl
theorem value81 (q : Snake 81) : valuation q 81 = decide (InPath q (276 : Vertex)) := rfl
theorem value82 (q : Snake 81) : valuation q 82 = decide (InPath q (277 : Vertex)) := rfl
theorem value83 (q : Snake 81) : valuation q 83 = decide (InPath q (278 : Vertex)) := rfl
theorem value84 (q : Snake 81) : valuation q 84 = decide (InPath q (279 : Vertex)) := rfl
theorem value85 (q : Snake 81) : valuation q 85 = decide (InPath q (280 : Vertex)) := rfl
theorem value86 (q : Snake 81) : valuation q 86 = decide (InPath q (281 : Vertex)) := rfl
theorem value87 (q : Snake 81) : valuation q 87 = decide (InPath q (282 : Vertex)) := rfl
theorem value88 (q : Snake 81) : valuation q 88 = decide (InPath q (283 : Vertex)) := rfl
theorem value89 (q : Snake 81) : valuation q 89 = decide (InPath q (284 : Vertex)) := rfl
theorem value90 (q : Snake 81) : valuation q 90 = decide (InPath q (287 : Vertex)) := rfl
theorem value91 (q : Snake 81) : valuation q 91 = decide (InPath q (320 : Vertex)) := rfl
theorem value92 (q : Snake 81) : valuation q 92 = decide (InPath q (321 : Vertex)) := rfl
theorem value93 (q : Snake 81) : valuation q 93 = decide (InPath q (322 : Vertex)) := rfl
theorem value94 (q : Snake 81) : valuation q 94 = decide (InPath q (323 : Vertex)) := rfl
theorem value95 (q : Snake 81) : valuation q 95 = decide (InPath q (325 : Vertex)) := rfl
theorem value96 (q : Snake 81) : valuation q 96 = decide (InPath q (330 : Vertex)) := rfl
theorem value97 (q : Snake 81) : valuation q 97 = decide (InPath q (332 : Vertex)) := rfl
theorem value98 (q : Snake 81) : valuation q 98 = decide (InPath q (333 : Vertex)) := rfl
theorem value99 (q : Snake 81) : valuation q 99 = decide (InPath q (334 : Vertex)) := rfl
theorem value100 (q : Snake 81) : valuation q 100 = decide (InPath q (336 : Vertex)) := rfl
theorem value101 (q : Snake 81) : valuation q 101 = decide (InPath q (337 : Vertex)) := rfl
theorem value102 (q : Snake 81) : valuation q 102 = decide (InPath q (342 : Vertex)) := rfl
theorem value103 (q : Snake 81) : valuation q 103 = decide (InPath q (343 : Vertex)) := rfl
theorem value104 (q : Snake 81) : valuation q 104 = decide (InPath q (345 : Vertex)) := rfl
theorem value105 (q : Snake 81) : valuation q 105 = decide (InPath q (347 : Vertex)) := rfl
theorem value106 (q : Snake 81) : valuation q 106 = decide (InPath q (348 : Vertex)) := rfl
theorem value107 (q : Snake 81) : valuation q 107 = decide (InPath q (350 : Vertex)) := rfl
theorem value108 (q : Snake 81) : valuation q 108 = decide (InPath q (351 : Vertex)) := rfl
theorem value109 (q : Snake 81) : valuation q 109 = decide (InPath q (384 : Vertex)) := rfl
theorem value110 (q : Snake 81) : valuation q 110 = decide (InPath q (385 : Vertex)) := rfl
theorem value111 (q : Snake 81) : valuation q 111 = decide (InPath q (386 : Vertex)) := rfl
theorem value112 (q : Snake 81) : valuation q 112 = decide (InPath q (389 : Vertex)) := rfl
theorem value113 (q : Snake 81) : valuation q 113 = decide (InPath q (394 : Vertex)) := rfl
theorem value114 (q : Snake 81) : valuation q 114 = decide (InPath q (396 : Vertex)) := rfl
theorem value115 (q : Snake 81) : valuation q 115 = decide (InPath q (397 : Vertex)) := rfl
theorem value116 (q : Snake 81) : valuation q 116 = decide (InPath q (398 : Vertex)) := rfl
theorem value117 (q : Snake 81) : valuation q 117 = decide (InPath q (400 : Vertex)) := rfl
theorem value118 (q : Snake 81) : valuation q 118 = decide (InPath q (401 : Vertex)) := rfl
theorem value119 (q : Snake 81) : valuation q 119 = decide (InPath q (403 : Vertex)) := rfl
theorem value120 (q : Snake 81) : valuation q 120 = decide (InPath q (406 : Vertex)) := rfl
theorem value121 (q : Snake 81) : valuation q 121 = decide (InPath q (407 : Vertex)) := rfl
theorem value122 (q : Snake 81) : valuation q 122 = decide (InPath q (409 : Vertex)) := rfl
theorem value123 (q : Snake 81) : valuation q 123 = decide (InPath q (411 : Vertex)) := rfl
theorem value124 (q : Snake 81) : valuation q 124 = decide (InPath q (412 : Vertex)) := rfl
theorem value125 (q : Snake 81) : valuation q 125 = decide (InPath q (414 : Vertex)) := rfl
theorem value126 (q : Snake 81) : valuation q 126 = decide (InPath q (415 : Vertex)) := rfl
theorem value127 (q : Snake 81) : valuation q 127 = decide (InPath q (485 : Vertex)) := rfl
theorem value128 (q : Snake 81) : valuation q 128 = decide (BallClauseLogic.Endpoint q (0 : Vertex)) := rfl
theorem value129 (q : Snake 81) : valuation q 129 = decide (BallClauseLogic.Endpoint q (1 : Vertex)) := rfl
theorem value130 (q : Snake 81) : valuation q 130 = decide (BallClauseLogic.Endpoint q (2 : Vertex)) := rfl
theorem value131 (q : Snake 81) : valuation q 131 = decide (BallClauseLogic.Endpoint q (5 : Vertex)) := rfl
theorem value132 (q : Snake 81) : valuation q 132 = decide (BallClauseLogic.Endpoint q (8 : Vertex)) := rfl
theorem value133 (q : Snake 81) : valuation q 133 = decide (BallClauseLogic.Endpoint q (10 : Vertex)) := rfl
theorem value134 (q : Snake 81) : valuation q 134 = decide (BallClauseLogic.Endpoint q (12 : Vertex)) := rfl
theorem value135 (q : Snake 81) : valuation q 135 = decide (BallClauseLogic.Endpoint q (14 : Vertex)) := rfl
theorem value136 (q : Snake 81) : valuation q 136 = decide (BallClauseLogic.Endpoint q (15 : Vertex)) := rfl
theorem value137 (q : Snake 81) : valuation q 137 = decide (BallClauseLogic.Endpoint q (17 : Vertex)) := rfl
theorem value138 (q : Snake 81) : valuation q 138 = decide (BallClauseLogic.Endpoint q (18 : Vertex)) := rfl
theorem value139 (q : Snake 81) : valuation q 139 = decide (BallClauseLogic.Endpoint q (19 : Vertex)) := rfl
theorem value140 (q : Snake 81) : valuation q 140 = decide (BallClauseLogic.Endpoint q (21 : Vertex)) := rfl
theorem value141 (q : Snake 81) : valuation q 141 = decide (BallClauseLogic.Endpoint q (22 : Vertex)) := rfl
theorem value142 (q : Snake 81) : valuation q 142 = decide (BallClauseLogic.Endpoint q (23 : Vertex)) := rfl
theorem value143 (q : Snake 81) : valuation q 143 = decide (BallClauseLogic.Endpoint q (25 : Vertex)) := rfl
theorem value144 (q : Snake 81) : valuation q 144 = decide (BallClauseLogic.Endpoint q (27 : Vertex)) := rfl
theorem value145 (q : Snake 81) : valuation q 145 = decide (BallClauseLogic.Endpoint q (28 : Vertex)) := rfl
theorem value146 (q : Snake 81) : valuation q 146 = decide (BallClauseLogic.Endpoint q (29 : Vertex)) := rfl
theorem value147 (q : Snake 81) : valuation q 147 = decide (BallClauseLogic.Endpoint q (31 : Vertex)) := rfl
theorem value148 (q : Snake 81) : valuation q 148 = decide (BallClauseLogic.Endpoint q (67 : Vertex)) := rfl
theorem value149 (q : Snake 81) : valuation q 149 = decide (BallClauseLogic.Endpoint q (68 : Vertex)) := rfl
theorem value150 (q : Snake 81) : valuation q 150 = decide (BallClauseLogic.Endpoint q (69 : Vertex)) := rfl
theorem value151 (q : Snake 81) : valuation q 151 = decide (BallClauseLogic.Endpoint q (70 : Vertex)) := rfl
theorem value152 (q : Snake 81) : valuation q 152 = decide (BallClauseLogic.Endpoint q (71 : Vertex)) := rfl
theorem value153 (q : Snake 81) : valuation q 153 = decide (BallClauseLogic.Endpoint q (72 : Vertex)) := rfl
theorem value154 (q : Snake 81) : valuation q 154 = decide (BallClauseLogic.Endpoint q (73 : Vertex)) := rfl
theorem value155 (q : Snake 81) : valuation q 155 = decide (BallClauseLogic.Endpoint q (75 : Vertex)) := rfl
theorem value156 (q : Snake 81) : valuation q 156 = decide (BallClauseLogic.Endpoint q (79 : Vertex)) := rfl
theorem value157 (q : Snake 81) : valuation q 157 = decide (BallClauseLogic.Endpoint q (80 : Vertex)) := rfl
theorem value158 (q : Snake 81) : valuation q 158 = decide (BallClauseLogic.Endpoint q (82 : Vertex)) := rfl
theorem value159 (q : Snake 81) : valuation q 159 = decide (BallClauseLogic.Endpoint q (84 : Vertex)) := rfl
theorem value160 (q : Snake 81) : valuation q 160 = decide (BallClauseLogic.Endpoint q (85 : Vertex)) := rfl
theorem value161 (q : Snake 81) : valuation q 161 = decide (BallClauseLogic.Endpoint q (88 : Vertex)) := rfl
theorem value162 (q : Snake 81) : valuation q 162 = decide (BallClauseLogic.Endpoint q (90 : Vertex)) := rfl
theorem value163 (q : Snake 81) : valuation q 163 = decide (BallClauseLogic.Endpoint q (92 : Vertex)) := rfl
theorem value164 (q : Snake 81) : valuation q 164 = decide (BallClauseLogic.Endpoint q (94 : Vertex)) := rfl
theorem value165 (q : Snake 81) : valuation q 165 = decide (BallClauseLogic.Endpoint q (131 : Vertex)) := rfl
theorem value166 (q : Snake 81) : valuation q 166 = decide (BallClauseLogic.Endpoint q (132 : Vertex)) := rfl
theorem value167 (q : Snake 81) : valuation q 167 = decide (BallClauseLogic.Endpoint q (133 : Vertex)) := rfl
theorem value168 (q : Snake 81) : valuation q 168 = decide (BallClauseLogic.Endpoint q (134 : Vertex)) := rfl
theorem value169 (q : Snake 81) : valuation q 169 = decide (BallClauseLogic.Endpoint q (135 : Vertex)) := rfl
theorem value170 (q : Snake 81) : valuation q 170 = decide (BallClauseLogic.Endpoint q (136 : Vertex)) := rfl
theorem value171 (q : Snake 81) : valuation q 171 = decide (BallClauseLogic.Endpoint q (137 : Vertex)) := rfl
theorem value172 (q : Snake 81) : valuation q 172 = decide (BallClauseLogic.Endpoint q (138 : Vertex)) := rfl
theorem value173 (q : Snake 81) : valuation q 173 = decide (BallClauseLogic.Endpoint q (139 : Vertex)) := rfl
theorem value174 (q : Snake 81) : valuation q 174 = decide (BallClauseLogic.Endpoint q (141 : Vertex)) := rfl
theorem value175 (q : Snake 81) : valuation q 175 = decide (BallClauseLogic.Endpoint q (144 : Vertex)) := rfl
theorem value176 (q : Snake 81) : valuation q 176 = decide (BallClauseLogic.Endpoint q (148 : Vertex)) := rfl
theorem value177 (q : Snake 81) : valuation q 177 = decide (BallClauseLogic.Endpoint q (149 : Vertex)) := rfl
theorem value178 (q : Snake 81) : valuation q 178 = decide (BallClauseLogic.Endpoint q (150 : Vertex)) := rfl
theorem value179 (q : Snake 81) : valuation q 179 = decide (BallClauseLogic.Endpoint q (151 : Vertex)) := rfl
theorem value180 (q : Snake 81) : valuation q 180 = decide (BallClauseLogic.Endpoint q (152 : Vertex)) := rfl
theorem value181 (q : Snake 81) : valuation q 181 = decide (BallClauseLogic.Endpoint q (154 : Vertex)) := rfl
theorem value182 (q : Snake 81) : valuation q 182 = decide (BallClauseLogic.Endpoint q (158 : Vertex)) := rfl
theorem value183 (q : Snake 81) : valuation q 183 = decide (BallClauseLogic.Endpoint q (192 : Vertex)) := rfl
theorem value184 (q : Snake 81) : valuation q 184 = decide (BallClauseLogic.Endpoint q (193 : Vertex)) := rfl
theorem value185 (q : Snake 81) : valuation q 185 = decide (BallClauseLogic.Endpoint q (194 : Vertex)) := rfl
theorem value186 (q : Snake 81) : valuation q 186 = decide (BallClauseLogic.Endpoint q (197 : Vertex)) := rfl
theorem value187 (q : Snake 81) : valuation q 187 = decide (BallClauseLogic.Endpoint q (202 : Vertex)) := rfl
theorem value188 (q : Snake 81) : valuation q 188 = decide (BallClauseLogic.Endpoint q (204 : Vertex)) := rfl
theorem value189 (q : Snake 81) : valuation q 189 = decide (BallClauseLogic.Endpoint q (206 : Vertex)) := rfl
theorem value190 (q : Snake 81) : valuation q 190 = decide (BallClauseLogic.Endpoint q (208 : Vertex)) := rfl
theorem value191 (q : Snake 81) : valuation q 191 = decide (BallClauseLogic.Endpoint q (222 : Vertex)) := rfl
theorem value192 (q : Snake 81) : valuation q 192 = decide (BallClauseLogic.Endpoint q (228 : Vertex)) := rfl
theorem value193 (q : Snake 81) : valuation q 193 = decide (BallClauseLogic.Endpoint q (229 : Vertex)) := rfl
theorem value194 (q : Snake 81) : valuation q 194 = decide (BallClauseLogic.Endpoint q (245 : Vertex)) := rfl
theorem value195 (q : Snake 81) : valuation q 195 = decide (BallClauseLogic.Endpoint q (259 : Vertex)) := rfl
theorem value196 (q : Snake 81) : valuation q 196 = decide (BallClauseLogic.Endpoint q (260 : Vertex)) := rfl
theorem value197 (q : Snake 81) : valuation q 197 = decide (BallClauseLogic.Endpoint q (261 : Vertex)) := rfl
theorem value198 (q : Snake 81) : valuation q 198 = decide (BallClauseLogic.Endpoint q (262 : Vertex)) := rfl
theorem value199 (q : Snake 81) : valuation q 199 = decide (BallClauseLogic.Endpoint q (263 : Vertex)) := rfl
theorem value200 (q : Snake 81) : valuation q 200 = decide (BallClauseLogic.Endpoint q (264 : Vertex)) := rfl
theorem value201 (q : Snake 81) : valuation q 201 = decide (BallClauseLogic.Endpoint q (265 : Vertex)) := rfl
theorem value202 (q : Snake 81) : valuation q 202 = decide (BallClauseLogic.Endpoint q (267 : Vertex)) := rfl
theorem value203 (q : Snake 81) : valuation q 203 = decide (BallClauseLogic.Endpoint q (268 : Vertex)) := rfl
theorem value204 (q : Snake 81) : valuation q 204 = decide (BallClauseLogic.Endpoint q (269 : Vertex)) := rfl
theorem value205 (q : Snake 81) : valuation q 205 = decide (BallClauseLogic.Endpoint q (271 : Vertex)) := rfl
theorem value206 (q : Snake 81) : valuation q 206 = decide (BallClauseLogic.Endpoint q (272 : Vertex)) := rfl
theorem value207 (q : Snake 81) : valuation q 207 = decide (BallClauseLogic.Endpoint q (274 : Vertex)) := rfl
theorem value208 (q : Snake 81) : valuation q 208 = decide (BallClauseLogic.Endpoint q (276 : Vertex)) := rfl
theorem value209 (q : Snake 81) : valuation q 209 = decide (BallClauseLogic.Endpoint q (277 : Vertex)) := rfl
theorem value210 (q : Snake 81) : valuation q 210 = decide (BallClauseLogic.Endpoint q (278 : Vertex)) := rfl
theorem value211 (q : Snake 81) : valuation q 211 = decide (BallClauseLogic.Endpoint q (279 : Vertex)) := rfl
theorem value212 (q : Snake 81) : valuation q 212 = decide (BallClauseLogic.Endpoint q (280 : Vertex)) := rfl
theorem value213 (q : Snake 81) : valuation q 213 = decide (BallClauseLogic.Endpoint q (281 : Vertex)) := rfl
theorem value214 (q : Snake 81) : valuation q 214 = decide (BallClauseLogic.Endpoint q (282 : Vertex)) := rfl
theorem value215 (q : Snake 81) : valuation q 215 = decide (BallClauseLogic.Endpoint q (283 : Vertex)) := rfl
theorem value216 (q : Snake 81) : valuation q 216 = decide (BallClauseLogic.Endpoint q (284 : Vertex)) := rfl
theorem value217 (q : Snake 81) : valuation q 217 = decide (BallClauseLogic.Endpoint q (287 : Vertex)) := rfl
theorem value218 (q : Snake 81) : valuation q 218 = decide (BallClauseLogic.Endpoint q (320 : Vertex)) := rfl
theorem value219 (q : Snake 81) : valuation q 219 = decide (BallClauseLogic.Endpoint q (321 : Vertex)) := rfl
theorem value220 (q : Snake 81) : valuation q 220 = decide (BallClauseLogic.Endpoint q (322 : Vertex)) := rfl
theorem value221 (q : Snake 81) : valuation q 221 = decide (BallClauseLogic.Endpoint q (323 : Vertex)) := rfl
theorem value222 (q : Snake 81) : valuation q 222 = decide (BallClauseLogic.Endpoint q (325 : Vertex)) := rfl
theorem value223 (q : Snake 81) : valuation q 223 = decide (BallClauseLogic.Endpoint q (330 : Vertex)) := rfl
theorem value224 (q : Snake 81) : valuation q 224 = decide (BallClauseLogic.Endpoint q (332 : Vertex)) := rfl
theorem value225 (q : Snake 81) : valuation q 225 = decide (BallClauseLogic.Endpoint q (333 : Vertex)) := rfl
theorem value226 (q : Snake 81) : valuation q 226 = decide (BallClauseLogic.Endpoint q (334 : Vertex)) := rfl
theorem value227 (q : Snake 81) : valuation q 227 = decide (BallClauseLogic.Endpoint q (336 : Vertex)) := rfl
theorem value228 (q : Snake 81) : valuation q 228 = decide (BallClauseLogic.Endpoint q (337 : Vertex)) := rfl
theorem value229 (q : Snake 81) : valuation q 229 = decide (BallClauseLogic.Endpoint q (342 : Vertex)) := rfl
theorem value230 (q : Snake 81) : valuation q 230 = decide (BallClauseLogic.Endpoint q (343 : Vertex)) := rfl
theorem value231 (q : Snake 81) : valuation q 231 = decide (BallClauseLogic.Endpoint q (345 : Vertex)) := rfl
theorem value232 (q : Snake 81) : valuation q 232 = decide (BallClauseLogic.Endpoint q (347 : Vertex)) := rfl
theorem value233 (q : Snake 81) : valuation q 233 = decide (BallClauseLogic.Endpoint q (348 : Vertex)) := rfl
theorem value234 (q : Snake 81) : valuation q 234 = decide (BallClauseLogic.Endpoint q (350 : Vertex)) := rfl
theorem value235 (q : Snake 81) : valuation q 235 = decide (BallClauseLogic.Endpoint q (351 : Vertex)) := rfl
theorem value236 (q : Snake 81) : valuation q 236 = decide (BallClauseLogic.Endpoint q (384 : Vertex)) := rfl
theorem value237 (q : Snake 81) : valuation q 237 = decide (BallClauseLogic.Endpoint q (385 : Vertex)) := rfl
theorem value238 (q : Snake 81) : valuation q 238 = decide (BallClauseLogic.Endpoint q (386 : Vertex)) := rfl
theorem value239 (q : Snake 81) : valuation q 239 = decide (BallClauseLogic.Endpoint q (389 : Vertex)) := rfl
theorem value240 (q : Snake 81) : valuation q 240 = decide (BallClauseLogic.Endpoint q (394 : Vertex)) := rfl
theorem value241 (q : Snake 81) : valuation q 241 = decide (BallClauseLogic.Endpoint q (396 : Vertex)) := rfl
theorem value242 (q : Snake 81) : valuation q 242 = decide (BallClauseLogic.Endpoint q (397 : Vertex)) := rfl
theorem value243 (q : Snake 81) : valuation q 243 = decide (BallClauseLogic.Endpoint q (398 : Vertex)) := rfl
theorem value244 (q : Snake 81) : valuation q 244 = decide (BallClauseLogic.Endpoint q (400 : Vertex)) := rfl
theorem value245 (q : Snake 81) : valuation q 245 = decide (BallClauseLogic.Endpoint q (401 : Vertex)) := rfl
theorem value246 (q : Snake 81) : valuation q 246 = decide (BallClauseLogic.Endpoint q (403 : Vertex)) := rfl
theorem value247 (q : Snake 81) : valuation q 247 = decide (BallClauseLogic.Endpoint q (406 : Vertex)) := rfl
theorem value248 (q : Snake 81) : valuation q 248 = decide (BallClauseLogic.Endpoint q (407 : Vertex)) := rfl
theorem value249 (q : Snake 81) : valuation q 249 = decide (BallClauseLogic.Endpoint q (409 : Vertex)) := rfl
theorem value250 (q : Snake 81) : valuation q 250 = decide (BallClauseLogic.Endpoint q (411 : Vertex)) := rfl
theorem value251 (q : Snake 81) : valuation q 251 = decide (BallClauseLogic.Endpoint q (412 : Vertex)) := rfl
theorem value252 (q : Snake 81) : valuation q 252 = decide (BallClauseLogic.Endpoint q (414 : Vertex)) := rfl
theorem value253 (q : Snake 81) : valuation q 253 = decide (BallClauseLogic.Endpoint q (415 : Vertex)) := rfl
theorem value255 (q : Snake 81) : valuation q 255 = decide (1 ≤ count255 (baseVal q)) := rfl
theorem value257 (q : Snake 81) : valuation q 257 = decide (1 ≤ count257 (baseVal q)) := rfl
theorem value265 (q : Snake 81) : valuation q 265 = decide (1 ≤ count265 (baseVal q)) := rfl
theorem value267 (q : Snake 81) : valuation q 267 = decide (1 ≤ count267 (baseVal q)) := rfl
theorem value271 (q : Snake 81) : valuation q 271 = decide (1 ≤ count271 (baseVal q)) := rfl
theorem value273 (q : Snake 81) : valuation q 273 = decide (1 ≤ count273 (baseVal q)) := rfl
theorem value275 (q : Snake 81) : valuation q 275 = decide (1 ≤ count275 (baseVal q)) := rfl
theorem value277 (q : Snake 81) : valuation q 277 = decide (1 ≤ count277 (baseVal q)) := rfl
theorem value279 (q : Snake 81) : valuation q 279 = decide (1 ≤ count279 (baseVal q)) := rfl
theorem value281 (q : Snake 81) : valuation q 281 = decide (1 ≤ count281 (baseVal q)) := rfl
theorem value282 (q : Snake 81) : valuation q 282 = decide (2 ≤ count281 (baseVal q)) := rfl
theorem value283 (q : Snake 81) : valuation q 283 = decide (1 ≤ count283 (baseVal q)) := rfl
theorem value285 (q : Snake 81) : valuation q 285 = decide (1 ≤ count285 (baseVal q)) := rfl
theorem value287 (q : Snake 81) : valuation q 287 = decide (1 ≤ count287 (baseVal q)) := rfl
theorem value288 (q : Snake 81) : valuation q 288 = decide (2 ≤ count287 (baseVal q)) := rfl
theorem value289 (q : Snake 81) : valuation q 289 = decide (1 ≤ count289 (baseVal q)) := rfl
theorem value291 (q : Snake 81) : valuation q 291 = decide (1 ≤ count291 (baseVal q)) := rfl
theorem value293 (q : Snake 81) : valuation q 293 = decide (1 ≤ count293 (baseVal q)) := rfl
theorem value295 (q : Snake 81) : valuation q 295 = decide (1 ≤ count295 (baseVal q)) := rfl
theorem value296 (q : Snake 81) : valuation q 296 = decide (2 ≤ count295 (baseVal q)) := rfl
theorem value297 (q : Snake 81) : valuation q 297 = decide (1 ≤ count297 (baseVal q)) := rfl
theorem value299 (q : Snake 81) : valuation q 299 = decide (1 ≤ count299 (baseVal q)) := rfl
theorem value301 (q : Snake 81) : valuation q 301 = decide (1 ≤ count301 (baseVal q)) := rfl
theorem value303 (q : Snake 81) : valuation q 303 = decide (1 ≤ count303 (baseVal q)) := rfl
theorem value305 (q : Snake 81) : valuation q 305 = decide (1 ≤ count305 (baseVal q)) := rfl
theorem value307 (q : Snake 81) : valuation q 307 = decide (1 ≤ count307 (baseVal q)) := rfl
theorem value309 (q : Snake 81) : valuation q 309 = decide (1 ≤ count309 (baseVal q)) := rfl
theorem value311 (q : Snake 81) : valuation q 311 = decide (1 ≤ count311 (baseVal q)) := rfl
theorem value312 (q : Snake 81) : valuation q 312 = decide (2 ≤ count311 (baseVal q)) := rfl
theorem value313 (q : Snake 81) : valuation q 313 = decide (1 ≤ count313 (baseVal q)) := rfl
theorem value314 (q : Snake 81) : valuation q 314 = decide (2 ≤ count313 (baseVal q)) := rfl
theorem value315 (q : Snake 81) : valuation q 315 = decide (1 ≤ count315 (baseVal q)) := rfl
theorem value317 (q : Snake 81) : valuation q 317 = decide (1 ≤ count317 (baseVal q)) := rfl
theorem value319 (q : Snake 81) : valuation q 319 = decide (1 ≤ count319 (baseVal q)) := rfl
theorem value321 (q : Snake 81) : valuation q 321 = decide (1 ≤ count321 (baseVal q)) := rfl
theorem value323 (q : Snake 81) : valuation q 323 = decide (1 ≤ count323 (baseVal q)) := rfl
theorem value325 (q : Snake 81) : valuation q 325 = decide (1 ≤ count325 (baseVal q)) := rfl
theorem value327 (q : Snake 81) : valuation q 327 = decide (1 ≤ count327 (baseVal q)) := rfl
theorem value329 (q : Snake 81) : valuation q 329 = decide (1 ≤ count329 (baseVal q)) := rfl
theorem value333 (q : Snake 81) : valuation q 333 = decide (1 ≤ count333 (baseVal q)) := rfl
theorem value335 (q : Snake 81) : valuation q 335 = decide (1 ≤ count335 (baseVal q)) := rfl
theorem value339 (q : Snake 81) : valuation q 339 = decide (1 ≤ count339 (baseVal q)) := rfl
theorem value341 (q : Snake 81) : valuation q 341 = decide (1 ≤ count341 (baseVal q)) := rfl
theorem value342 (q : Snake 81) : valuation q 342 = decide (2 ≤ count341 (baseVal q)) := rfl
theorem value343 (q : Snake 81) : valuation q 343 = decide (1 ≤ count343 (baseVal q)) := rfl
theorem value344 (q : Snake 81) : valuation q 344 = decide (2 ≤ count343 (baseVal q)) := rfl
theorem value345 (q : Snake 81) : valuation q 345 = decide (1 ≤ count345 (baseVal q)) := rfl
theorem value349 (q : Snake 81) : valuation q 349 = decide (1 ≤ count349 (baseVal q)) := rfl
theorem value351 (q : Snake 81) : valuation q 351 = decide (1 ≤ count351 (baseVal q)) := rfl
theorem value353 (q : Snake 81) : valuation q 353 = decide (1 ≤ count353 (baseVal q)) := rfl
theorem value355 (q : Snake 81) : valuation q 355 = decide (1 ≤ count355 (baseVal q)) := rfl
theorem value357 (q : Snake 81) : valuation q 357 = decide (1 ≤ count357 (baseVal q)) := rfl
theorem value358 (q : Snake 81) : valuation q 358 = decide (2 ≤ count357 (baseVal q)) := rfl
theorem value359 (q : Snake 81) : valuation q 359 = decide (1 ≤ count359 (baseVal q)) := rfl
theorem value361 (q : Snake 81) : valuation q 361 = decide (1 ≤ count361 (baseVal q)) := rfl
theorem value363 (q : Snake 81) : valuation q 363 = decide (1 ≤ count363 (baseVal q)) := rfl
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
theorem value379 (q : Snake 81) : valuation q 379 = decide (1 ≤ count379 (baseVal q)) := rfl
theorem value381 (q : Snake 81) : valuation q 381 = decide (1 ≤ count381 (baseVal q)) := rfl
theorem value383 (q : Snake 81) : valuation q 383 = decide (1 ≤ count383 (baseVal q)) := rfl
theorem value387 (q : Snake 81) : valuation q 387 = decide (1 ≤ count387 (baseVal q)) := rfl
theorem value389 (q : Snake 81) : valuation q 389 = decide (1 ≤ count389 (baseVal q)) := rfl
theorem value390 (q : Snake 81) : valuation q 390 = decide (2 ≤ count389 (baseVal q)) := rfl
theorem value391 (q : Snake 81) : valuation q 391 = decide (1 ≤ count391 (baseVal q)) := rfl
theorem value393 (q : Snake 81) : valuation q 393 = decide (1 ≤ count393 (baseVal q)) := rfl
theorem value395 (q : Snake 81) : valuation q 395 = decide (1 ≤ count395 (baseVal q)) := rfl
theorem value396 (q : Snake 81) : valuation q 396 = decide (2 ≤ count395 (baseVal q)) := rfl
theorem value399 (q : Snake 81) : valuation q 399 = decide (1 ≤ count399 (baseVal q)) := rfl
theorem value401 (q : Snake 81) : valuation q 401 = decide (1 ≤ count401 (baseVal q)) := rfl
theorem value403 (q : Snake 81) : valuation q 403 = decide (1 ≤ count403 (baseVal q)) := rfl
theorem value404 (q : Snake 81) : valuation q 404 = decide (2 ≤ count403 (baseVal q)) := rfl
theorem value405 (q : Snake 81) : valuation q 405 = decide (1 ≤ count405 (baseVal q)) := rfl
theorem value406 (q : Snake 81) : valuation q 406 = decide (2 ≤ count405 (baseVal q)) := rfl
theorem value407 (q : Snake 81) : valuation q 407 = decide (1 ≤ count407 (baseVal q)) := rfl
theorem value409 (q : Snake 81) : valuation q 409 = decide (1 ≤ count409 (baseVal q)) := rfl
theorem value411 (q : Snake 81) : valuation q 411 = decide (1 ≤ count411 (baseVal q)) := rfl
theorem value412 (q : Snake 81) : valuation q 412 = decide (2 ≤ count411 (baseVal q)) := rfl
theorem value413 (q : Snake 81) : valuation q 413 = decide (1 ≤ count413 (baseVal q)) := rfl
theorem value415 (q : Snake 81) : valuation q 415 = decide (1 ≤ count415 (baseVal q)) := rfl
theorem value417 (q : Snake 81) : valuation q 417 = decide (1 ≤ count417 (baseVal q)) := rfl
theorem value419 (q : Snake 81) : valuation q 419 = decide (1 ≤ count419 (baseVal q)) := rfl
theorem value420 (q : Snake 81) : valuation q 420 = decide (2 ≤ count419 (baseVal q)) := rfl
theorem value421 (q : Snake 81) : valuation q 421 = decide (1 ≤ count421 (baseVal q)) := rfl
theorem value425 (q : Snake 81) : valuation q 425 = decide (1 ≤ count425 (baseVal q)) := rfl
theorem value427 (q : Snake 81) : valuation q 427 = decide (1 ≤ count427 (baseVal q)) := rfl
theorem value429 (q : Snake 81) : valuation q 429 = decide (1 ≤ count429 (baseVal q)) := rfl
theorem value431 (q : Snake 81) : valuation q 431 = decide (1 ≤ count431 (baseVal q)) := rfl
theorem value433 (q : Snake 81) : valuation q 433 = decide (1 ≤ count433 (baseVal q)) := rfl
theorem value435 (q : Snake 81) : valuation q 435 = decide (1 ≤ count435 (baseVal q)) := rfl
theorem value436 (q : Snake 81) : valuation q 436 = decide (2 ≤ count435 (baseVal q)) := rfl
theorem value437 (q : Snake 81) : valuation q 437 = decide (1 ≤ count437 (baseVal q)) := rfl
theorem value438 (q : Snake 81) : valuation q 438 = decide (2 ≤ count437 (baseVal q)) := rfl
theorem value441 (q : Snake 81) : valuation q 441 = decide (1 ≤ count441 (baseVal q)) := rfl
theorem value443 (q : Snake 81) : valuation q 443 = decide (1 ≤ count443 (baseVal q)) := rfl
theorem value445 (q : Snake 81) : valuation q 445 = decide (1 ≤ count445 (baseVal q)) := rfl
theorem value447 (q : Snake 81) : valuation q 447 = decide (1 ≤ count447 (baseVal q)) := rfl
theorem value449 (q : Snake 81) : valuation q 449 = decide (1 ≤ count449 (baseVal q)) := rfl
theorem value450 (q : Snake 81) : valuation q 450 = decide (2 ≤ count449 (baseVal q)) := rfl
theorem value451 (q : Snake 81) : valuation q 451 = decide (1 ≤ count451 (baseVal q)) := rfl
theorem value452 (q : Snake 81) : valuation q 452 = decide (2 ≤ count451 (baseVal q)) := rfl
theorem value453 (q : Snake 81) : valuation q 453 = decide (1 ≤ count453 (baseVal q)) := rfl
theorem value455 (q : Snake 81) : valuation q 455 = decide (1 ≤ count455 (baseVal q)) := rfl
theorem value457 (q : Snake 81) : valuation q 457 = decide (1 ≤ count457 (baseVal q)) := rfl
theorem value459 (q : Snake 81) : valuation q 459 = decide (1 ≤ count459 (baseVal q)) := rfl
theorem value461 (q : Snake 81) : valuation q 461 = decide (1 ≤ count461 (baseVal q)) := rfl
theorem value463 (q : Snake 81) : valuation q 463 = decide (1 ≤ count463 (baseVal q)) := rfl
theorem value465 (q : Snake 81) : valuation q 465 = decide (1 ≤ count465 (baseVal q)) := rfl
theorem value466 (q : Snake 81) : valuation q 466 = decide (2 ≤ count465 (baseVal q)) := rfl
theorem value467 (q : Snake 81) : valuation q 467 = decide (1 ≤ count467 (baseVal q)) := rfl
theorem value468 (q : Snake 81) : valuation q 468 = decide (2 ≤ count467 (baseVal q)) := rfl
theorem value469 (q : Snake 81) : valuation q 469 = decide (1 ≤ count469 (baseVal q)) := rfl
theorem value473 (q : Snake 81) : valuation q 473 = decide (1 ≤ count473 (baseVal q)) := rfl
theorem value475 (q : Snake 81) : valuation q 475 = decide (1 ≤ count475 (baseVal q)) := rfl
theorem value476 (q : Snake 81) : valuation q 476 = decide (2 ≤ count475 (baseVal q)) := rfl
theorem value477 (q : Snake 81) : valuation q 477 = decide (1 ≤ count477 (baseVal q)) := rfl
theorem value479 (q : Snake 81) : valuation q 479 = decide (1 ≤ count479 (baseVal q)) := rfl
theorem value480 (q : Snake 81) : valuation q 480 = decide (2 ≤ count479 (baseVal q)) := rfl
theorem value481 (q : Snake 81) : valuation q 481 = decide (1 ≤ count481 (baseVal q)) := rfl
theorem value482 (q : Snake 81) : valuation q 482 = decide (2 ≤ count481 (baseVal q)) := rfl
theorem value483 (q : Snake 81) : valuation q 483 = decide (1 ≤ count483 (baseVal q)) := rfl
theorem value485 (q : Snake 81) : valuation q 485 = decide (1 ≤ count485 (baseVal q)) := rfl
theorem value487 (q : Snake 81) : valuation q 487 = decide (1 ≤ count487 (baseVal q)) := rfl
theorem value489 (q : Snake 81) : valuation q 489 = decide (1 ≤ count489 (baseVal q)) := rfl
theorem value491 (q : Snake 81) : valuation q 491 = decide (1 ≤ count491 (baseVal q)) := rfl
theorem value493 (q : Snake 81) : valuation q 493 = decide (1 ≤ count493 (baseVal q)) := rfl
theorem value495 (q : Snake 81) : valuation q 495 = decide (1 ≤ count495 (baseVal q)) := rfl
theorem value496 (q : Snake 81) : valuation q 496 = decide (2 ≤ count495 (baseVal q)) := rfl
theorem value497 (q : Snake 81) : valuation q 497 = decide (1 ≤ count497 (baseVal q)) := rfl
theorem value498 (q : Snake 81) : valuation q 498 = decide (2 ≤ count497 (baseVal q)) := rfl
theorem value499 (q : Snake 81) : valuation q 499 = decide (1 ≤ count499 (baseVal q)) := rfl
theorem value500 (q : Snake 81) : valuation q 500 = decide (2 ≤ count499 (baseVal q)) := rfl
theorem value501 (q : Snake 81) : valuation q 501 = decide (1 ≤ count501 (baseVal q)) := rfl
theorem value502 (q : Snake 81) : valuation q 502 = decide (2 ≤ count501 (baseVal q)) := rfl
theorem value504 (q : Snake 81) : valuation q 504 = decide (2 ≤ count503 (baseVal q)) := rfl
theorem value867 (q : Snake 81) : valuation q 867 = decide (1 ≤ count867 (baseVal q)) := rfl
theorem value868 (q : Snake 81) : valuation q 868 = decide (2 ≤ count867 (baseVal q)) := rfl
theorem value869 (q : Snake 81) : valuation q 869 = decide (1 ≤ count869 (baseVal q)) := rfl
theorem value870 (q : Snake 81) : valuation q 870 = decide (2 ≤ count869 (baseVal q)) := rfl
theorem value871 (q : Snake 81) : valuation q 871 = decide (1 ≤ count871 (baseVal q)) := rfl
theorem value872 (q : Snake 81) : valuation q 872 = decide (2 ≤ count871 (baseVal q)) := rfl
theorem value873 (q : Snake 81) : valuation q 873 = decide (3 ≤ count871 (baseVal q)) := rfl
theorem value874 (q : Snake 81) : valuation q 874 = decide (4 ≤ count871 (baseVal q)) := rfl
theorem value875 (q : Snake 81) : valuation q 875 = decide (1 ≤ count875 (baseVal q)) := rfl
theorem value876 (q : Snake 81) : valuation q 876 = decide (2 ≤ count875 (baseVal q)) := rfl
theorem value877 (q : Snake 81) : valuation q 877 = decide (1 ≤ count877 (baseVal q)) := rfl
theorem value878 (q : Snake 81) : valuation q 878 = decide (2 ≤ count877 (baseVal q)) := rfl
theorem value879 (q : Snake 81) : valuation q 879 = decide (1 ≤ count879 (baseVal q)) := rfl
theorem value880 (q : Snake 81) : valuation q 880 = decide (2 ≤ count879 (baseVal q)) := rfl
theorem value881 (q : Snake 81) : valuation q 881 = decide (3 ≤ count879 (baseVal q)) := rfl
theorem value882 (q : Snake 81) : valuation q 882 = decide (4 ≤ count879 (baseVal q)) := rfl
theorem value883 (q : Snake 81) : valuation q 883 = decide (1 ≤ count883 (baseVal q)) := rfl
theorem value884 (q : Snake 81) : valuation q 884 = decide (2 ≤ count883 (baseVal q)) := rfl
theorem value885 (q : Snake 81) : valuation q 885 = decide (3 ≤ count883 (baseVal q)) := rfl
theorem value886 (q : Snake 81) : valuation q 886 = decide (4 ≤ count883 (baseVal q)) := rfl
theorem value887 (q : Snake 81) : valuation q 887 = decide (5 ≤ count883 (baseVal q)) := rfl
theorem value888 (q : Snake 81) : valuation q 888 = decide (6 ≤ count883 (baseVal q)) := rfl
theorem value891 (q : Snake 81) : valuation q 891 = decide (1 ≤ count891 (baseVal q)) := rfl
theorem value892 (q : Snake 81) : valuation q 892 = decide (2 ≤ count891 (baseVal q)) := rfl
theorem value893 (q : Snake 81) : valuation q 893 = decide (1 ≤ count893 (baseVal q)) := rfl
theorem value894 (q : Snake 81) : valuation q 894 = decide (2 ≤ count893 (baseVal q)) := rfl
theorem value895 (q : Snake 81) : valuation q 895 = decide (1 ≤ count895 (baseVal q)) := rfl
theorem value896 (q : Snake 81) : valuation q 896 = decide (2 ≤ count895 (baseVal q)) := rfl
theorem value897 (q : Snake 81) : valuation q 897 = decide (3 ≤ count895 (baseVal q)) := rfl
theorem value898 (q : Snake 81) : valuation q 898 = decide (4 ≤ count895 (baseVal q)) := rfl
theorem value899 (q : Snake 81) : valuation q 899 = decide (1 ≤ count899 (baseVal q)) := rfl
theorem value900 (q : Snake 81) : valuation q 900 = decide (2 ≤ count899 (baseVal q)) := rfl
theorem value901 (q : Snake 81) : valuation q 901 = decide (1 ≤ count901 (baseVal q)) := rfl
theorem value902 (q : Snake 81) : valuation q 902 = decide (2 ≤ count901 (baseVal q)) := rfl
theorem value903 (q : Snake 81) : valuation q 903 = decide (1 ≤ count903 (baseVal q)) := rfl
theorem value904 (q : Snake 81) : valuation q 904 = decide (2 ≤ count903 (baseVal q)) := rfl
theorem value905 (q : Snake 81) : valuation q 905 = decide (3 ≤ count903 (baseVal q)) := rfl
theorem value906 (q : Snake 81) : valuation q 906 = decide (4 ≤ count903 (baseVal q)) := rfl
theorem value907 (q : Snake 81) : valuation q 907 = decide (1 ≤ count907 (baseVal q)) := rfl
theorem value908 (q : Snake 81) : valuation q 908 = decide (2 ≤ count907 (baseVal q)) := rfl
theorem value909 (q : Snake 81) : valuation q 909 = decide (3 ≤ count907 (baseVal q)) := rfl
theorem value910 (q : Snake 81) : valuation q 910 = decide (4 ≤ count907 (baseVal q)) := rfl
theorem value911 (q : Snake 81) : valuation q 911 = decide (5 ≤ count907 (baseVal q)) := rfl
theorem value912 (q : Snake 81) : valuation q 912 = decide (6 ≤ count907 (baseVal q)) := rfl
theorem value916 (q : Snake 81) : valuation q 916 = decide (2 ≤ count915 (baseVal q)) := rfl
theorem value917 (q : Snake 81) : valuation q 917 = decide (3 ≤ count915 (baseVal q)) := rfl
theorem value918 (q : Snake 81) : valuation q 918 = decide (4 ≤ count915 (baseVal q)) := rfl
theorem value919 (q : Snake 81) : valuation q 919 = decide (5 ≤ count915 (baseVal q)) := rfl
theorem value920 (q : Snake 81) : valuation q 920 = decide (6 ≤ count915 (baseVal q)) := rfl
theorem value921 (q : Snake 81) : valuation q 921 = decide (7 ≤ count915 (baseVal q)) := rfl
theorem value922 (q : Snake 81) : valuation q 922 = decide (8 ≤ count915 (baseVal q)) := rfl
theorem value923 (q : Snake 81) : valuation q 923 = decide (9 ≤ count915 (baseVal q)) := rfl
theorem value931 (q : Snake 81) : valuation q 931 = decide (1 ≤ count931 (baseVal q)) := rfl
theorem value932 (q : Snake 81) : valuation q 932 = decide (2 ≤ count931 (baseVal q)) := rfl
theorem value933 (q : Snake 81) : valuation q 933 = decide (1 ≤ count933 (baseVal q)) := rfl
theorem value934 (q : Snake 81) : valuation q 934 = decide (2 ≤ count933 (baseVal q)) := rfl
theorem value935 (q : Snake 81) : valuation q 935 = decide (1 ≤ count935 (baseVal q)) := rfl
theorem value936 (q : Snake 81) : valuation q 936 = decide (2 ≤ count935 (baseVal q)) := rfl
theorem value937 (q : Snake 81) : valuation q 937 = decide (3 ≤ count935 (baseVal q)) := rfl
theorem value938 (q : Snake 81) : valuation q 938 = decide (4 ≤ count935 (baseVal q)) := rfl
theorem value939 (q : Snake 81) : valuation q 939 = decide (1 ≤ count939 (baseVal q)) := rfl
theorem value940 (q : Snake 81) : valuation q 940 = decide (2 ≤ count939 (baseVal q)) := rfl
theorem value941 (q : Snake 81) : valuation q 941 = decide (1 ≤ count941 (baseVal q)) := rfl
theorem value942 (q : Snake 81) : valuation q 942 = decide (2 ≤ count941 (baseVal q)) := rfl
theorem value943 (q : Snake 81) : valuation q 943 = decide (1 ≤ count943 (baseVal q)) := rfl
theorem value944 (q : Snake 81) : valuation q 944 = decide (2 ≤ count943 (baseVal q)) := rfl
theorem value945 (q : Snake 81) : valuation q 945 = decide (3 ≤ count943 (baseVal q)) := rfl
theorem value946 (q : Snake 81) : valuation q 946 = decide (4 ≤ count943 (baseVal q)) := rfl
theorem value947 (q : Snake 81) : valuation q 947 = decide (1 ≤ count947 (baseVal q)) := rfl
theorem value948 (q : Snake 81) : valuation q 948 = decide (2 ≤ count947 (baseVal q)) := rfl
theorem value949 (q : Snake 81) : valuation q 949 = decide (3 ≤ count947 (baseVal q)) := rfl
theorem value950 (q : Snake 81) : valuation q 950 = decide (4 ≤ count947 (baseVal q)) := rfl
theorem value951 (q : Snake 81) : valuation q 951 = decide (5 ≤ count947 (baseVal q)) := rfl
theorem value952 (q : Snake 81) : valuation q 952 = decide (6 ≤ count947 (baseVal q)) := rfl
theorem value954 (q : Snake 81) : valuation q 954 = decide (8 ≤ count947 (baseVal q)) := rfl
theorem value955 (q : Snake 81) : valuation q 955 = decide (1 ≤ count955 (baseVal q)) := rfl
theorem value956 (q : Snake 81) : valuation q 956 = decide (2 ≤ count955 (baseVal q)) := rfl
theorem value957 (q : Snake 81) : valuation q 957 = decide (1 ≤ count957 (baseVal q)) := rfl
theorem value958 (q : Snake 81) : valuation q 958 = decide (2 ≤ count957 (baseVal q)) := rfl
theorem value959 (q : Snake 81) : valuation q 959 = decide (1 ≤ count959 (baseVal q)) := rfl
theorem value960 (q : Snake 81) : valuation q 960 = decide (2 ≤ count959 (baseVal q)) := rfl
theorem value961 (q : Snake 81) : valuation q 961 = decide (3 ≤ count959 (baseVal q)) := rfl
theorem value962 (q : Snake 81) : valuation q 962 = decide (4 ≤ count959 (baseVal q)) := rfl
theorem value963 (q : Snake 81) : valuation q 963 = decide (1 ≤ count963 (baseVal q)) := rfl
theorem value964 (q : Snake 81) : valuation q 964 = decide (2 ≤ count963 (baseVal q)) := rfl
theorem value965 (q : Snake 81) : valuation q 965 = decide (1 ≤ count965 (baseVal q)) := rfl
theorem value966 (q : Snake 81) : valuation q 966 = decide (2 ≤ count965 (baseVal q)) := rfl
theorem value967 (q : Snake 81) : valuation q 967 = decide (1 ≤ count967 (baseVal q)) := rfl
theorem value968 (q : Snake 81) : valuation q 968 = decide (2 ≤ count967 (baseVal q)) := rfl
theorem value969 (q : Snake 81) : valuation q 969 = decide (3 ≤ count967 (baseVal q)) := rfl
theorem value970 (q : Snake 81) : valuation q 970 = decide (4 ≤ count967 (baseVal q)) := rfl
theorem value971 (q : Snake 81) : valuation q 971 = decide (1 ≤ count971 (baseVal q)) := rfl
theorem value972 (q : Snake 81) : valuation q 972 = decide (2 ≤ count971 (baseVal q)) := rfl
theorem value973 (q : Snake 81) : valuation q 973 = decide (3 ≤ count971 (baseVal q)) := rfl
theorem value974 (q : Snake 81) : valuation q 974 = decide (4 ≤ count971 (baseVal q)) := rfl
theorem value975 (q : Snake 81) : valuation q 975 = decide (5 ≤ count971 (baseVal q)) := rfl
theorem value976 (q : Snake 81) : valuation q 976 = decide (6 ≤ count971 (baseVal q)) := rfl
theorem value981 (q : Snake 81) : valuation q 981 = decide (3 ≤ count979 (baseVal q)) := rfl
theorem value982 (q : Snake 81) : valuation q 982 = decide (4 ≤ count979 (baseVal q)) := rfl
theorem value983 (q : Snake 81) : valuation q 983 = decide (5 ≤ count979 (baseVal q)) := rfl
theorem value984 (q : Snake 81) : valuation q 984 = decide (6 ≤ count979 (baseVal q)) := rfl
theorem value985 (q : Snake 81) : valuation q 985 = decide (7 ≤ count979 (baseVal q)) := rfl
theorem value986 (q : Snake 81) : valuation q 986 = decide (8 ≤ count979 (baseVal q)) := rfl
theorem value987 (q : Snake 81) : valuation q 987 = decide (9 ≤ count979 (baseVal q)) := rfl
theorem value988 (q : Snake 81) : valuation q 988 = decide (10 ≤ count979 (baseVal q)) := rfl
theorem value990 (q : Snake 81) : valuation q 990 = decide (12 ≤ count979 (baseVal q)) := rfl
theorem value1003 (q : Snake 81) : valuation q 1003 = decide (9 ≤ count995 (baseVal q)) := rfl
theorem value1004 (q : Snake 81) : valuation q 1004 = decide (10 ≤ count995 (baseVal q)) := rfl
theorem value1005 (q : Snake 81) : valuation q 1005 = decide (11 ≤ count995 (baseVal q)) := rfl
theorem value1006 (q : Snake 81) : valuation q 1006 = decide (12 ≤ count995 (baseVal q)) := rfl
theorem value1007 (q : Snake 81) : valuation q 1007 = decide (13 ≤ count995 (baseVal q)) := rfl
theorem value1008 (q : Snake 81) : valuation q 1008 = decide (14 ≤ count995 (baseVal q)) := rfl
theorem value1009 (q : Snake 81) : valuation q 1009 = decide (15 ≤ count995 (baseVal q)) := rfl
theorem value1019 (q : Snake 81) : valuation q 1019 = decide (1 ≤ count1019 (baseVal q)) := rfl
theorem value1020 (q : Snake 81) : valuation q 1020 = decide (2 ≤ count1019 (baseVal q)) := rfl
theorem value1021 (q : Snake 81) : valuation q 1021 = decide (1 ≤ count1021 (baseVal q)) := rfl
theorem value1022 (q : Snake 81) : valuation q 1022 = decide (2 ≤ count1021 (baseVal q)) := rfl
theorem value1024 (q : Snake 81) : valuation q 1024 = decide (2 ≤ count1023 (baseVal q)) := rfl
theorem value1025 (q : Snake 81) : valuation q 1025 = decide (3 ≤ count1023 (baseVal q)) := rfl
theorem value1026 (q : Snake 81) : valuation q 1026 = decide (4 ≤ count1023 (baseVal q)) := rfl
theorem value1027 (q : Snake 81) : valuation q 1027 = decide (1 ≤ count1027 (baseVal q)) := rfl
theorem value1028 (q : Snake 81) : valuation q 1028 = decide (2 ≤ count1027 (baseVal q)) := rfl
theorem value1029 (q : Snake 81) : valuation q 1029 = decide (1 ≤ count1029 (baseVal q)) := rfl
theorem value1030 (q : Snake 81) : valuation q 1030 = decide (2 ≤ count1029 (baseVal q)) := rfl
theorem value1031 (q : Snake 81) : valuation q 1031 = decide (1 ≤ count1031 (baseVal q)) := rfl
theorem value1032 (q : Snake 81) : valuation q 1032 = decide (2 ≤ count1031 (baseVal q)) := rfl
theorem value1033 (q : Snake 81) : valuation q 1033 = decide (3 ≤ count1031 (baseVal q)) := rfl
theorem value1034 (q : Snake 81) : valuation q 1034 = decide (4 ≤ count1031 (baseVal q)) := rfl
theorem value1036 (q : Snake 81) : valuation q 1036 = decide (2 ≤ count1035 (baseVal q)) := rfl
theorem value1037 (q : Snake 81) : valuation q 1037 = decide (3 ≤ count1035 (baseVal q)) := rfl
theorem value1038 (q : Snake 81) : valuation q 1038 = decide (4 ≤ count1035 (baseVal q)) := rfl
theorem value1039 (q : Snake 81) : valuation q 1039 = decide (5 ≤ count1035 (baseVal q)) := rfl
theorem value1040 (q : Snake 81) : valuation q 1040 = decide (6 ≤ count1035 (baseVal q)) := rfl
theorem value1041 (q : Snake 81) : valuation q 1041 = decide (7 ≤ count1035 (baseVal q)) := rfl
theorem value1042 (q : Snake 81) : valuation q 1042 = decide (8 ≤ count1035 (baseVal q)) := rfl
theorem value1043 (q : Snake 81) : valuation q 1043 = decide (1 ≤ count1043 (baseVal q)) := rfl
theorem value1044 (q : Snake 81) : valuation q 1044 = decide (2 ≤ count1043 (baseVal q)) := rfl
theorem value1045 (q : Snake 81) : valuation q 1045 = decide (1 ≤ count1045 (baseVal q)) := rfl
theorem value1046 (q : Snake 81) : valuation q 1046 = decide (2 ≤ count1045 (baseVal q)) := rfl
theorem value1047 (q : Snake 81) : valuation q 1047 = decide (1 ≤ count1047 (baseVal q)) := rfl
theorem value1048 (q : Snake 81) : valuation q 1048 = decide (2 ≤ count1047 (baseVal q)) := rfl
theorem value1049 (q : Snake 81) : valuation q 1049 = decide (3 ≤ count1047 (baseVal q)) := rfl
theorem value1050 (q : Snake 81) : valuation q 1050 = decide (4 ≤ count1047 (baseVal q)) := rfl
theorem value1051 (q : Snake 81) : valuation q 1051 = decide (1 ≤ count1051 (baseVal q)) := rfl
theorem value1052 (q : Snake 81) : valuation q 1052 = decide (2 ≤ count1051 (baseVal q)) := rfl
theorem value1053 (q : Snake 81) : valuation q 1053 = decide (1 ≤ count1053 (baseVal q)) := rfl
theorem value1054 (q : Snake 81) : valuation q 1054 = decide (2 ≤ count1053 (baseVal q)) := rfl
theorem value1055 (q : Snake 81) : valuation q 1055 = decide (1 ≤ count1055 (baseVal q)) := rfl
theorem value1056 (q : Snake 81) : valuation q 1056 = decide (2 ≤ count1055 (baseVal q)) := rfl
theorem value1057 (q : Snake 81) : valuation q 1057 = decide (3 ≤ count1055 (baseVal q)) := rfl
theorem value1058 (q : Snake 81) : valuation q 1058 = decide (4 ≤ count1055 (baseVal q)) := rfl
theorem value1059 (q : Snake 81) : valuation q 1059 = decide (1 ≤ count1059 (baseVal q)) := rfl
theorem value1060 (q : Snake 81) : valuation q 1060 = decide (2 ≤ count1059 (baseVal q)) := rfl
theorem value1061 (q : Snake 81) : valuation q 1061 = decide (3 ≤ count1059 (baseVal q)) := rfl
theorem value1062 (q : Snake 81) : valuation q 1062 = decide (4 ≤ count1059 (baseVal q)) := rfl
theorem value1063 (q : Snake 81) : valuation q 1063 = decide (5 ≤ count1059 (baseVal q)) := rfl
theorem value1064 (q : Snake 81) : valuation q 1064 = decide (6 ≤ count1059 (baseVal q)) := rfl
theorem value1065 (q : Snake 81) : valuation q 1065 = decide (7 ≤ count1059 (baseVal q)) := rfl
theorem value1066 (q : Snake 81) : valuation q 1066 = decide (8 ≤ count1059 (baseVal q)) := rfl
theorem value1071 (q : Snake 81) : valuation q 1071 = decide (5 ≤ count1067 (baseVal q)) := rfl
theorem value1072 (q : Snake 81) : valuation q 1072 = decide (6 ≤ count1067 (baseVal q)) := rfl
theorem value1073 (q : Snake 81) : valuation q 1073 = decide (7 ≤ count1067 (baseVal q)) := rfl
theorem value1074 (q : Snake 81) : valuation q 1074 = decide (8 ≤ count1067 (baseVal q)) := rfl
theorem value1075 (q : Snake 81) : valuation q 1075 = decide (9 ≤ count1067 (baseVal q)) := rfl
theorem value1076 (q : Snake 81) : valuation q 1076 = decide (10 ≤ count1067 (baseVal q)) := rfl
theorem value1077 (q : Snake 81) : valuation q 1077 = decide (11 ≤ count1067 (baseVal q)) := rfl
theorem value1078 (q : Snake 81) : valuation q 1078 = decide (12 ≤ count1067 (baseVal q)) := rfl
theorem value1079 (q : Snake 81) : valuation q 1079 = decide (13 ≤ count1067 (baseVal q)) := rfl
theorem value1083 (q : Snake 81) : valuation q 1083 = decide (1 ≤ count1083 (baseVal q)) := rfl
theorem value1084 (q : Snake 81) : valuation q 1084 = decide (2 ≤ count1083 (baseVal q)) := rfl
theorem value1085 (q : Snake 81) : valuation q 1085 = decide (1 ≤ count1085 (baseVal q)) := rfl
theorem value1086 (q : Snake 81) : valuation q 1086 = decide (2 ≤ count1085 (baseVal q)) := rfl
theorem value1087 (q : Snake 81) : valuation q 1087 = decide (1 ≤ count1087 (baseVal q)) := rfl
theorem value1088 (q : Snake 81) : valuation q 1088 = decide (2 ≤ count1087 (baseVal q)) := rfl
theorem value1089 (q : Snake 81) : valuation q 1089 = decide (3 ≤ count1087 (baseVal q)) := rfl
theorem value1090 (q : Snake 81) : valuation q 1090 = decide (4 ≤ count1087 (baseVal q)) := rfl
theorem value1091 (q : Snake 81) : valuation q 1091 = decide (1 ≤ count1091 (baseVal q)) := rfl
theorem value1092 (q : Snake 81) : valuation q 1092 = decide (2 ≤ count1091 (baseVal q)) := rfl
theorem value1093 (q : Snake 81) : valuation q 1093 = decide (1 ≤ count1093 (baseVal q)) := rfl
theorem value1094 (q : Snake 81) : valuation q 1094 = decide (2 ≤ count1093 (baseVal q)) := rfl
theorem value1095 (q : Snake 81) : valuation q 1095 = decide (1 ≤ count1095 (baseVal q)) := rfl
theorem value1096 (q : Snake 81) : valuation q 1096 = decide (2 ≤ count1095 (baseVal q)) := rfl
theorem value1097 (q : Snake 81) : valuation q 1097 = decide (3 ≤ count1095 (baseVal q)) := rfl
theorem value1098 (q : Snake 81) : valuation q 1098 = decide (4 ≤ count1095 (baseVal q)) := rfl
theorem value1099 (q : Snake 81) : valuation q 1099 = decide (1 ≤ count1099 (baseVal q)) := rfl
theorem value1100 (q : Snake 81) : valuation q 1100 = decide (2 ≤ count1099 (baseVal q)) := rfl
theorem value1101 (q : Snake 81) : valuation q 1101 = decide (3 ≤ count1099 (baseVal q)) := rfl
theorem value1102 (q : Snake 81) : valuation q 1102 = decide (4 ≤ count1099 (baseVal q)) := rfl
theorem value1103 (q : Snake 81) : valuation q 1103 = decide (5 ≤ count1099 (baseVal q)) := rfl
theorem value1104 (q : Snake 81) : valuation q 1104 = decide (6 ≤ count1099 (baseVal q)) := rfl
theorem value1107 (q : Snake 81) : valuation q 1107 = decide (1 ≤ count1107 (baseVal q)) := rfl
theorem value1108 (q : Snake 81) : valuation q 1108 = decide (2 ≤ count1107 (baseVal q)) := rfl
theorem value1109 (q : Snake 81) : valuation q 1109 = decide (1 ≤ count1109 (baseVal q)) := rfl
theorem value1110 (q : Snake 81) : valuation q 1110 = decide (2 ≤ count1109 (baseVal q)) := rfl
theorem value1111 (q : Snake 81) : valuation q 1111 = decide (1 ≤ count1111 (baseVal q)) := rfl
theorem value1112 (q : Snake 81) : valuation q 1112 = decide (2 ≤ count1111 (baseVal q)) := rfl
theorem value1113 (q : Snake 81) : valuation q 1113 = decide (3 ≤ count1111 (baseVal q)) := rfl
theorem value1114 (q : Snake 81) : valuation q 1114 = decide (4 ≤ count1111 (baseVal q)) := rfl
theorem value1115 (q : Snake 81) : valuation q 1115 = decide (1 ≤ count1115 (baseVal q)) := rfl
theorem value1116 (q : Snake 81) : valuation q 1116 = decide (2 ≤ count1115 (baseVal q)) := rfl
theorem value1117 (q : Snake 81) : valuation q 1117 = decide (1 ≤ count1117 (baseVal q)) := rfl
theorem value1119 (q : Snake 81) : valuation q 1119 = decide (1 ≤ count1119 (baseVal q)) := rfl
theorem value1120 (q : Snake 81) : valuation q 1120 = decide (2 ≤ count1119 (baseVal q)) := rfl
theorem value1121 (q : Snake 81) : valuation q 1121 = decide (3 ≤ count1119 (baseVal q)) := rfl
theorem value1123 (q : Snake 81) : valuation q 1123 = decide (1 ≤ count1123 (baseVal q)) := rfl
theorem value1124 (q : Snake 81) : valuation q 1124 = decide (2 ≤ count1123 (baseVal q)) := rfl
theorem value1125 (q : Snake 81) : valuation q 1125 = decide (3 ≤ count1123 (baseVal q)) := rfl
theorem value1126 (q : Snake 81) : valuation q 1126 = decide (4 ≤ count1123 (baseVal q)) := rfl
theorem value1131 (q : Snake 81) : valuation q 1131 = decide (1 ≤ count1131 (baseVal q)) := rfl
theorem value1132 (q : Snake 81) : valuation q 1132 = decide (2 ≤ count1131 (baseVal q)) := rfl
theorem value1133 (q : Snake 81) : valuation q 1133 = decide (3 ≤ count1131 (baseVal q)) := rfl
theorem value1134 (q : Snake 81) : valuation q 1134 = decide (4 ≤ count1131 (baseVal q)) := rfl
theorem value1135 (q : Snake 81) : valuation q 1135 = decide (5 ≤ count1131 (baseVal q)) := rfl
theorem value1136 (q : Snake 81) : valuation q 1136 = decide (6 ≤ count1131 (baseVal q)) := rfl
theorem value1137 (q : Snake 81) : valuation q 1137 = decide (7 ≤ count1131 (baseVal q)) := rfl
theorem value1138 (q : Snake 81) : valuation q 1138 = decide (8 ≤ count1131 (baseVal q)) := rfl
theorem value1139 (q : Snake 81) : valuation q 1139 = decide (9 ≤ count1131 (baseVal q)) := rfl
theorem value1155 (q : Snake 81) : valuation q 1155 = decide (9 ≤ count1147 (baseVal q)) := rfl
theorem value1156 (q : Snake 81) : valuation q 1156 = decide (10 ≤ count1147 (baseVal q)) := rfl
theorem value1157 (q : Snake 81) : valuation q 1157 = decide (11 ≤ count1147 (baseVal q)) := rfl
theorem value1158 (q : Snake 81) : valuation q 1158 = decide (12 ≤ count1147 (baseVal q)) := rfl
theorem value1159 (q : Snake 81) : valuation q 1159 = decide (13 ≤ count1147 (baseVal q)) := rfl
theorem value1160 (q : Snake 81) : valuation q 1160 = decide (14 ≤ count1147 (baseVal q)) := rfl
theorem value1161 (q : Snake 81) : valuation q 1161 = decide (15 ≤ count1147 (baseVal q)) := rfl
theorem value1194 (q : Snake 81) : valuation q 1194 = decide (24 ≤ count1171 (baseVal q)) := rfl
theorem value1551 (q : Snake 81) : valuation q 1551 = decide (1 ≤ count1551 (baseVal q)) := rfl
theorem value1553 (q : Snake 81) : valuation q 1553 = decide (1 ≤ count1553 (baseVal q)) := rfl
theorem value1556 (q : Snake 81) : valuation q 1556 = decide (1 ≤ count1556 (baseVal q)) := rfl
theorem value1558 (q : Snake 81) : valuation q 1558 = decide (1 ≤ count1558 (baseVal q)) := rfl
theorem value1559 (q : Snake 81) : valuation q 1559 = decide (2 ≤ count1558 (baseVal q)) := rfl
theorem value1560 (q : Snake 81) : valuation q 1560 = decide (1 ≤ count1560 (baseVal q)) := rfl
theorem value1561 (q : Snake 81) : valuation q 1561 = decide (2 ≤ count1560 (baseVal q)) := rfl
theorem value1564 (q : Snake 81) : valuation q 1564 = decide (1 ≤ count1564 (baseVal q)) := rfl
theorem value1565 (q : Snake 81) : valuation q 1565 = decide (2 ≤ count1564 (baseVal q)) := rfl
theorem value1571 (q : Snake 81) : valuation q 1571 = decide (1 ≤ count1571 (baseVal q)) := rfl
theorem value1573 (q : Snake 81) : valuation q 1573 = decide (1 ≤ count1573 (baseVal q)) := rfl
theorem value1576 (q : Snake 81) : valuation q 1576 = decide (2 ≤ count1575 (baseVal q)) := rfl
theorem value1579 (q : Snake 81) : valuation q 1579 = decide (1 ≤ count1579 (baseVal q)) := rfl
theorem value1581 (q : Snake 81) : valuation q 1581 = decide (1 ≤ count1581 (baseVal q)) := rfl
theorem value1583 (q : Snake 81) : valuation q 1583 = decide (1 ≤ count1583 (baseVal q)) := rfl
theorem value1584 (q : Snake 81) : valuation q 1584 = decide (2 ≤ count1583 (baseVal q)) := rfl
theorem value1589 (q : Snake 81) : valuation q 1589 = decide (3 ≤ count1587 (baseVal q)) := rfl
theorem value1590 (q : Snake 81) : valuation q 1590 = decide (4 ≤ count1587 (baseVal q)) := rfl
theorem value1598 (q : Snake 81) : valuation q 1598 = decide (4 ≤ count1595 (baseVal q)) := rfl
theorem value1599 (q : Snake 81) : valuation q 1599 = decide (5 ≤ count1595 (baseVal q)) := rfl
theorem value1600 (q : Snake 81) : valuation q 1600 = decide (6 ≤ count1595 (baseVal q)) := rfl
theorem value1610 (q : Snake 81) : valuation q 1610 = decide (1 ≤ count1610 (baseVal q)) := rfl
theorem value1612 (q : Snake 81) : valuation q 1612 = decide (1 ≤ count1612 (baseVal q)) := rfl
theorem value1614 (q : Snake 81) : valuation q 1614 = decide (1 ≤ count1614 (baseVal q)) := rfl
theorem value1618 (q : Snake 81) : valuation q 1618 = decide (1 ≤ count1618 (baseVal q)) := rfl
theorem value1620 (q : Snake 81) : valuation q 1620 = decide (1 ≤ count1620 (baseVal q)) := rfl
theorem value1621 (q : Snake 81) : valuation q 1621 = decide (2 ≤ count1620 (baseVal q)) := rfl
theorem value1622 (q : Snake 81) : valuation q 1622 = decide (1 ≤ count1622 (baseVal q)) := rfl
theorem value1623 (q : Snake 81) : valuation q 1623 = decide (2 ≤ count1622 (baseVal q)) := rfl
theorem value1627 (q : Snake 81) : valuation q 1627 = decide (2 ≤ count1626 (baseVal q)) := rfl
theorem value1628 (q : Snake 81) : valuation q 1628 = decide (3 ≤ count1626 (baseVal q)) := rfl
theorem value1634 (q : Snake 81) : valuation q 1634 = decide (1 ≤ count1634 (baseVal q)) := rfl
theorem value1635 (q : Snake 81) : valuation q 1635 = decide (2 ≤ count1634 (baseVal q)) := rfl
theorem value1636 (q : Snake 81) : valuation q 1636 = decide (1 ≤ count1636 (baseVal q)) := rfl
theorem value1638 (q : Snake 81) : valuation q 1638 = decide (1 ≤ count1638 (baseVal q)) := rfl
theorem value1639 (q : Snake 81) : valuation q 1639 = decide (2 ≤ count1638 (baseVal q)) := rfl
theorem value1642 (q : Snake 81) : valuation q 1642 = decide (1 ≤ count1642 (baseVal q)) := rfl
theorem value1643 (q : Snake 81) : valuation q 1643 = decide (2 ≤ count1642 (baseVal q)) := rfl
theorem value1644 (q : Snake 81) : valuation q 1644 = decide (1 ≤ count1644 (baseVal q)) := rfl
theorem value1646 (q : Snake 81) : valuation q 1646 = decide (1 ≤ count1646 (baseVal q)) := rfl
theorem value1647 (q : Snake 81) : valuation q 1647 = decide (2 ≤ count1646 (baseVal q)) := rfl
theorem value1648 (q : Snake 81) : valuation q 1648 = decide (3 ≤ count1646 (baseVal q)) := rfl
theorem value1651 (q : Snake 81) : valuation q 1651 = decide (2 ≤ count1650 (baseVal q)) := rfl
theorem value1652 (q : Snake 81) : valuation q 1652 = decide (3 ≤ count1650 (baseVal q)) := rfl
theorem value1661 (q : Snake 81) : valuation q 1661 = decide (4 ≤ count1658 (baseVal q)) := rfl
theorem value1662 (q : Snake 81) : valuation q 1662 = decide (5 ≤ count1658 (baseVal q)) := rfl
theorem value1682 (q : Snake 81) : valuation q 1682 = decide (9 ≤ count1674 (baseVal q)) := rfl
theorem value1683 (q : Snake 81) : valuation q 1683 = decide (10 ≤ count1674 (baseVal q)) := rfl
theorem value1697 (q : Snake 81) : valuation q 1697 = decide (1 ≤ count1697 (baseVal q)) := rfl
theorem value1699 (q : Snake 81) : valuation q 1699 = decide (1 ≤ count1699 (baseVal q)) := rfl
theorem value1701 (q : Snake 81) : valuation q 1701 = decide (1 ≤ count1701 (baseVal q)) := rfl
theorem value1702 (q : Snake 81) : valuation q 1702 = decide (2 ≤ count1701 (baseVal q)) := rfl
theorem value1705 (q : Snake 81) : valuation q 1705 = decide (1 ≤ count1705 (baseVal q)) := rfl
theorem value1707 (q : Snake 81) : valuation q 1707 = decide (1 ≤ count1707 (baseVal q)) := rfl
theorem value1710 (q : Snake 81) : valuation q 1710 = decide (2 ≤ count1709 (baseVal q)) := rfl
theorem value1715 (q : Snake 81) : valuation q 1715 = decide (3 ≤ count1713 (baseVal q)) := rfl
theorem value1716 (q : Snake 81) : valuation q 1716 = decide (4 ≤ count1713 (baseVal q)) := rfl
theorem value1721 (q : Snake 81) : valuation q 1721 = decide (1 ≤ count1721 (baseVal q)) := rfl
theorem value1722 (q : Snake 81) : valuation q 1722 = decide (2 ≤ count1721 (baseVal q)) := rfl
theorem value1723 (q : Snake 81) : valuation q 1723 = decide (1 ≤ count1723 (baseVal q)) := rfl
theorem value1724 (q : Snake 81) : valuation q 1724 = decide (2 ≤ count1723 (baseVal q)) := rfl
theorem value1727 (q : Snake 81) : valuation q 1727 = decide (3 ≤ count1725 (baseVal q)) := rfl
theorem value1730 (q : Snake 81) : valuation q 1730 = decide (2 ≤ count1729 (baseVal q)) := rfl
theorem value1734 (q : Snake 81) : valuation q 1734 = decide (2 ≤ count1733 (baseVal q)) := rfl
theorem value1741 (q : Snake 81) : valuation q 1741 = decide (5 ≤ count1737 (baseVal q)) := rfl
theorem value1752 (q : Snake 81) : valuation q 1752 = decide (8 ≤ count1745 (baseVal q)) := rfl
theorem value1753 (q : Snake 81) : valuation q 1753 = decide (9 ≤ count1745 (baseVal q)) := rfl
theorem value1763 (q : Snake 81) : valuation q 1763 = decide (1 ≤ count1763 (baseVal q)) := rfl
theorem value1765 (q : Snake 81) : valuation q 1765 = decide (1 ≤ count1765 (baseVal q)) := rfl
theorem value1769 (q : Snake 81) : valuation q 1769 = decide (1 ≤ count1769 (baseVal q)) := rfl
theorem value1771 (q : Snake 81) : valuation q 1771 = decide (1 ≤ count1771 (baseVal q)) := rfl
theorem value1774 (q : Snake 81) : valuation q 1774 = decide (2 ≤ count1773 (baseVal q)) := rfl
theorem value1777 (q : Snake 81) : valuation q 1777 = decide (1 ≤ count1777 (baseVal q)) := rfl
theorem value1778 (q : Snake 81) : valuation q 1778 = decide (2 ≤ count1777 (baseVal q)) := rfl
theorem value1786 (q : Snake 81) : valuation q 1786 = decide (2 ≤ count1785 (baseVal q)) := rfl
theorem value1787 (q : Snake 81) : valuation q 1787 = decide (1 ≤ count1787 (baseVal q)) := rfl
theorem value1789 (q : Snake 81) : valuation q 1789 = decide (1 ≤ count1789 (baseVal q)) := rfl
theorem value1791 (q : Snake 81) : valuation q 1791 = decide (3 ≤ count1789 (baseVal q)) := rfl
theorem value1793 (q : Snake 81) : valuation q 1793 = decide (1 ≤ count1793 (baseVal q)) := rfl
theorem value1795 (q : Snake 81) : valuation q 1795 = decide (1 ≤ count1795 (baseVal q)) := rfl
theorem value1797 (q : Snake 81) : valuation q 1797 = decide (1 ≤ count1797 (baseVal q)) := rfl
theorem value1798 (q : Snake 81) : valuation q 1798 = decide (2 ≤ count1797 (baseVal q)) := rfl
theorem value1802 (q : Snake 81) : valuation q 1802 = decide (2 ≤ count1801 (baseVal q)) := rfl
theorem value1805 (q : Snake 81) : valuation q 1805 = decide (5 ≤ count1801 (baseVal q)) := rfl
theorem value1812 (q : Snake 81) : valuation q 1812 = decide (4 ≤ count1809 (baseVal q)) := rfl
theorem value1814 (q : Snake 81) : valuation q 1814 = decide (6 ≤ count1809 (baseVal q)) := rfl
theorem value1837 (q : Snake 81) : valuation q 1837 = decide (13 ≤ count1825 (baseVal q)) := rfl
theorem value1838 (q : Snake 81) : valuation q 1838 = decide (14 ≤ count1825 (baseVal q)) := rfl
theorem value1870 (q : Snake 81) : valuation q 1870 = decide (23 ≤ count1848 (baseVal q)) := rfl
theorem meaningNeg126 (b : Nat → Bool) : literal (valuationOf b) (-126) = decide (1 ≤ countLit b [-126]) := by
  change literal b (-126) = decide (1 ≤ countLit b [-126])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-126) <;> decide
theorem meaningNeg125 (b : Nat → Bool) : literal (valuationOf b) (-125) = decide (1 ≤ countLit b [-125]) := by
  change literal b (-125) = decide (1 ≤ countLit b [-125])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-125) <;> decide
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
theorem meaningNeg89 (b : Nat → Bool) : literal (valuationOf b) (-89) = decide (1 ≤ countLit b [-89]) := by
  change literal b (-89) = decide (1 ≤ countLit b [-89])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-89) <;> decide
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
theorem meaningNeg65 (b : Nat → Bool) : literal (valuationOf b) (-65) = decide (1 ≤ countLit b [-65]) := by
  change literal b (-65) = decide (1 ≤ countLit b [-65])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-65) <;> decide
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
theorem meaningNeg48 (b : Nat → Bool) : literal (valuationOf b) (-48) = decide (1 ≤ countLit b [-48]) := by
  change literal b (-48) = decide (1 ≤ countLit b [-48])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-48) <;> decide
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
theorem meaningNeg42 (b : Nat → Bool) : literal (valuationOf b) (-42) = decide (1 ≤ countLit b [-42]) := by
  change literal b (-42) = decide (1 ≤ countLit b [-42])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-42) <;> decide
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
theorem meaningNeg34 (b : Nat → Bool) : literal (valuationOf b) (-34) = decide (1 ≤ countLit b [-34]) := by
  change literal b (-34) = decide (1 ≤ countLit b [-34])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-34) <;> decide
theorem meaningNeg33 (b : Nat → Bool) : literal (valuationOf b) (-33) = decide (1 ≤ countLit b [-33]) := by
  change literal b (-33) = decide (1 ≤ countLit b [-33])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-33) <;> decide
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
theorem meaningNeg17 (b : Nat → Bool) : literal (valuationOf b) (-17) = decide (1 ≤ countLit b [-17]) := by
  change literal b (-17) = decide (1 ≤ countLit b [-17])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (-17) <;> decide
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
theorem meaning129 (b : Nat → Bool) : literal (valuationOf b) (129) = decide (1 ≤ countLit b [129]) := by
  change literal b (129) = decide (1 ≤ countLit b [129])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (129) <;> decide
theorem meaning130 (b : Nat → Bool) : literal (valuationOf b) (130) = decide (1 ≤ countLit b [130]) := by
  change literal b (130) = decide (1 ≤ countLit b [130])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (130) <;> decide
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
theorem meaning140 (b : Nat → Bool) : literal (valuationOf b) (140) = decide (1 ≤ countLit b [140]) := by
  change literal b (140) = decide (1 ≤ countLit b [140])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (140) <;> decide
theorem meaning141 (b : Nat → Bool) : literal (valuationOf b) (141) = decide (1 ≤ countLit b [141]) := by
  change literal b (141) = decide (1 ≤ countLit b [141])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (141) <;> decide
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
theorem meaning147 (b : Nat → Bool) : literal (valuationOf b) (147) = decide (1 ≤ countLit b [147]) := by
  change literal b (147) = decide (1 ≤ countLit b [147])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (147) <;> decide
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
theorem meaning161 (b : Nat → Bool) : literal (valuationOf b) (161) = decide (1 ≤ countLit b [161]) := by
  change literal b (161) = decide (1 ≤ countLit b [161])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (161) <;> decide
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
theorem meaning172 (b : Nat → Bool) : literal (valuationOf b) (172) = decide (1 ≤ countLit b [172]) := by
  change literal b (172) = decide (1 ≤ countLit b [172])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (172) <;> decide
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
theorem meaning180 (b : Nat → Bool) : literal (valuationOf b) (180) = decide (1 ≤ countLit b [180]) := by
  change literal b (180) = decide (1 ≤ countLit b [180])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (180) <;> decide
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
theorem meaning189 (b : Nat → Bool) : literal (valuationOf b) (189) = decide (1 ≤ countLit b [189]) := by
  change literal b (189) = decide (1 ≤ countLit b [189])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (189) <;> decide
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
theorem meaning195 (b : Nat → Bool) : literal (valuationOf b) (195) = decide (1 ≤ countLit b [195]) := by
  change literal b (195) = decide (1 ≤ countLit b [195])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (195) <;> decide
theorem meaning198 (b : Nat → Bool) : literal (valuationOf b) (198) = decide (1 ≤ countLit b [198]) := by
  change literal b (198) = decide (1 ≤ countLit b [198])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (198) <;> decide
theorem meaning201 (b : Nat → Bool) : literal (valuationOf b) (201) = decide (1 ≤ countLit b [201]) := by
  change literal b (201) = decide (1 ≤ countLit b [201])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (201) <;> decide
theorem meaning205 (b : Nat → Bool) : literal (valuationOf b) (205) = decide (1 ≤ countLit b [205]) := by
  change literal b (205) = decide (1 ≤ countLit b [205])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (205) <;> decide
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
theorem meaning215 (b : Nat → Bool) : literal (valuationOf b) (215) = decide (1 ≤ countLit b [215]) := by
  change literal b (215) = decide (1 ≤ countLit b [215])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (215) <;> decide
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
theorem meaning225 (b : Nat → Bool) : literal (valuationOf b) (225) = decide (1 ≤ countLit b [225]) := by
  change literal b (225) = decide (1 ≤ countLit b [225])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (225) <;> decide
theorem meaning226 (b : Nat → Bool) : literal (valuationOf b) (226) = decide (1 ≤ countLit b [226]) := by
  change literal b (226) = decide (1 ≤ countLit b [226])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (226) <;> decide
theorem meaning227 (b : Nat → Bool) : literal (valuationOf b) (227) = decide (1 ≤ countLit b [227]) := by
  change literal b (227) = decide (1 ≤ countLit b [227])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (227) <;> decide
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
theorem meaning233 (b : Nat → Bool) : literal (valuationOf b) (233) = decide (1 ≤ countLit b [233]) := by
  change literal b (233) = decide (1 ≤ countLit b [233])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (233) <;> decide
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
theorem meaning242 (b : Nat → Bool) : literal (valuationOf b) (242) = decide (1 ≤ countLit b [242]) := by
  change literal b (242) = decide (1 ≤ countLit b [242])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (242) <;> decide
theorem meaning243 (b : Nat → Bool) : literal (valuationOf b) (243) = decide (1 ≤ countLit b [243]) := by
  change literal b (243) = decide (1 ≤ countLit b [243])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (243) <;> decide
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
theorem meaning247 (b : Nat → Bool) : literal (valuationOf b) (247) = decide (1 ≤ countLit b [247]) := by
  change literal b (247) = decide (1 ≤ countLit b [247])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (247) <;> decide
theorem meaning249 (b : Nat → Bool) : literal (valuationOf b) (249) = decide (1 ≤ countLit b [249]) := by
  change literal b (249) = decide (1 ≤ countLit b [249])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (249) <;> decide
theorem meaning251 (b : Nat → Bool) : literal (valuationOf b) (251) = decide (1 ≤ countLit b [251]) := by
  change literal b (251) = decide (1 ≤ countLit b [251])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (251) <;> decide
theorem meaning253 (b : Nat → Bool) : literal (valuationOf b) (253) = decide (1 ≤ countLit b [253]) := by
  change literal b (253) = decide (1 ≤ countLit b [253])
  unfold countLit
  simp only [List.countP_cons, List.countP_nil]
  cases literal b (253) <;> decide
theorem meaning255 (b : Nat → Bool) : literal (valuationOf b) 255 = decide (1 ≤ count255 b) := rfl
theorem meaning257 (b : Nat → Bool) : literal (valuationOf b) 257 = decide (1 ≤ count257 b) := rfl
theorem meaning265 (b : Nat → Bool) : literal (valuationOf b) 265 = decide (1 ≤ count265 b) := rfl
theorem meaning267 (b : Nat → Bool) : literal (valuationOf b) 267 = decide (1 ≤ count267 b) := rfl
theorem meaning271 (b : Nat → Bool) : literal (valuationOf b) 271 = decide (1 ≤ count271 b) := rfl
theorem meaning273 (b : Nat → Bool) : literal (valuationOf b) 273 = decide (1 ≤ count273 b) := rfl
theorem meaning275 (b : Nat → Bool) : literal (valuationOf b) 275 = decide (1 ≤ count275 b) := rfl
theorem meaning277 (b : Nat → Bool) : literal (valuationOf b) 277 = decide (1 ≤ count277 b) := rfl
theorem meaning279 (b : Nat → Bool) : literal (valuationOf b) 279 = decide (1 ≤ count279 b) := rfl
theorem meaning281 (b : Nat → Bool) : literal (valuationOf b) 281 = decide (1 ≤ count281 b) := rfl
theorem meaning282 (b : Nat → Bool) : literal (valuationOf b) 282 = decide (2 ≤ count281 b) := rfl
theorem meaning283 (b : Nat → Bool) : literal (valuationOf b) 283 = decide (1 ≤ count283 b) := rfl
theorem meaning285 (b : Nat → Bool) : literal (valuationOf b) 285 = decide (1 ≤ count285 b) := rfl
theorem meaning287 (b : Nat → Bool) : literal (valuationOf b) 287 = decide (1 ≤ count287 b) := rfl
theorem meaning288 (b : Nat → Bool) : literal (valuationOf b) 288 = decide (2 ≤ count287 b) := rfl
theorem meaning289 (b : Nat → Bool) : literal (valuationOf b) 289 = decide (1 ≤ count289 b) := rfl
theorem meaning291 (b : Nat → Bool) : literal (valuationOf b) 291 = decide (1 ≤ count291 b) := rfl
theorem meaning293 (b : Nat → Bool) : literal (valuationOf b) 293 = decide (1 ≤ count293 b) := rfl
theorem meaning295 (b : Nat → Bool) : literal (valuationOf b) 295 = decide (1 ≤ count295 b) := rfl
theorem meaning296 (b : Nat → Bool) : literal (valuationOf b) 296 = decide (2 ≤ count295 b) := rfl
theorem meaning297 (b : Nat → Bool) : literal (valuationOf b) 297 = decide (1 ≤ count297 b) := rfl
theorem meaning299 (b : Nat → Bool) : literal (valuationOf b) 299 = decide (1 ≤ count299 b) := rfl
theorem meaning301 (b : Nat → Bool) : literal (valuationOf b) 301 = decide (1 ≤ count301 b) := rfl
theorem meaning303 (b : Nat → Bool) : literal (valuationOf b) 303 = decide (1 ≤ count303 b) := rfl
theorem meaning305 (b : Nat → Bool) : literal (valuationOf b) 305 = decide (1 ≤ count305 b) := rfl
theorem meaning307 (b : Nat → Bool) : literal (valuationOf b) 307 = decide (1 ≤ count307 b) := rfl
theorem meaning309 (b : Nat → Bool) : literal (valuationOf b) 309 = decide (1 ≤ count309 b) := rfl
theorem meaning311 (b : Nat → Bool) : literal (valuationOf b) 311 = decide (1 ≤ count311 b) := rfl
theorem meaning312 (b : Nat → Bool) : literal (valuationOf b) 312 = decide (2 ≤ count311 b) := rfl
theorem meaning313 (b : Nat → Bool) : literal (valuationOf b) 313 = decide (1 ≤ count313 b) := rfl
theorem meaning314 (b : Nat → Bool) : literal (valuationOf b) 314 = decide (2 ≤ count313 b) := rfl
theorem meaning315 (b : Nat → Bool) : literal (valuationOf b) 315 = decide (1 ≤ count315 b) := rfl
theorem meaning317 (b : Nat → Bool) : literal (valuationOf b) 317 = decide (1 ≤ count317 b) := rfl
theorem meaning319 (b : Nat → Bool) : literal (valuationOf b) 319 = decide (1 ≤ count319 b) := rfl
theorem meaning321 (b : Nat → Bool) : literal (valuationOf b) 321 = decide (1 ≤ count321 b) := rfl
theorem meaning323 (b : Nat → Bool) : literal (valuationOf b) 323 = decide (1 ≤ count323 b) := rfl
theorem meaning325 (b : Nat → Bool) : literal (valuationOf b) 325 = decide (1 ≤ count325 b) := rfl
theorem meaning327 (b : Nat → Bool) : literal (valuationOf b) 327 = decide (1 ≤ count327 b) := rfl
theorem meaning329 (b : Nat → Bool) : literal (valuationOf b) 329 = decide (1 ≤ count329 b) := rfl
theorem meaning333 (b : Nat → Bool) : literal (valuationOf b) 333 = decide (1 ≤ count333 b) := rfl
theorem meaning335 (b : Nat → Bool) : literal (valuationOf b) 335 = decide (1 ≤ count335 b) := rfl
theorem meaning339 (b : Nat → Bool) : literal (valuationOf b) 339 = decide (1 ≤ count339 b) := rfl
theorem meaning341 (b : Nat → Bool) : literal (valuationOf b) 341 = decide (1 ≤ count341 b) := rfl
theorem meaning342 (b : Nat → Bool) : literal (valuationOf b) 342 = decide (2 ≤ count341 b) := rfl
theorem meaning343 (b : Nat → Bool) : literal (valuationOf b) 343 = decide (1 ≤ count343 b) := rfl
theorem meaning344 (b : Nat → Bool) : literal (valuationOf b) 344 = decide (2 ≤ count343 b) := rfl
theorem meaning345 (b : Nat → Bool) : literal (valuationOf b) 345 = decide (1 ≤ count345 b) := rfl
theorem meaning349 (b : Nat → Bool) : literal (valuationOf b) 349 = decide (1 ≤ count349 b) := rfl
theorem meaning351 (b : Nat → Bool) : literal (valuationOf b) 351 = decide (1 ≤ count351 b) := rfl
theorem meaning353 (b : Nat → Bool) : literal (valuationOf b) 353 = decide (1 ≤ count353 b) := rfl
theorem meaning355 (b : Nat → Bool) : literal (valuationOf b) 355 = decide (1 ≤ count355 b) := rfl
theorem meaning357 (b : Nat → Bool) : literal (valuationOf b) 357 = decide (1 ≤ count357 b) := rfl
theorem meaning358 (b : Nat → Bool) : literal (valuationOf b) 358 = decide (2 ≤ count357 b) := rfl
theorem meaning359 (b : Nat → Bool) : literal (valuationOf b) 359 = decide (1 ≤ count359 b) := rfl
theorem meaning361 (b : Nat → Bool) : literal (valuationOf b) 361 = decide (1 ≤ count361 b) := rfl
theorem meaning363 (b : Nat → Bool) : literal (valuationOf b) 363 = decide (1 ≤ count363 b) := rfl
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
theorem meaning379 (b : Nat → Bool) : literal (valuationOf b) 379 = decide (1 ≤ count379 b) := rfl
theorem meaning381 (b : Nat → Bool) : literal (valuationOf b) 381 = decide (1 ≤ count381 b) := rfl
theorem meaning383 (b : Nat → Bool) : literal (valuationOf b) 383 = decide (1 ≤ count383 b) := rfl
theorem meaning387 (b : Nat → Bool) : literal (valuationOf b) 387 = decide (1 ≤ count387 b) := rfl
theorem meaning389 (b : Nat → Bool) : literal (valuationOf b) 389 = decide (1 ≤ count389 b) := rfl
theorem meaning390 (b : Nat → Bool) : literal (valuationOf b) 390 = decide (2 ≤ count389 b) := rfl
theorem meaning391 (b : Nat → Bool) : literal (valuationOf b) 391 = decide (1 ≤ count391 b) := rfl
theorem meaning393 (b : Nat → Bool) : literal (valuationOf b) 393 = decide (1 ≤ count393 b) := rfl
theorem meaning395 (b : Nat → Bool) : literal (valuationOf b) 395 = decide (1 ≤ count395 b) := rfl
theorem meaning396 (b : Nat → Bool) : literal (valuationOf b) 396 = decide (2 ≤ count395 b) := rfl
theorem meaning399 (b : Nat → Bool) : literal (valuationOf b) 399 = decide (1 ≤ count399 b) := rfl
theorem meaning401 (b : Nat → Bool) : literal (valuationOf b) 401 = decide (1 ≤ count401 b) := rfl
theorem meaning403 (b : Nat → Bool) : literal (valuationOf b) 403 = decide (1 ≤ count403 b) := rfl
theorem meaning404 (b : Nat → Bool) : literal (valuationOf b) 404 = decide (2 ≤ count403 b) := rfl
theorem meaning405 (b : Nat → Bool) : literal (valuationOf b) 405 = decide (1 ≤ count405 b) := rfl
theorem meaning406 (b : Nat → Bool) : literal (valuationOf b) 406 = decide (2 ≤ count405 b) := rfl
theorem meaning407 (b : Nat → Bool) : literal (valuationOf b) 407 = decide (1 ≤ count407 b) := rfl
theorem meaning409 (b : Nat → Bool) : literal (valuationOf b) 409 = decide (1 ≤ count409 b) := rfl
theorem meaning411 (b : Nat → Bool) : literal (valuationOf b) 411 = decide (1 ≤ count411 b) := rfl
theorem meaning412 (b : Nat → Bool) : literal (valuationOf b) 412 = decide (2 ≤ count411 b) := rfl
theorem meaning413 (b : Nat → Bool) : literal (valuationOf b) 413 = decide (1 ≤ count413 b) := rfl
theorem meaning415 (b : Nat → Bool) : literal (valuationOf b) 415 = decide (1 ≤ count415 b) := rfl
theorem meaning417 (b : Nat → Bool) : literal (valuationOf b) 417 = decide (1 ≤ count417 b) := rfl
theorem meaning419 (b : Nat → Bool) : literal (valuationOf b) 419 = decide (1 ≤ count419 b) := rfl
theorem meaning420 (b : Nat → Bool) : literal (valuationOf b) 420 = decide (2 ≤ count419 b) := rfl
theorem meaning421 (b : Nat → Bool) : literal (valuationOf b) 421 = decide (1 ≤ count421 b) := rfl
theorem meaning425 (b : Nat → Bool) : literal (valuationOf b) 425 = decide (1 ≤ count425 b) := rfl
theorem meaning427 (b : Nat → Bool) : literal (valuationOf b) 427 = decide (1 ≤ count427 b) := rfl
theorem meaning429 (b : Nat → Bool) : literal (valuationOf b) 429 = decide (1 ≤ count429 b) := rfl
theorem meaning431 (b : Nat → Bool) : literal (valuationOf b) 431 = decide (1 ≤ count431 b) := rfl
theorem meaning433 (b : Nat → Bool) : literal (valuationOf b) 433 = decide (1 ≤ count433 b) := rfl
theorem meaning435 (b : Nat → Bool) : literal (valuationOf b) 435 = decide (1 ≤ count435 b) := rfl
theorem meaning436 (b : Nat → Bool) : literal (valuationOf b) 436 = decide (2 ≤ count435 b) := rfl
theorem meaning437 (b : Nat → Bool) : literal (valuationOf b) 437 = decide (1 ≤ count437 b) := rfl
theorem meaning438 (b : Nat → Bool) : literal (valuationOf b) 438 = decide (2 ≤ count437 b) := rfl
theorem meaning441 (b : Nat → Bool) : literal (valuationOf b) 441 = decide (1 ≤ count441 b) := rfl
theorem meaning443 (b : Nat → Bool) : literal (valuationOf b) 443 = decide (1 ≤ count443 b) := rfl
theorem meaning445 (b : Nat → Bool) : literal (valuationOf b) 445 = decide (1 ≤ count445 b) := rfl
theorem meaning447 (b : Nat → Bool) : literal (valuationOf b) 447 = decide (1 ≤ count447 b) := rfl
theorem meaning449 (b : Nat → Bool) : literal (valuationOf b) 449 = decide (1 ≤ count449 b) := rfl
theorem meaning450 (b : Nat → Bool) : literal (valuationOf b) 450 = decide (2 ≤ count449 b) := rfl
theorem meaning451 (b : Nat → Bool) : literal (valuationOf b) 451 = decide (1 ≤ count451 b) := rfl
theorem meaning452 (b : Nat → Bool) : literal (valuationOf b) 452 = decide (2 ≤ count451 b) := rfl
theorem meaning453 (b : Nat → Bool) : literal (valuationOf b) 453 = decide (1 ≤ count453 b) := rfl
theorem meaning455 (b : Nat → Bool) : literal (valuationOf b) 455 = decide (1 ≤ count455 b) := rfl
theorem meaning457 (b : Nat → Bool) : literal (valuationOf b) 457 = decide (1 ≤ count457 b) := rfl
theorem meaning459 (b : Nat → Bool) : literal (valuationOf b) 459 = decide (1 ≤ count459 b) := rfl
theorem meaning461 (b : Nat → Bool) : literal (valuationOf b) 461 = decide (1 ≤ count461 b) := rfl
theorem meaning463 (b : Nat → Bool) : literal (valuationOf b) 463 = decide (1 ≤ count463 b) := rfl
theorem meaning465 (b : Nat → Bool) : literal (valuationOf b) 465 = decide (1 ≤ count465 b) := rfl
theorem meaning466 (b : Nat → Bool) : literal (valuationOf b) 466 = decide (2 ≤ count465 b) := rfl
theorem meaning467 (b : Nat → Bool) : literal (valuationOf b) 467 = decide (1 ≤ count467 b) := rfl
theorem meaning468 (b : Nat → Bool) : literal (valuationOf b) 468 = decide (2 ≤ count467 b) := rfl
theorem meaning469 (b : Nat → Bool) : literal (valuationOf b) 469 = decide (1 ≤ count469 b) := rfl
theorem meaning473 (b : Nat → Bool) : literal (valuationOf b) 473 = decide (1 ≤ count473 b) := rfl
theorem meaning475 (b : Nat → Bool) : literal (valuationOf b) 475 = decide (1 ≤ count475 b) := rfl
theorem meaning476 (b : Nat → Bool) : literal (valuationOf b) 476 = decide (2 ≤ count475 b) := rfl
theorem meaning477 (b : Nat → Bool) : literal (valuationOf b) 477 = decide (1 ≤ count477 b) := rfl
theorem meaning479 (b : Nat → Bool) : literal (valuationOf b) 479 = decide (1 ≤ count479 b) := rfl
theorem meaning480 (b : Nat → Bool) : literal (valuationOf b) 480 = decide (2 ≤ count479 b) := rfl
theorem meaning481 (b : Nat → Bool) : literal (valuationOf b) 481 = decide (1 ≤ count481 b) := rfl
theorem meaning482 (b : Nat → Bool) : literal (valuationOf b) 482 = decide (2 ≤ count481 b) := rfl
theorem meaning483 (b : Nat → Bool) : literal (valuationOf b) 483 = decide (1 ≤ count483 b) := rfl
theorem meaning485 (b : Nat → Bool) : literal (valuationOf b) 485 = decide (1 ≤ count485 b) := rfl
theorem meaning487 (b : Nat → Bool) : literal (valuationOf b) 487 = decide (1 ≤ count487 b) := rfl
theorem meaning489 (b : Nat → Bool) : literal (valuationOf b) 489 = decide (1 ≤ count489 b) := rfl
theorem meaning491 (b : Nat → Bool) : literal (valuationOf b) 491 = decide (1 ≤ count491 b) := rfl
theorem meaning493 (b : Nat → Bool) : literal (valuationOf b) 493 = decide (1 ≤ count493 b) := rfl
theorem meaning495 (b : Nat → Bool) : literal (valuationOf b) 495 = decide (1 ≤ count495 b) := rfl
theorem meaning496 (b : Nat → Bool) : literal (valuationOf b) 496 = decide (2 ≤ count495 b) := rfl
theorem meaning497 (b : Nat → Bool) : literal (valuationOf b) 497 = decide (1 ≤ count497 b) := rfl
theorem meaning498 (b : Nat → Bool) : literal (valuationOf b) 498 = decide (2 ≤ count497 b) := rfl
theorem meaning499 (b : Nat → Bool) : literal (valuationOf b) 499 = decide (1 ≤ count499 b) := rfl
theorem meaning500 (b : Nat → Bool) : literal (valuationOf b) 500 = decide (2 ≤ count499 b) := rfl
theorem meaning501 (b : Nat → Bool) : literal (valuationOf b) 501 = decide (1 ≤ count501 b) := rfl
theorem meaning502 (b : Nat → Bool) : literal (valuationOf b) 502 = decide (2 ≤ count501 b) := rfl
theorem meaning504 (b : Nat → Bool) : literal (valuationOf b) 504 = decide (2 ≤ count503 b) := rfl
theorem meaning867 (b : Nat → Bool) : literal (valuationOf b) 867 = decide (1 ≤ count867 b) := rfl
theorem meaning868 (b : Nat → Bool) : literal (valuationOf b) 868 = decide (2 ≤ count867 b) := rfl
theorem meaning869 (b : Nat → Bool) : literal (valuationOf b) 869 = decide (1 ≤ count869 b) := rfl
theorem meaning870 (b : Nat → Bool) : literal (valuationOf b) 870 = decide (2 ≤ count869 b) := rfl
theorem meaning871 (b : Nat → Bool) : literal (valuationOf b) 871 = decide (1 ≤ count871 b) := rfl
theorem meaning872 (b : Nat → Bool) : literal (valuationOf b) 872 = decide (2 ≤ count871 b) := rfl
theorem meaning873 (b : Nat → Bool) : literal (valuationOf b) 873 = decide (3 ≤ count871 b) := rfl
theorem meaning874 (b : Nat → Bool) : literal (valuationOf b) 874 = decide (4 ≤ count871 b) := rfl
theorem meaning875 (b : Nat → Bool) : literal (valuationOf b) 875 = decide (1 ≤ count875 b) := rfl
theorem meaning876 (b : Nat → Bool) : literal (valuationOf b) 876 = decide (2 ≤ count875 b) := rfl
theorem meaning877 (b : Nat → Bool) : literal (valuationOf b) 877 = decide (1 ≤ count877 b) := rfl
theorem meaning878 (b : Nat → Bool) : literal (valuationOf b) 878 = decide (2 ≤ count877 b) := rfl
theorem meaning879 (b : Nat → Bool) : literal (valuationOf b) 879 = decide (1 ≤ count879 b) := rfl
theorem meaning880 (b : Nat → Bool) : literal (valuationOf b) 880 = decide (2 ≤ count879 b) := rfl
theorem meaning881 (b : Nat → Bool) : literal (valuationOf b) 881 = decide (3 ≤ count879 b) := rfl
theorem meaning882 (b : Nat → Bool) : literal (valuationOf b) 882 = decide (4 ≤ count879 b) := rfl
theorem meaning883 (b : Nat → Bool) : literal (valuationOf b) 883 = decide (1 ≤ count883 b) := rfl
theorem meaning884 (b : Nat → Bool) : literal (valuationOf b) 884 = decide (2 ≤ count883 b) := rfl
theorem meaning885 (b : Nat → Bool) : literal (valuationOf b) 885 = decide (3 ≤ count883 b) := rfl
theorem meaning886 (b : Nat → Bool) : literal (valuationOf b) 886 = decide (4 ≤ count883 b) := rfl
theorem meaning887 (b : Nat → Bool) : literal (valuationOf b) 887 = decide (5 ≤ count883 b) := rfl
theorem meaning888 (b : Nat → Bool) : literal (valuationOf b) 888 = decide (6 ≤ count883 b) := rfl
theorem meaning891 (b : Nat → Bool) : literal (valuationOf b) 891 = decide (1 ≤ count891 b) := rfl
theorem meaning892 (b : Nat → Bool) : literal (valuationOf b) 892 = decide (2 ≤ count891 b) := rfl
theorem meaning893 (b : Nat → Bool) : literal (valuationOf b) 893 = decide (1 ≤ count893 b) := rfl
theorem meaning894 (b : Nat → Bool) : literal (valuationOf b) 894 = decide (2 ≤ count893 b) := rfl
theorem meaning895 (b : Nat → Bool) : literal (valuationOf b) 895 = decide (1 ≤ count895 b) := rfl
theorem meaning896 (b : Nat → Bool) : literal (valuationOf b) 896 = decide (2 ≤ count895 b) := rfl
theorem meaning897 (b : Nat → Bool) : literal (valuationOf b) 897 = decide (3 ≤ count895 b) := rfl
theorem meaning898 (b : Nat → Bool) : literal (valuationOf b) 898 = decide (4 ≤ count895 b) := rfl
theorem meaning899 (b : Nat → Bool) : literal (valuationOf b) 899 = decide (1 ≤ count899 b) := rfl
theorem meaning900 (b : Nat → Bool) : literal (valuationOf b) 900 = decide (2 ≤ count899 b) := rfl
theorem meaning901 (b : Nat → Bool) : literal (valuationOf b) 901 = decide (1 ≤ count901 b) := rfl
theorem meaning902 (b : Nat → Bool) : literal (valuationOf b) 902 = decide (2 ≤ count901 b) := rfl
theorem meaning903 (b : Nat → Bool) : literal (valuationOf b) 903 = decide (1 ≤ count903 b) := rfl
theorem meaning904 (b : Nat → Bool) : literal (valuationOf b) 904 = decide (2 ≤ count903 b) := rfl
theorem meaning905 (b : Nat → Bool) : literal (valuationOf b) 905 = decide (3 ≤ count903 b) := rfl
theorem meaning906 (b : Nat → Bool) : literal (valuationOf b) 906 = decide (4 ≤ count903 b) := rfl
theorem meaning907 (b : Nat → Bool) : literal (valuationOf b) 907 = decide (1 ≤ count907 b) := rfl
theorem meaning908 (b : Nat → Bool) : literal (valuationOf b) 908 = decide (2 ≤ count907 b) := rfl
theorem meaning909 (b : Nat → Bool) : literal (valuationOf b) 909 = decide (3 ≤ count907 b) := rfl
theorem meaning910 (b : Nat → Bool) : literal (valuationOf b) 910 = decide (4 ≤ count907 b) := rfl
theorem meaning911 (b : Nat → Bool) : literal (valuationOf b) 911 = decide (5 ≤ count907 b) := rfl
theorem meaning912 (b : Nat → Bool) : literal (valuationOf b) 912 = decide (6 ≤ count907 b) := rfl
theorem meaning916 (b : Nat → Bool) : literal (valuationOf b) 916 = decide (2 ≤ count915 b) := rfl
theorem meaning917 (b : Nat → Bool) : literal (valuationOf b) 917 = decide (3 ≤ count915 b) := rfl
theorem meaning918 (b : Nat → Bool) : literal (valuationOf b) 918 = decide (4 ≤ count915 b) := rfl
theorem meaning919 (b : Nat → Bool) : literal (valuationOf b) 919 = decide (5 ≤ count915 b) := rfl
theorem meaning920 (b : Nat → Bool) : literal (valuationOf b) 920 = decide (6 ≤ count915 b) := rfl
theorem meaning921 (b : Nat → Bool) : literal (valuationOf b) 921 = decide (7 ≤ count915 b) := rfl
theorem meaning922 (b : Nat → Bool) : literal (valuationOf b) 922 = decide (8 ≤ count915 b) := rfl
theorem meaning923 (b : Nat → Bool) : literal (valuationOf b) 923 = decide (9 ≤ count915 b) := rfl
theorem meaning931 (b : Nat → Bool) : literal (valuationOf b) 931 = decide (1 ≤ count931 b) := rfl
theorem meaning932 (b : Nat → Bool) : literal (valuationOf b) 932 = decide (2 ≤ count931 b) := rfl
theorem meaning933 (b : Nat → Bool) : literal (valuationOf b) 933 = decide (1 ≤ count933 b) := rfl
theorem meaning934 (b : Nat → Bool) : literal (valuationOf b) 934 = decide (2 ≤ count933 b) := rfl
theorem meaning935 (b : Nat → Bool) : literal (valuationOf b) 935 = decide (1 ≤ count935 b) := rfl
theorem meaning936 (b : Nat → Bool) : literal (valuationOf b) 936 = decide (2 ≤ count935 b) := rfl
theorem meaning937 (b : Nat → Bool) : literal (valuationOf b) 937 = decide (3 ≤ count935 b) := rfl
theorem meaning938 (b : Nat → Bool) : literal (valuationOf b) 938 = decide (4 ≤ count935 b) := rfl
theorem meaning939 (b : Nat → Bool) : literal (valuationOf b) 939 = decide (1 ≤ count939 b) := rfl
theorem meaning940 (b : Nat → Bool) : literal (valuationOf b) 940 = decide (2 ≤ count939 b) := rfl
theorem meaning941 (b : Nat → Bool) : literal (valuationOf b) 941 = decide (1 ≤ count941 b) := rfl
theorem meaning942 (b : Nat → Bool) : literal (valuationOf b) 942 = decide (2 ≤ count941 b) := rfl
theorem meaning943 (b : Nat → Bool) : literal (valuationOf b) 943 = decide (1 ≤ count943 b) := rfl
theorem meaning944 (b : Nat → Bool) : literal (valuationOf b) 944 = decide (2 ≤ count943 b) := rfl
theorem meaning945 (b : Nat → Bool) : literal (valuationOf b) 945 = decide (3 ≤ count943 b) := rfl
theorem meaning946 (b : Nat → Bool) : literal (valuationOf b) 946 = decide (4 ≤ count943 b) := rfl
theorem meaning947 (b : Nat → Bool) : literal (valuationOf b) 947 = decide (1 ≤ count947 b) := rfl
theorem meaning948 (b : Nat → Bool) : literal (valuationOf b) 948 = decide (2 ≤ count947 b) := rfl
theorem meaning949 (b : Nat → Bool) : literal (valuationOf b) 949 = decide (3 ≤ count947 b) := rfl
theorem meaning950 (b : Nat → Bool) : literal (valuationOf b) 950 = decide (4 ≤ count947 b) := rfl
theorem meaning951 (b : Nat → Bool) : literal (valuationOf b) 951 = decide (5 ≤ count947 b) := rfl
theorem meaning952 (b : Nat → Bool) : literal (valuationOf b) 952 = decide (6 ≤ count947 b) := rfl
theorem meaning954 (b : Nat → Bool) : literal (valuationOf b) 954 = decide (8 ≤ count947 b) := rfl
theorem meaning955 (b : Nat → Bool) : literal (valuationOf b) 955 = decide (1 ≤ count955 b) := rfl
theorem meaning956 (b : Nat → Bool) : literal (valuationOf b) 956 = decide (2 ≤ count955 b) := rfl
theorem meaning957 (b : Nat → Bool) : literal (valuationOf b) 957 = decide (1 ≤ count957 b) := rfl
theorem meaning958 (b : Nat → Bool) : literal (valuationOf b) 958 = decide (2 ≤ count957 b) := rfl
theorem meaning959 (b : Nat → Bool) : literal (valuationOf b) 959 = decide (1 ≤ count959 b) := rfl
theorem meaning960 (b : Nat → Bool) : literal (valuationOf b) 960 = decide (2 ≤ count959 b) := rfl
theorem meaning961 (b : Nat → Bool) : literal (valuationOf b) 961 = decide (3 ≤ count959 b) := rfl
theorem meaning962 (b : Nat → Bool) : literal (valuationOf b) 962 = decide (4 ≤ count959 b) := rfl
theorem meaning963 (b : Nat → Bool) : literal (valuationOf b) 963 = decide (1 ≤ count963 b) := rfl
theorem meaning964 (b : Nat → Bool) : literal (valuationOf b) 964 = decide (2 ≤ count963 b) := rfl
theorem meaning965 (b : Nat → Bool) : literal (valuationOf b) 965 = decide (1 ≤ count965 b) := rfl
theorem meaning966 (b : Nat → Bool) : literal (valuationOf b) 966 = decide (2 ≤ count965 b) := rfl
theorem meaning967 (b : Nat → Bool) : literal (valuationOf b) 967 = decide (1 ≤ count967 b) := rfl
theorem meaning968 (b : Nat → Bool) : literal (valuationOf b) 968 = decide (2 ≤ count967 b) := rfl
theorem meaning969 (b : Nat → Bool) : literal (valuationOf b) 969 = decide (3 ≤ count967 b) := rfl
theorem meaning970 (b : Nat → Bool) : literal (valuationOf b) 970 = decide (4 ≤ count967 b) := rfl
theorem meaning971 (b : Nat → Bool) : literal (valuationOf b) 971 = decide (1 ≤ count971 b) := rfl
theorem meaning972 (b : Nat → Bool) : literal (valuationOf b) 972 = decide (2 ≤ count971 b) := rfl
theorem meaning973 (b : Nat → Bool) : literal (valuationOf b) 973 = decide (3 ≤ count971 b) := rfl
theorem meaning974 (b : Nat → Bool) : literal (valuationOf b) 974 = decide (4 ≤ count971 b) := rfl
theorem meaning975 (b : Nat → Bool) : literal (valuationOf b) 975 = decide (5 ≤ count971 b) := rfl
theorem meaning976 (b : Nat → Bool) : literal (valuationOf b) 976 = decide (6 ≤ count971 b) := rfl
theorem meaning981 (b : Nat → Bool) : literal (valuationOf b) 981 = decide (3 ≤ count979 b) := rfl
theorem meaning982 (b : Nat → Bool) : literal (valuationOf b) 982 = decide (4 ≤ count979 b) := rfl
theorem meaning983 (b : Nat → Bool) : literal (valuationOf b) 983 = decide (5 ≤ count979 b) := rfl
theorem meaning984 (b : Nat → Bool) : literal (valuationOf b) 984 = decide (6 ≤ count979 b) := rfl
theorem meaning985 (b : Nat → Bool) : literal (valuationOf b) 985 = decide (7 ≤ count979 b) := rfl
theorem meaning986 (b : Nat → Bool) : literal (valuationOf b) 986 = decide (8 ≤ count979 b) := rfl
theorem meaning987 (b : Nat → Bool) : literal (valuationOf b) 987 = decide (9 ≤ count979 b) := rfl
theorem meaning988 (b : Nat → Bool) : literal (valuationOf b) 988 = decide (10 ≤ count979 b) := rfl
theorem meaning990 (b : Nat → Bool) : literal (valuationOf b) 990 = decide (12 ≤ count979 b) := rfl
theorem meaning1003 (b : Nat → Bool) : literal (valuationOf b) 1003 = decide (9 ≤ count995 b) := rfl
theorem meaning1004 (b : Nat → Bool) : literal (valuationOf b) 1004 = decide (10 ≤ count995 b) := rfl
theorem meaning1005 (b : Nat → Bool) : literal (valuationOf b) 1005 = decide (11 ≤ count995 b) := rfl
theorem meaning1006 (b : Nat → Bool) : literal (valuationOf b) 1006 = decide (12 ≤ count995 b) := rfl
theorem meaning1007 (b : Nat → Bool) : literal (valuationOf b) 1007 = decide (13 ≤ count995 b) := rfl
theorem meaning1008 (b : Nat → Bool) : literal (valuationOf b) 1008 = decide (14 ≤ count995 b) := rfl
theorem meaning1009 (b : Nat → Bool) : literal (valuationOf b) 1009 = decide (15 ≤ count995 b) := rfl
theorem meaning1019 (b : Nat → Bool) : literal (valuationOf b) 1019 = decide (1 ≤ count1019 b) := rfl
theorem meaning1020 (b : Nat → Bool) : literal (valuationOf b) 1020 = decide (2 ≤ count1019 b) := rfl
theorem meaning1021 (b : Nat → Bool) : literal (valuationOf b) 1021 = decide (1 ≤ count1021 b) := rfl
theorem meaning1022 (b : Nat → Bool) : literal (valuationOf b) 1022 = decide (2 ≤ count1021 b) := rfl
theorem meaning1024 (b : Nat → Bool) : literal (valuationOf b) 1024 = decide (2 ≤ count1023 b) := rfl
theorem meaning1025 (b : Nat → Bool) : literal (valuationOf b) 1025 = decide (3 ≤ count1023 b) := rfl
theorem meaning1026 (b : Nat → Bool) : literal (valuationOf b) 1026 = decide (4 ≤ count1023 b) := rfl
theorem meaning1027 (b : Nat → Bool) : literal (valuationOf b) 1027 = decide (1 ≤ count1027 b) := rfl
theorem meaning1028 (b : Nat → Bool) : literal (valuationOf b) 1028 = decide (2 ≤ count1027 b) := rfl
theorem meaning1029 (b : Nat → Bool) : literal (valuationOf b) 1029 = decide (1 ≤ count1029 b) := rfl
theorem meaning1030 (b : Nat → Bool) : literal (valuationOf b) 1030 = decide (2 ≤ count1029 b) := rfl
theorem meaning1031 (b : Nat → Bool) : literal (valuationOf b) 1031 = decide (1 ≤ count1031 b) := rfl
theorem meaning1032 (b : Nat → Bool) : literal (valuationOf b) 1032 = decide (2 ≤ count1031 b) := rfl
theorem meaning1033 (b : Nat → Bool) : literal (valuationOf b) 1033 = decide (3 ≤ count1031 b) := rfl
theorem meaning1034 (b : Nat → Bool) : literal (valuationOf b) 1034 = decide (4 ≤ count1031 b) := rfl
theorem meaning1036 (b : Nat → Bool) : literal (valuationOf b) 1036 = decide (2 ≤ count1035 b) := rfl
theorem meaning1037 (b : Nat → Bool) : literal (valuationOf b) 1037 = decide (3 ≤ count1035 b) := rfl
theorem meaning1038 (b : Nat → Bool) : literal (valuationOf b) 1038 = decide (4 ≤ count1035 b) := rfl
theorem meaning1039 (b : Nat → Bool) : literal (valuationOf b) 1039 = decide (5 ≤ count1035 b) := rfl
theorem meaning1040 (b : Nat → Bool) : literal (valuationOf b) 1040 = decide (6 ≤ count1035 b) := rfl
theorem meaning1041 (b : Nat → Bool) : literal (valuationOf b) 1041 = decide (7 ≤ count1035 b) := rfl
theorem meaning1042 (b : Nat → Bool) : literal (valuationOf b) 1042 = decide (8 ≤ count1035 b) := rfl
theorem meaning1043 (b : Nat → Bool) : literal (valuationOf b) 1043 = decide (1 ≤ count1043 b) := rfl
theorem meaning1044 (b : Nat → Bool) : literal (valuationOf b) 1044 = decide (2 ≤ count1043 b) := rfl
theorem meaning1045 (b : Nat → Bool) : literal (valuationOf b) 1045 = decide (1 ≤ count1045 b) := rfl
theorem meaning1046 (b : Nat → Bool) : literal (valuationOf b) 1046 = decide (2 ≤ count1045 b) := rfl
theorem meaning1047 (b : Nat → Bool) : literal (valuationOf b) 1047 = decide (1 ≤ count1047 b) := rfl
theorem meaning1048 (b : Nat → Bool) : literal (valuationOf b) 1048 = decide (2 ≤ count1047 b) := rfl
theorem meaning1049 (b : Nat → Bool) : literal (valuationOf b) 1049 = decide (3 ≤ count1047 b) := rfl
theorem meaning1050 (b : Nat → Bool) : literal (valuationOf b) 1050 = decide (4 ≤ count1047 b) := rfl
theorem meaning1051 (b : Nat → Bool) : literal (valuationOf b) 1051 = decide (1 ≤ count1051 b) := rfl
theorem meaning1052 (b : Nat → Bool) : literal (valuationOf b) 1052 = decide (2 ≤ count1051 b) := rfl
theorem meaning1053 (b : Nat → Bool) : literal (valuationOf b) 1053 = decide (1 ≤ count1053 b) := rfl
theorem meaning1054 (b : Nat → Bool) : literal (valuationOf b) 1054 = decide (2 ≤ count1053 b) := rfl
theorem meaning1055 (b : Nat → Bool) : literal (valuationOf b) 1055 = decide (1 ≤ count1055 b) := rfl
theorem meaning1056 (b : Nat → Bool) : literal (valuationOf b) 1056 = decide (2 ≤ count1055 b) := rfl
theorem meaning1057 (b : Nat → Bool) : literal (valuationOf b) 1057 = decide (3 ≤ count1055 b) := rfl
theorem meaning1058 (b : Nat → Bool) : literal (valuationOf b) 1058 = decide (4 ≤ count1055 b) := rfl
theorem meaning1059 (b : Nat → Bool) : literal (valuationOf b) 1059 = decide (1 ≤ count1059 b) := rfl
theorem meaning1060 (b : Nat → Bool) : literal (valuationOf b) 1060 = decide (2 ≤ count1059 b) := rfl
theorem meaning1061 (b : Nat → Bool) : literal (valuationOf b) 1061 = decide (3 ≤ count1059 b) := rfl
theorem meaning1062 (b : Nat → Bool) : literal (valuationOf b) 1062 = decide (4 ≤ count1059 b) := rfl
theorem meaning1063 (b : Nat → Bool) : literal (valuationOf b) 1063 = decide (5 ≤ count1059 b) := rfl
theorem meaning1064 (b : Nat → Bool) : literal (valuationOf b) 1064 = decide (6 ≤ count1059 b) := rfl
theorem meaning1065 (b : Nat → Bool) : literal (valuationOf b) 1065 = decide (7 ≤ count1059 b) := rfl
theorem meaning1066 (b : Nat → Bool) : literal (valuationOf b) 1066 = decide (8 ≤ count1059 b) := rfl
theorem meaning1071 (b : Nat → Bool) : literal (valuationOf b) 1071 = decide (5 ≤ count1067 b) := rfl
theorem meaning1072 (b : Nat → Bool) : literal (valuationOf b) 1072 = decide (6 ≤ count1067 b) := rfl
theorem meaning1073 (b : Nat → Bool) : literal (valuationOf b) 1073 = decide (7 ≤ count1067 b) := rfl
theorem meaning1074 (b : Nat → Bool) : literal (valuationOf b) 1074 = decide (8 ≤ count1067 b) := rfl
theorem meaning1075 (b : Nat → Bool) : literal (valuationOf b) 1075 = decide (9 ≤ count1067 b) := rfl
theorem meaning1076 (b : Nat → Bool) : literal (valuationOf b) 1076 = decide (10 ≤ count1067 b) := rfl
theorem meaning1077 (b : Nat → Bool) : literal (valuationOf b) 1077 = decide (11 ≤ count1067 b) := rfl
theorem meaning1078 (b : Nat → Bool) : literal (valuationOf b) 1078 = decide (12 ≤ count1067 b) := rfl
theorem meaning1079 (b : Nat → Bool) : literal (valuationOf b) 1079 = decide (13 ≤ count1067 b) := rfl
theorem meaning1083 (b : Nat → Bool) : literal (valuationOf b) 1083 = decide (1 ≤ count1083 b) := rfl
theorem meaning1084 (b : Nat → Bool) : literal (valuationOf b) 1084 = decide (2 ≤ count1083 b) := rfl
theorem meaning1085 (b : Nat → Bool) : literal (valuationOf b) 1085 = decide (1 ≤ count1085 b) := rfl
theorem meaning1086 (b : Nat → Bool) : literal (valuationOf b) 1086 = decide (2 ≤ count1085 b) := rfl
theorem meaning1087 (b : Nat → Bool) : literal (valuationOf b) 1087 = decide (1 ≤ count1087 b) := rfl
theorem meaning1088 (b : Nat → Bool) : literal (valuationOf b) 1088 = decide (2 ≤ count1087 b) := rfl
theorem meaning1089 (b : Nat → Bool) : literal (valuationOf b) 1089 = decide (3 ≤ count1087 b) := rfl
theorem meaning1090 (b : Nat → Bool) : literal (valuationOf b) 1090 = decide (4 ≤ count1087 b) := rfl
theorem meaning1091 (b : Nat → Bool) : literal (valuationOf b) 1091 = decide (1 ≤ count1091 b) := rfl
theorem meaning1092 (b : Nat → Bool) : literal (valuationOf b) 1092 = decide (2 ≤ count1091 b) := rfl
theorem meaning1093 (b : Nat → Bool) : literal (valuationOf b) 1093 = decide (1 ≤ count1093 b) := rfl
theorem meaning1094 (b : Nat → Bool) : literal (valuationOf b) 1094 = decide (2 ≤ count1093 b) := rfl
theorem meaning1095 (b : Nat → Bool) : literal (valuationOf b) 1095 = decide (1 ≤ count1095 b) := rfl
theorem meaning1096 (b : Nat → Bool) : literal (valuationOf b) 1096 = decide (2 ≤ count1095 b) := rfl
theorem meaning1097 (b : Nat → Bool) : literal (valuationOf b) 1097 = decide (3 ≤ count1095 b) := rfl
theorem meaning1098 (b : Nat → Bool) : literal (valuationOf b) 1098 = decide (4 ≤ count1095 b) := rfl
theorem meaning1099 (b : Nat → Bool) : literal (valuationOf b) 1099 = decide (1 ≤ count1099 b) := rfl
theorem meaning1100 (b : Nat → Bool) : literal (valuationOf b) 1100 = decide (2 ≤ count1099 b) := rfl
theorem meaning1101 (b : Nat → Bool) : literal (valuationOf b) 1101 = decide (3 ≤ count1099 b) := rfl
theorem meaning1102 (b : Nat → Bool) : literal (valuationOf b) 1102 = decide (4 ≤ count1099 b) := rfl
theorem meaning1103 (b : Nat → Bool) : literal (valuationOf b) 1103 = decide (5 ≤ count1099 b) := rfl
theorem meaning1104 (b : Nat → Bool) : literal (valuationOf b) 1104 = decide (6 ≤ count1099 b) := rfl
theorem meaning1107 (b : Nat → Bool) : literal (valuationOf b) 1107 = decide (1 ≤ count1107 b) := rfl
theorem meaning1108 (b : Nat → Bool) : literal (valuationOf b) 1108 = decide (2 ≤ count1107 b) := rfl
theorem meaning1109 (b : Nat → Bool) : literal (valuationOf b) 1109 = decide (1 ≤ count1109 b) := rfl
theorem meaning1110 (b : Nat → Bool) : literal (valuationOf b) 1110 = decide (2 ≤ count1109 b) := rfl
theorem meaning1111 (b : Nat → Bool) : literal (valuationOf b) 1111 = decide (1 ≤ count1111 b) := rfl
theorem meaning1112 (b : Nat → Bool) : literal (valuationOf b) 1112 = decide (2 ≤ count1111 b) := rfl
theorem meaning1113 (b : Nat → Bool) : literal (valuationOf b) 1113 = decide (3 ≤ count1111 b) := rfl
theorem meaning1114 (b : Nat → Bool) : literal (valuationOf b) 1114 = decide (4 ≤ count1111 b) := rfl
theorem meaning1115 (b : Nat → Bool) : literal (valuationOf b) 1115 = decide (1 ≤ count1115 b) := rfl
theorem meaning1116 (b : Nat → Bool) : literal (valuationOf b) 1116 = decide (2 ≤ count1115 b) := rfl
theorem meaning1117 (b : Nat → Bool) : literal (valuationOf b) 1117 = decide (1 ≤ count1117 b) := rfl
theorem meaning1119 (b : Nat → Bool) : literal (valuationOf b) 1119 = decide (1 ≤ count1119 b) := rfl
theorem meaning1120 (b : Nat → Bool) : literal (valuationOf b) 1120 = decide (2 ≤ count1119 b) := rfl
theorem meaning1121 (b : Nat → Bool) : literal (valuationOf b) 1121 = decide (3 ≤ count1119 b) := rfl
theorem meaning1123 (b : Nat → Bool) : literal (valuationOf b) 1123 = decide (1 ≤ count1123 b) := rfl
theorem meaning1124 (b : Nat → Bool) : literal (valuationOf b) 1124 = decide (2 ≤ count1123 b) := rfl
theorem meaning1125 (b : Nat → Bool) : literal (valuationOf b) 1125 = decide (3 ≤ count1123 b) := rfl
theorem meaning1126 (b : Nat → Bool) : literal (valuationOf b) 1126 = decide (4 ≤ count1123 b) := rfl
theorem meaning1131 (b : Nat → Bool) : literal (valuationOf b) 1131 = decide (1 ≤ count1131 b) := rfl
theorem meaning1132 (b : Nat → Bool) : literal (valuationOf b) 1132 = decide (2 ≤ count1131 b) := rfl
theorem meaning1133 (b : Nat → Bool) : literal (valuationOf b) 1133 = decide (3 ≤ count1131 b) := rfl
theorem meaning1134 (b : Nat → Bool) : literal (valuationOf b) 1134 = decide (4 ≤ count1131 b) := rfl
theorem meaning1135 (b : Nat → Bool) : literal (valuationOf b) 1135 = decide (5 ≤ count1131 b) := rfl
theorem meaning1136 (b : Nat → Bool) : literal (valuationOf b) 1136 = decide (6 ≤ count1131 b) := rfl
theorem meaning1137 (b : Nat → Bool) : literal (valuationOf b) 1137 = decide (7 ≤ count1131 b) := rfl
theorem meaning1138 (b : Nat → Bool) : literal (valuationOf b) 1138 = decide (8 ≤ count1131 b) := rfl
theorem meaning1139 (b : Nat → Bool) : literal (valuationOf b) 1139 = decide (9 ≤ count1131 b) := rfl
theorem meaning1155 (b : Nat → Bool) : literal (valuationOf b) 1155 = decide (9 ≤ count1147 b) := rfl
theorem meaning1156 (b : Nat → Bool) : literal (valuationOf b) 1156 = decide (10 ≤ count1147 b) := rfl
theorem meaning1157 (b : Nat → Bool) : literal (valuationOf b) 1157 = decide (11 ≤ count1147 b) := rfl
theorem meaning1158 (b : Nat → Bool) : literal (valuationOf b) 1158 = decide (12 ≤ count1147 b) := rfl
theorem meaning1159 (b : Nat → Bool) : literal (valuationOf b) 1159 = decide (13 ≤ count1147 b) := rfl
theorem meaning1160 (b : Nat → Bool) : literal (valuationOf b) 1160 = decide (14 ≤ count1147 b) := rfl
theorem meaning1161 (b : Nat → Bool) : literal (valuationOf b) 1161 = decide (15 ≤ count1147 b) := rfl
theorem meaning1194 (b : Nat → Bool) : literal (valuationOf b) 1194 = decide (24 ≤ count1171 b) := rfl
theorem meaning1551 (b : Nat → Bool) : literal (valuationOf b) 1551 = decide (1 ≤ count1551 b) := rfl
theorem meaning1553 (b : Nat → Bool) : literal (valuationOf b) 1553 = decide (1 ≤ count1553 b) := rfl
theorem meaning1556 (b : Nat → Bool) : literal (valuationOf b) 1556 = decide (1 ≤ count1556 b) := rfl
theorem meaning1558 (b : Nat → Bool) : literal (valuationOf b) 1558 = decide (1 ≤ count1558 b) := rfl
theorem meaning1559 (b : Nat → Bool) : literal (valuationOf b) 1559 = decide (2 ≤ count1558 b) := rfl
theorem meaning1560 (b : Nat → Bool) : literal (valuationOf b) 1560 = decide (1 ≤ count1560 b) := rfl
theorem meaning1561 (b : Nat → Bool) : literal (valuationOf b) 1561 = decide (2 ≤ count1560 b) := rfl
theorem meaning1564 (b : Nat → Bool) : literal (valuationOf b) 1564 = decide (1 ≤ count1564 b) := rfl
theorem meaning1565 (b : Nat → Bool) : literal (valuationOf b) 1565 = decide (2 ≤ count1564 b) := rfl
theorem meaning1571 (b : Nat → Bool) : literal (valuationOf b) 1571 = decide (1 ≤ count1571 b) := rfl
theorem meaning1573 (b : Nat → Bool) : literal (valuationOf b) 1573 = decide (1 ≤ count1573 b) := rfl
theorem meaning1576 (b : Nat → Bool) : literal (valuationOf b) 1576 = decide (2 ≤ count1575 b) := rfl
theorem meaning1579 (b : Nat → Bool) : literal (valuationOf b) 1579 = decide (1 ≤ count1579 b) := rfl
theorem meaning1581 (b : Nat → Bool) : literal (valuationOf b) 1581 = decide (1 ≤ count1581 b) := rfl
theorem meaning1583 (b : Nat → Bool) : literal (valuationOf b) 1583 = decide (1 ≤ count1583 b) := rfl
theorem meaning1584 (b : Nat → Bool) : literal (valuationOf b) 1584 = decide (2 ≤ count1583 b) := rfl
theorem meaning1589 (b : Nat → Bool) : literal (valuationOf b) 1589 = decide (3 ≤ count1587 b) := rfl
theorem meaning1590 (b : Nat → Bool) : literal (valuationOf b) 1590 = decide (4 ≤ count1587 b) := rfl
theorem meaning1598 (b : Nat → Bool) : literal (valuationOf b) 1598 = decide (4 ≤ count1595 b) := rfl
theorem meaning1599 (b : Nat → Bool) : literal (valuationOf b) 1599 = decide (5 ≤ count1595 b) := rfl
theorem meaning1600 (b : Nat → Bool) : literal (valuationOf b) 1600 = decide (6 ≤ count1595 b) := rfl
theorem meaning1610 (b : Nat → Bool) : literal (valuationOf b) 1610 = decide (1 ≤ count1610 b) := rfl
theorem meaning1612 (b : Nat → Bool) : literal (valuationOf b) 1612 = decide (1 ≤ count1612 b) := rfl
theorem meaning1614 (b : Nat → Bool) : literal (valuationOf b) 1614 = decide (1 ≤ count1614 b) := rfl
theorem meaning1618 (b : Nat → Bool) : literal (valuationOf b) 1618 = decide (1 ≤ count1618 b) := rfl
theorem meaning1620 (b : Nat → Bool) : literal (valuationOf b) 1620 = decide (1 ≤ count1620 b) := rfl
theorem meaning1621 (b : Nat → Bool) : literal (valuationOf b) 1621 = decide (2 ≤ count1620 b) := rfl
theorem meaning1622 (b : Nat → Bool) : literal (valuationOf b) 1622 = decide (1 ≤ count1622 b) := rfl
theorem meaning1623 (b : Nat → Bool) : literal (valuationOf b) 1623 = decide (2 ≤ count1622 b) := rfl
theorem meaning1627 (b : Nat → Bool) : literal (valuationOf b) 1627 = decide (2 ≤ count1626 b) := rfl
theorem meaning1628 (b : Nat → Bool) : literal (valuationOf b) 1628 = decide (3 ≤ count1626 b) := rfl
theorem meaning1634 (b : Nat → Bool) : literal (valuationOf b) 1634 = decide (1 ≤ count1634 b) := rfl
theorem meaning1635 (b : Nat → Bool) : literal (valuationOf b) 1635 = decide (2 ≤ count1634 b) := rfl
theorem meaning1636 (b : Nat → Bool) : literal (valuationOf b) 1636 = decide (1 ≤ count1636 b) := rfl
theorem meaning1638 (b : Nat → Bool) : literal (valuationOf b) 1638 = decide (1 ≤ count1638 b) := rfl
theorem meaning1639 (b : Nat → Bool) : literal (valuationOf b) 1639 = decide (2 ≤ count1638 b) := rfl
theorem meaning1642 (b : Nat → Bool) : literal (valuationOf b) 1642 = decide (1 ≤ count1642 b) := rfl
theorem meaning1643 (b : Nat → Bool) : literal (valuationOf b) 1643 = decide (2 ≤ count1642 b) := rfl
theorem meaning1644 (b : Nat → Bool) : literal (valuationOf b) 1644 = decide (1 ≤ count1644 b) := rfl
theorem meaning1646 (b : Nat → Bool) : literal (valuationOf b) 1646 = decide (1 ≤ count1646 b) := rfl
theorem meaning1647 (b : Nat → Bool) : literal (valuationOf b) 1647 = decide (2 ≤ count1646 b) := rfl
theorem meaning1648 (b : Nat → Bool) : literal (valuationOf b) 1648 = decide (3 ≤ count1646 b) := rfl
theorem meaning1651 (b : Nat → Bool) : literal (valuationOf b) 1651 = decide (2 ≤ count1650 b) := rfl
theorem meaning1652 (b : Nat → Bool) : literal (valuationOf b) 1652 = decide (3 ≤ count1650 b) := rfl
theorem meaning1661 (b : Nat → Bool) : literal (valuationOf b) 1661 = decide (4 ≤ count1658 b) := rfl
theorem meaning1662 (b : Nat → Bool) : literal (valuationOf b) 1662 = decide (5 ≤ count1658 b) := rfl
theorem meaning1682 (b : Nat → Bool) : literal (valuationOf b) 1682 = decide (9 ≤ count1674 b) := rfl
theorem meaning1683 (b : Nat → Bool) : literal (valuationOf b) 1683 = decide (10 ≤ count1674 b) := rfl
theorem meaning1697 (b : Nat → Bool) : literal (valuationOf b) 1697 = decide (1 ≤ count1697 b) := rfl
theorem meaning1699 (b : Nat → Bool) : literal (valuationOf b) 1699 = decide (1 ≤ count1699 b) := rfl
theorem meaning1701 (b : Nat → Bool) : literal (valuationOf b) 1701 = decide (1 ≤ count1701 b) := rfl
theorem meaning1702 (b : Nat → Bool) : literal (valuationOf b) 1702 = decide (2 ≤ count1701 b) := rfl
theorem meaning1705 (b : Nat → Bool) : literal (valuationOf b) 1705 = decide (1 ≤ count1705 b) := rfl
theorem meaning1707 (b : Nat → Bool) : literal (valuationOf b) 1707 = decide (1 ≤ count1707 b) := rfl
theorem meaning1710 (b : Nat → Bool) : literal (valuationOf b) 1710 = decide (2 ≤ count1709 b) := rfl
theorem meaning1715 (b : Nat → Bool) : literal (valuationOf b) 1715 = decide (3 ≤ count1713 b) := rfl
theorem meaning1716 (b : Nat → Bool) : literal (valuationOf b) 1716 = decide (4 ≤ count1713 b) := rfl
theorem meaning1721 (b : Nat → Bool) : literal (valuationOf b) 1721 = decide (1 ≤ count1721 b) := rfl
theorem meaning1722 (b : Nat → Bool) : literal (valuationOf b) 1722 = decide (2 ≤ count1721 b) := rfl
theorem meaning1723 (b : Nat → Bool) : literal (valuationOf b) 1723 = decide (1 ≤ count1723 b) := rfl
theorem meaning1724 (b : Nat → Bool) : literal (valuationOf b) 1724 = decide (2 ≤ count1723 b) := rfl
theorem meaning1727 (b : Nat → Bool) : literal (valuationOf b) 1727 = decide (3 ≤ count1725 b) := rfl
theorem meaning1730 (b : Nat → Bool) : literal (valuationOf b) 1730 = decide (2 ≤ count1729 b) := rfl
theorem meaning1734 (b : Nat → Bool) : literal (valuationOf b) 1734 = decide (2 ≤ count1733 b) := rfl
theorem meaning1741 (b : Nat → Bool) : literal (valuationOf b) 1741 = decide (5 ≤ count1737 b) := rfl
theorem meaning1752 (b : Nat → Bool) : literal (valuationOf b) 1752 = decide (8 ≤ count1745 b) := rfl
theorem meaning1753 (b : Nat → Bool) : literal (valuationOf b) 1753 = decide (9 ≤ count1745 b) := rfl
theorem meaning1763 (b : Nat → Bool) : literal (valuationOf b) 1763 = decide (1 ≤ count1763 b) := rfl
theorem meaning1765 (b : Nat → Bool) : literal (valuationOf b) 1765 = decide (1 ≤ count1765 b) := rfl
theorem meaning1769 (b : Nat → Bool) : literal (valuationOf b) 1769 = decide (1 ≤ count1769 b) := rfl
theorem meaning1771 (b : Nat → Bool) : literal (valuationOf b) 1771 = decide (1 ≤ count1771 b) := rfl
theorem meaning1774 (b : Nat → Bool) : literal (valuationOf b) 1774 = decide (2 ≤ count1773 b) := rfl
theorem meaning1777 (b : Nat → Bool) : literal (valuationOf b) 1777 = decide (1 ≤ count1777 b) := rfl
theorem meaning1778 (b : Nat → Bool) : literal (valuationOf b) 1778 = decide (2 ≤ count1777 b) := rfl
theorem meaning1786 (b : Nat → Bool) : literal (valuationOf b) 1786 = decide (2 ≤ count1785 b) := rfl
theorem meaning1787 (b : Nat → Bool) : literal (valuationOf b) 1787 = decide (1 ≤ count1787 b) := rfl
theorem meaning1789 (b : Nat → Bool) : literal (valuationOf b) 1789 = decide (1 ≤ count1789 b) := rfl
theorem meaning1791 (b : Nat → Bool) : literal (valuationOf b) 1791 = decide (3 ≤ count1789 b) := rfl
theorem meaning1793 (b : Nat → Bool) : literal (valuationOf b) 1793 = decide (1 ≤ count1793 b) := rfl
theorem meaning1795 (b : Nat → Bool) : literal (valuationOf b) 1795 = decide (1 ≤ count1795 b) := rfl
theorem meaning1797 (b : Nat → Bool) : literal (valuationOf b) 1797 = decide (1 ≤ count1797 b) := rfl
theorem meaning1798 (b : Nat → Bool) : literal (valuationOf b) 1798 = decide (2 ≤ count1797 b) := rfl
theorem meaning1802 (b : Nat → Bool) : literal (valuationOf b) 1802 = decide (2 ≤ count1801 b) := rfl
theorem meaning1805 (b : Nat → Bool) : literal (valuationOf b) 1805 = decide (5 ≤ count1801 b) := rfl
theorem meaning1812 (b : Nat → Bool) : literal (valuationOf b) 1812 = decide (4 ≤ count1809 b) := rfl
theorem meaning1814 (b : Nat → Bool) : literal (valuationOf b) 1814 = decide (6 ≤ count1809 b) := rfl
theorem meaning1837 (b : Nat → Bool) : literal (valuationOf b) 1837 = decide (13 ≤ count1825 b) := rfl
theorem meaning1838 (b : Nat → Bool) : literal (valuationOf b) 1838 = decide (14 ≤ count1825 b) := rfl
theorem meaning1870 (b : Nat → Bool) : literal (valuationOf b) 1870 = decide (23 ≤ count1848 b) := rfl
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
end Snake9.Regrowth.E112057
